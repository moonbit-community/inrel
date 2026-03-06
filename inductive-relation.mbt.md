# Inductive Relation for Free

## 前言

性质导向随机测试（Property-Based Random Testing）早已是函数式编程与形式化验证社区的常用技术，但一旦规格里出现「稀疏前置条件」，最直接的「生成-测试」路线就会迅速失效：大多数样本被丢弃，剩余样本分布又往往偏斜，既浪费计算，也掩盖缺陷。手写生成器当然可以缓解这一问题，却常常比规格本身更难维护，稍有改动就要整段重写；而自动化方案若仅停留在解释执行，也容易遭遇性能负担与正确性疑虑。基于这些现实约束，我们选择以 *Generating Good Generators for Inductive Relations*（Lampropoulos, Paraskevopoulou, Pierce, 2017）为主线，重新组织「从归纳关系到生成器」的论证与工程路径。

本文在术语、定义与算法骨架上尽量忠实论文，在叙述节奏与代码落点上则面向 MoonBit 实作做必要重排。换言之，我们关心的不只是论文如何定义输入语言、unification 状态与构造子分支编译，更关心这些定义如何稳定落到可运行的 DSL、可组合的生成器 AST，以及可复用的测试接口中。凡是与实现直接相关的地方，本文会优先给出可对照仓库代码的解释；凡是超出当前工程边界的内容（例如论文中的证明生成框架），则会明确标注其位置与取舍。

「for Free」 在这里并不意味着零成本，而是强调一种工程收益：一旦归纳关系写清楚，生成器便可随规格演化而系统地产生，不再依赖大量手工同步。我们希望把论文中的核心思想从 Coq/QuickChick 语境迁移到更通用的实现视角 MoonBit/QuickCheck，让读者既能看到理论上的约束条件，也能直接追踪到编译流水线中的每一步决策。若本文最终能让「规格即生成器」的直觉在实践中更可操作，则其目的可谓达成。

## 稀疏前置条件

本文关注的不是「如何把性质写成一句话」，而是「如何让测试在复杂前置条件下仍然有效」。在真实工程里，测试失败常常不是因为性质错误，而是因为样本质量不足。样本质量不足有两种典型表现：第一，候选输入大多在前置条件处被过滤；第二，未被过滤的输入分布过于偏斜，反复落在简单边界，从而掩盖深层缺陷。我们接下来将通过几个具体例子讨论为何 QuickCheck 风格的「生成-过滤」会在稀疏条件下浪费预算，并希望读者能体会到手动编写生成器的不便之处。

QuickCheck 在实践中通常包含三件事：生成器、反例打印与反例缩减。本文当前阶段只聚焦生成器，因为它直接决定了样本分布与测试吞吐。只要生成器质量不足，后续的缩减与展示再完善，也只能处理少量偶然命中的样本，无法系统扩大 bug 暴露面。换言之，生成器是性质测试的「入口控制面」。

### `sorted + insert`

我们先从具体例子入手，尤其是那些简单的性质，但带有结构前置条件。
此处选用的性质是：有序列表在进行「有序插入」之后依旧有序，因此依赖一个能生成有序列表的生成器，
现在我们使用 `List[T]` 的默认生成器来生成样本，并过滤掉无序列表。

```mbt check
///|
type Sec1IntList = @list.List[Int]

///|
fn insert_sorted(x : Int, xs : Sec1IntList) -> Sec1IntList {
  match xs {
    Empty => @list.cons(x, @list.empty())
    More(y, ..) if x <= y => @list.cons(x, xs)
    More(y, tail=ys) => @list.cons(y, insert_sorted(x, ys))
  }
}

///|
fn is_sorted(xs : Sec1IntList) -> Bool {
  xs.sort() == xs
}
```

我们希望分析它的统计情况，QuickCheck 恰好提供了这些接口：`classify` 用于标记测试类别，`collect` 用于汇总样本特征。统计逻辑与属性测试运行在同一条管线里，可以方便生成报告。

```mbt check
///|
fn prop_insert_preserves_sorted(x : Int, xs : Sec1IntList) -> Bool {
  !is_sorted(xs) || is_sorted(insert_sorted(x, xs))
}

///|
test "sec1: quickcheck classify/collect reports sparse-precondition profile" {
  let gen_xs : @qc.Gen[Sec1IntList] = @qc.Gen::spawn()
  let prop = @qc.forall(gen_xs, xs => {
    prop_insert_preserves_sorted(0, xs)
    |> @qc.classify(is_sorted(xs), "sorted-input")
    |> @qc.classify(!is_sorted(xs), "unsorted-input")
  })
  let report = @qc.quick_check_silence(prop, max_success=200, max_size=200)
  inspect(
    report,
    content=(
      #|+++ [200/0/200] Ok, passed!
      #|91% : unsorted-input
      #|9% : sorted-input
    ),
  )
}
```

这段写法的价值不只在「通过测试」，而在「让样本分布成为可见信息」。当 `unsorted-input` 占比持续偏高时，我们可以明确知道预算主要消耗在过滤环节，而不是性质检验环节。这样，是否需要迁移到关系驱动生成器，就不再是主观判断，而是可观测的工程信号。
从结果我们可以看出，不到 10% 的列表是有序的，将近 90% 的生成都被浪费了，因而自定义一个合适的有序列表生成器确有必要。在本例子中，实际上编写一个生成器相对简单，只需要在生成完成之后直接对列表进行排序即可，而标准库已经提供了 `List::sort` 函数。