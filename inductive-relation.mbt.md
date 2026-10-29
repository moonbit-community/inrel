# Inductive Relation for Free

## 前言

性质导向随机测试（Property-Based Random Testing）早已是函数式编程与形式化验证社区的常用技术，但一旦规格里出现「稀疏前置条件」，最直接的「生成-测试」路线就会迅速失效：大多数样本被丢弃，剩余样本分布又往往偏斜，既浪费计算，也掩盖缺陷。手写生成器当然可以缓解这一问题，却常常比规格本身更难维护，稍有改动就要整段重写；而自动化方案若仅停留在解释执行，也容易遭遇性能负担与正确性疑虑。基于这些现实约束，我们选择以 *Generating Good Generators for Inductive Relations*（Lampropoulos, Paraskevopoulou, Pierce, 2017）为主线，重新组织「从归纳关系到生成器」的论证与工程路径。

本文在术语、定义与算法骨架上尽量忠实论文，在叙述节奏与代码落点上则面向 MoonBit 实作做必要重排。换言之，我们关心的不只是论文如何定义输入语言、unification 状态与构造子分支编译，更关心这些定义如何稳定落到可运行的 DSL、可组合的生成器 AST，以及可复用的测试接口中。凡是与实现直接相关的地方，本文会优先给出可对照仓库代码的解释；凡是超出当前工程边界的内容（例如论文中的证明生成框架），则会明确标注其位置与取舍。

「for Free」 在这里并不意味着零成本，而是强调一种工程收益：一旦归纳关系写清楚，生成器便可随规格演化而系统地产生，不再依赖大量手工同步。我们希望把论文中的核心思想从 Coq/QuickChick 语境迁移到更通用的实现视角 MoonBit/QuickCheck，让读者既能看到理论上的约束条件，也能直接追踪到编译流水线中的每一步决策。若本文最终能让「规格即生成器」的直觉在实践中更可操作，则其目的可谓达成。

## 稀疏前置条件

本文关注的不是「如何把性质写成一句话」，而是「如何让测试在复杂前置条件下仍然有效」。在真实工程里，测试失败常常不是因为性质错误，而是因为样本质量不足。样本质量不足有两种典型表现：第一，候选输入大多在前置条件处被过滤；第二，未被过滤的输入分布过于偏斜，反复落在简单边界，从而掩盖深层缺陷。我们接下来将通过几个具体例子讨论为何 QuickCheck 风格的「生成-过滤」会在稀疏条件下浪费预算，并希望读者能体会到手动编写生成器的不便之处。

QuickCheck 在实践中通常包含三件事：生成器、反例打印与反例缩减。本文当前阶段只聚焦生成器，因为它直接决定了样本分布与测试吞吐。只要生成器质量不足，后续的缩减与展示再完善，也只能处理少量偶然命中的样本，无法系统扩大 bug 暴露面。换言之，生成器是性质测试的「入口控制面」。

### 有序列表

我们先从具体例子入手，尤其是那些简单的性质，但带有结构前置条件。
此处选用的性质是：有序列表在进行「有序插入」之后依旧有序，因此依赖一个能生成有序列表的生成器，
现在我们使用 `List[T]` 的默认生成器来生成样本，并过滤掉无序列表。

```mbt check
///|
type Sec1IntList = @list.List[Int32]

///|
fn insert_sorted(x : Int32, xs : Sec1IntList) -> Sec1IntList {
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
fn prop_insert_preserves_sorted(x : Int32, xs : Sec1IntList) -> Bool {
  !is_sorted(xs) || is_sorted(insert_sorted(x, xs))
}

///|
test "sec1: quickcheck classify/collect reports sparse-precondition profile" {
  let gen_xs : @qc_core.Generator[Sec1IntList] = @qc_core.spawn()
  let mut sorted = 0
  let prop = @qc.forall(gen_xs, xs => {
    if is_sorted(xs) {
      sorted += 1
    }
    prop_insert_preserves_sorted(0, xs)
    |> @qc.classify(is_sorted(xs), "sorted-input")
    |> @qc.classify(!is_sorted(xs), "unsorted-input")
  })
  let report = @qc.quick_check_silence(prop, max_success=200, max_size=200)
  assert_true(report.has_prefix("+++ [200/0/200] Ok, passed!"))
  assert_true(report.contains("% : sorted-input"))
  assert_true(sorted > 0 && sorted < 200)
}
```

这段写法的价值不只在「通过测试」，而在「让样本分布成为可见信息」。当 `unsorted-input` 占比持续偏高时，我们可以明确知道预算主要消耗在过滤环节，而不是性质检验环节。这样，是否需要迁移到关系驱动生成器，就不再是主观判断，而是可观测的工程信号。
具体比例会随随机生成器版本变化；样例报告中，无序列表通常占多数，许多生成结果都无法满足前置条件，因而自定义一个合适的有序列表生成器确有必要。在本例子中，实际上编写一个生成器相对简单，只需要在生成完成之后直接对列表进行排序即可，而标准库已经提供了 `List::sort` 函数。

### 二叉搜索树

若前一个例子仍可借由一次后处理来弥补默认生成器的不足，那么二叉搜索树就更能说明问题所在。我们现在不再要求一个线性结构满足单一序约束，而是要求一棵递归数据在每个节点都同时满足局部与全局条件：左子树中所有标签都要小于根标签，右子树中所有标签都要大于根标签，而且这一对界值会随着递归持续收缩。换言之，约束不是附着在最终结果表面的一层筛子，而是贯穿整个生成过程的结构信息。若仍旧先生成任意树，再在外层检查其是否满足搜索树条件，那么被丢弃的就不只是「局部不合格」的样本，而是几乎所有没有沿着正确边界递归下去的样本。

为了把这个约束说得更精确一些，我们不妨直接把搜索树写成一个带界值参数的谓词。`Leaf` 总是满足条件，因为它不包含任何元素；`Node(x, l, r)` 则只有在 `lo < x < hi`，并且左子树满足 `bst(lo, x, l)`、右子树满足 `bst(x, hi, r)` 时才是合法的搜索树。这一写法有一个很重要的工程含义：上下界 `lo` 与 `hi` 不是事后验证时才想起的额外信息，而是从根节点开始就应当参与生成决策的输入。若生成器不接受这两个参数，它就只能在黑暗中盲目生长，最后再被整体否决。

```mbt check
///|
fn is_bst(lo : Int32, hi : Int32, tree : BstTree) -> Bool {
  match tree {
    Leaf => true
    Node(x, left, right) =>
      lo < x && x < hi && is_bst(lo, x, left) && is_bst(x, hi, right)
  }
}

///|
enum BstTree {
  Leaf
  Node(Int32, BstTree, BstTree)
} derive(Eq, Debug, Show, @qc_core.Arbitrary)
```

在这一表述下，默认生成器的无效之处会变得比 `sorted + insert` 更明显。对于列表，我们至少还能想象「先生成后排序」这一类补救；但对于搜索树，根节点一旦落错区间，左右子树的可行空间就会立刻被破坏，而且这种破坏会在递归中层层放大。于是，`generate-and-test` 的症结不再只是「浪费了一些样本」，而是「生成器根本没有利用输入所提供的约束信息」。下面这段统计并不证明某个精确概率；它只是展示这样一个事实：在固定上下界之后，默认树生成器所命中的合法 BST 样本会很少，而大多数预算都用在了否定样本上。

```mbt check
///|
test "sec1: bst is sparse under generic tree generator" {
  let lo = -100
  let hi = 100
  let gen_tree : @qc_core.Generator[BstTree] = @qc_core.spawn()
  let mut valid_bst = 0
  let prop = @qc.forall(gen_tree, tree => {
    if is_bst(lo, hi, tree) {
      valid_bst += 1
    }
    true
    |> @qc.classify(is_bst(lo, hi, tree), "bst-input")
    |> @qc.classify(!is_bst(lo, hi, tree), "non-bst-input")
  })
  let report = @qc.quick_check_silence(prop, max_success=200, max_size=40)
  assert_true(report.has_prefix("+++ [200/0/200] Ok, passed!"))
  assert_true(report.contains("% : bst-input"))
  assert_true(valid_bst > 0 && valid_bst < 200)
}
```

一旦承认上下界本来就是生成问题的输入，手写生成器的自然形态也就变得清楚了。它不应当先生成一棵树，再去猜这棵树是否满足 `is_bst(lo, hi)`；更自然的做法，是让生成器从一开始就带着 `lo` 与 `hi` 工作。在大小预算为零时，它只能返回 `Leaf`；预算大于零时，它既可以选择返回 `Leaf`，也可以尝试构造一个 `Node`。若选择后者，就先生成一个满足 `lo < x < hi` 的标签 `x`，再递归生成左右子树，其中左子树的界值变为 `(lo, x)`，右子树的界值变为 `(x, hi)`。这种写法并不需要在最后统一修复什么，因为约束已经在每一步里被消费掉了。

```mbt check
///|
fn gen_bst_sized(
  size : Int32,
  lo : Int32,
  hi : Int32,
) -> @qc_core.Generator[BstTree] {
  if size <= 0 || hi - lo <= 1 {
    @qc_core.pure(Leaf)
  } else {
    @qc_core.frequency([
      (1, @qc_core.pure(Leaf)),
      (
        1,
        @qc_core.int_range(lo + 1, hi).flat_map(x => {
          gen_bst_sized(size - 1, lo, x).flat_map(left => {
            gen_bst_sized(size - 1, x, hi).map(right => Node(x, left, right))
          })
        }),
      ),
    ])
  }
}
```

运行生成器并进行分类，可以看到 100% 的情况都成功生成了正确的二叉搜索树。

```mbt check
///|
fn gen_bst(lo : Int32, hi : Int32) -> @qc_core.Generator[BstTree] {
  @qc_core.sized(size => gen_bst_sized(size, lo, hi))
}

///|
test "sec1: bst generator carries bounds during construction" {
  let lo = 0
  let hi = 20
  let prop = @qc.forall(gen_bst(lo, hi), tree => {
    is_bst(lo, hi, tree)
    |> @qc.classify(is_bst(lo, hi, tree), "bst-input")
    |> @qc.classify(!is_bst(lo, hi, tree), "non-bst-input")
  })
  let report = @qc.quick_check_silence(prop, max_success=200, max_size=40)
  inspect(
    report,
    content=(
      #|+++ [200/0/200] Ok, passed!
      #|Coverage:
      #|100% : bst-input
      #|0% : non-bst-input
    ),
  )
}
```

这个例子比前一个例子更接近本文后面真正要处理的问题。对于有序列表，我们尚且可以把生成器理解为「先生成，再做一个便宜的修正」；而对于 BST，界值参数与递归结构已经紧密地缠在一起。手写生成器当然仍然可行，但它已经开始显露出我们真正关心的那一面：一旦规格由「局部 predicate」变成「带输入参数的递归关系」，生成器本身就会逐渐长成规格的影子。再往前走一步，我们就不难得到本文的核心主张：既然生成器在结构上越来越接近关系定义，那么更合理的做法，往往不是继续手写，而是直接从归纳关系系统地派生它。
