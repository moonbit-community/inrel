///|
fn assert_bst_bounds(tree : RuntimeValue, lo : Int, hi : Int) -> Unit raise {
  match tree {
    RuntimeCtor("Leaf", []) => ()
    RuntimeCtor("Node", [RuntimeInt(x), left, right]) => {
      assert_true(lo < x)
      assert_true(x < hi)
      assert_bst_bounds(left, lo, x)
      assert_bst_bounds(right, x, hi)
    }
    _ => fail("unexpected runtime tree shape: \{tree}")
  }
}

///|
enum Tree {
  Leaf
  Node(Int, Tree, Tree)
} derive(Eq, Show, Debug)

///|
fn decode_tree(value : RuntimeValue) -> Tree? {
  match value {
    RuntimeCtor("Leaf", []) => Some(Leaf)
    RuntimeCtor("Node", [RuntimeInt(xv), left, right]) => {
      guard decode_tree(left) is Some(lt) else { None }
      guard decode_tree(right) is Some(rt) else { None }
      Some(Node(xv, lt, rt))
    }
    _ => None
  }
}

///|
impl RuntimeDecode for Tree with from_runtime(value : RuntimeValue) {
  decode_tree(value)
}

///|
test "runtime eval: complete depth=0 returns leaf in zero branch" {
  let runtime = try! compile_relation_to_moonbit_generator(
    complete_relation_spec(),
  )
  guard runtime.run_one(0, [RuntimeInt(0)], @splitmix.new(seed=7))
    is Some(RuntimeCtor("Leaf", [])) else {
    fail("expected Leaf")
  }
}

///|
test "runtime eval: typed decode to moonbit Tree" {
  let runtime = try! compile_relation_to_moonbit_generator(
    complete_relation_spec(),
  )
  let out : Tree? = runtime.run_one1(4, 2, @splitmix.new(seed=29))
  guard out is Some(Node(_, _, _)) else { fail("expected typed Tree::Node") }
}

///|
test "runtime eval: complete depth>0 uses recursive node branch" {
  let runtime = try! compile_relation_to_moonbit_generator(
    complete_relation_spec(),
  )
  guard runtime.run_one(4, [RuntimeInt(2)], @splitmix.new(seed=11))
    is Some(RuntimeCtor("Node", [_x, _l, _r])) else {
    fail("expected Node for depth=2 in successor branch")
  }
}

///|
test "runtime eval: nonempty generates node directly" {
  let runtime = try! compile_relation_to_moonbit_generator(
    nonempty_relation_spec(),
  )
  guard runtime.run_one(3, [], @splitmix.new(seed=17))
    is Some(RuntimeCtor("Node", [_x, _l, _r])) else {
    fail("expected Node from nonempty relation")
  }
}

///|
test "runtime eval: bst generation respects bounds on all sampled trees" {
  let runtime = try! compile_relation_to_moonbit_generator(bst_relation_spec())
  for seed in 1..<=25 {
    guard runtime.run_one(
        5,
        [RuntimeInt(0), RuntimeInt(8)],
        @splitmix.new(seed=seed.to_uint64()),
      )
      is Some(tree) else {
      fail("bst generator returned None at seed \{seed}")
    }
    assert_bst_bounds(tree, 0, 8)
  }
}

///|
test "runtime eval: run_one2 supports typed output decoding" {
  let runtime = try! compile_relation_to_moonbit_generator(bst_relation_spec())
  let out : Tree? = runtime.run_one2(5, 0, 8, @splitmix.new(seed=42))
  inspect(
    out,
    content=(
      #|Some(Node(1, Leaf, Leaf))
    ),
  )
}

///|
fn complete_tree_assert(tree: Tree) -> Bool {
  match tree {
    Leaf => true
    Node(_, Leaf, Leaf) => true
    Node(_, left, right) => {
      complete_tree_assert(left) && complete_tree_assert(right)
    }
  }
}

fn bst_tree_assert(tree: Tree, lo: Int, hi: Int) -> Bool {
  match tree {
    Leaf => true
    Node(x, left, right) =>
      lo < x && x < hi && bst_tree_assert(left, lo, x) && bst_tree_assert(right, x, hi)
  }
}

///|
fn tree_denotation_env() -> DenotationEnv[Tree] {
  {
    use_ctor: (name, args) => {
      match (name, args) {
        ("Leaf", []) => Some(DenOut(Leaf))
        ("Node", [DenInt(x), DenOut(left), DenOut(right)]) =>
          Some(DenOut(Node(x, left, right)))
        _ => None
      }
    },
    split_ctor: (value, name) => {
      match (value, name) {
        (DenOut(Leaf), "Leaf") => Some([])
        (DenOut(Node(x, left, right)), "Node") =>
          Some([DenInt(x), DenOut(left), DenOut(right)])
        _ => None
      }
    },
    call: (_name, _args) => None,
    arbitrary: (_bind_name, ty, size, rs) => {
      match ty {
        Some(@spec.Named("Tree")) =>
          if size <= 0 || rs.next_positive_int() % 3 == 0 {
            Some(DenOut(Leaf))
          } else {
            let x : Int = @quickcheck.Arbitrary::arbitrary(size, rs)
            Some(DenOut(Node(x, Leaf, Leaf)))
          }
        _ => None
      }
    },
    eq: (lhs, rhs) => den_eq_with((l, r) => l == r, lhs, rhs),
    to_output: value => {
      match value {
        DenOut(tree) => Some(tree)
        _ => None
      }
    },
  }
}

///|
test "denotational eval: complete returns typed tree" {
  let gen = try! compile_relation_to_gen(
    complete_relation_spec(),
    tree_denotation_env(),
  )
  let out = gen.run1(4, 2, @splitmix.new(seed=29))
  guard out is Some(Node(_, _, _)) else { fail("expected Node output") }
}

///|
test "denotational eval: bst keeps bounds with typed output" {
  let gen = try! compile_relation_to_gen(
    bst_relation_spec(),
    tree_denotation_env(),
  )
  for seed in 1..<=25 {
    guard gen.run2(4, 0, 8, @splitmix.new(seed=seed.to_uint64())) is Some(tree) else {
      fail("bst denotational generator returned None at seed \{seed}")
    }
    assert_true(bst_tree_assert(tree, 0, 8))
    println(tree)
  }
}

///|
test "denotational eval: runtime bridge env returns runtime tree" {
  let gen = try! compile_relation_to_gen(
    complete_relation_spec(),
    tree_denotation_env(),
  )
  guard gen.run1(10, 5, @splitmix.new(seed=7)) is Some(tree)
  assert_true(complete_tree_assert(tree))
  debug_inspect(
    tree,
    content=(
      #|Node(
      #|  0,
      #|  Node(
      #|    3,
      #|    Node(
      #|      -6,
      #|      Node(-2, Node(-5, Leaf, Leaf), Node(-1, Leaf, Leaf)),
      #|      Node(1, Node(-5, Leaf, Leaf), Node(-1, Leaf, Leaf)),
      #|    ),
      #|    Node(
      #|      2,
      #|      Node(-6, Node(4, Leaf, Leaf), Node(-2, Leaf, Leaf)),
      #|      Node(0, Node(4, Leaf, Leaf), Node(1, Leaf, Leaf)),
      #|    ),
      #|  ),
      #|  Node(
      #|    -3,
      #|    Node(
      #|      2,
      #|      Node(4, Node(-4, Leaf, Leaf), Node(-1, Leaf, Leaf)),
      #|      Node(-1, Node(3, Leaf, Leaf), Node(0, Leaf, Leaf)),
      #|    ),
      #|    Node(
      #|      0,
      #|      Node(5, Node(1, Leaf, Leaf), Node(2, Leaf, Leaf)),
      #|      Node(0, Node(-3, Leaf, Leaf), Node(1, Leaf, Leaf)),
      #|    ),
      #|  ),
      #|)
    ),
  )
}
