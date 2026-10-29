///|
fn assert_bst_bounds(tree : RuntimeValue, lo : Int32, hi : Int32) -> Unit raise {
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
  Node(Int32, Tree, Tree)
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
impl RuntimeDecode for Tree with fn from_runtime(value : RuntimeValue) {
  decode_tree(value)
}

///|
test "runtime eval: complete depth=0 returns leaf in zero branch" {
  let runtime = try! compile_relation_to_moonbit_generator(complete_tree_spec())
  guard runtime.run_one(0, [RuntimeInt(0)], @splitmix.new(seed=7))
    is Some(RuntimeCtor("Leaf", [])) else {
    fail("expected Leaf")
  }
}

///|
test "runtime eval: typed decode to moonbit Tree" {
  let runtime = try! compile_relation_to_moonbit_generator(complete_tree_spec())
  let out : Tree? = runtime.run_one1(4, 2, @splitmix.new(seed=29))
  guard out is Some(Node(_, _, _)) else { fail("expected typed Tree::Node") }
}

///|
test "runtime eval: complete depth>0 uses recursive node branch" {
  let runtime = try! compile_relation_to_moonbit_generator(complete_tree_spec())
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
  guard out is Some(tree) else { fail("expected a generated tree") }
  assert_true(bst_tree_assert(tree, 0, 8))
  let repeated : Tree? = runtime.run_one2(5, 0, 8, @splitmix.new(seed=42))
  assert_eq(out, repeated)
}

///|
fn complete_tree_assert(tree : Tree) -> Bool {
  complete_tree_depth(tree) is Some(_)
}

///|
fn complete_tree_depth(tree : Tree) -> Int32? {
  match tree {
    Leaf => Some(0)
    Node(_, left, right) => {
      guard complete_tree_depth(left) is Some(left_depth) else { None }
      guard complete_tree_depth(right) is Some(right_depth) else { None }
      if left_depth == right_depth {
        Some(left_depth + 1)
      } else {
        None
      }
    }
  }
}

///|
fn bst_tree_assert(tree : Tree, lo : Int32, hi : Int32) -> Bool {
  match tree {
    Leaf => true
    Node(x, left, right) =>
      lo < x &&
      x < hi &&
      bst_tree_assert(left, lo, x) &&
      bst_tree_assert(right, x, hi)
  }
}

///|
fn tree_denotation_env() -> DenotationEnv[Tree] {
  den_out_env_builder()
  .with_ctor(
    "Leaf",
    args => {
      match args {
        [] => Some(Leaf)
        _ => None
      }
    },
    tree => {
      match tree {
        Leaf => Some([])
        _ => None
      }
    },
  )
  .with_ctor(
    "Node",
    args => {
      match args {
        [DenInt(x), DenOut(left), DenOut(right)] => Some(Node(x, left, right))
        _ => None
      }
    },
    tree => {
      match tree {
        Node(x, left, right) => Some([DenInt(x), DenOut(left), DenOut(right)])
        _ => None
      }
    },
  )
  .with_arbitrary((_bind_name, ty, size, rs) => {
    match ty {
      Some(@spec.Named("Tree")) =>
        if size <= 0 || rs.next_positive_int() % 3 == 0 {
          Some(DenOut(Leaf))
        } else {
          let x : Int32 = @quickcheck.Arbitrary::arbitrary(size, rs)
          Some(DenOut(Node(x, Leaf, Leaf)))
        }
      _ => None
    }
  })
  .build()
}

///|
test "denotational eval: complete returns typed tree" {
  let gen = try! compile_relation_to_gen(
    complete_tree_spec(),
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
  let gen = compile_relation_to_gen(complete_tree_spec(), tree_denotation_env())
  guard gen.run1(10, 5, @splitmix.new(seed=7)) is Some(tree)
  assert_eq(complete_tree_depth(tree), Some(5))
  assert_eq(gen.run1(10, 5, @splitmix.new(seed=7)), Some(tree))
}
