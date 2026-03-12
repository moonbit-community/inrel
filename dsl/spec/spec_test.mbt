///|
test "relation mode partition follows in/out split" {
  let rel = @spec.make_relation(
    "complete",
    [
      @spec.make_param("depth", @spec.ty("Nat"), @spec.mode_in()),
      @spec.make_param("tree", @spec.ty("Tree"), @spec.mode_out()),
    ],
    [],
  )
  inspect(rel.arity(), content="2")
  inspect(rel.input_positions(), content="[0]")
  inspect(rel.output_positions(), content="[1]")
}

///|
test "constructor helper defaults weight to one" {
  let c = @spec.forall0("CompleteLeaf", () => {
    @spec.body([@spec.ctor("O", []), @spec.ctor("Leaf", [])])
  })
  inspect(c.weight, content="1")
}

///|
test "relation show renders empty inductive body" {
  let rel = @spec.make_relation(
    "empty_rel",
    [
      @spec.make_param(
        "xs",
        @spec.type_app("List", [@spec.ty("Nat")]),
        @spec.mode_in(),
      ),
    ],
    [],
  )
  inspect(
    rel.to_string(),
    content="Inductive empty_rel : List Nat -> Prop :=\n.",
  )
}

///|
test "relation show renders constructor and binders" {
  let rel = @spec.make_relation(
    "nonempty",
    [@spec.make_param("tree", @spec.ty("Tree"), @spec.mode_out())],
    [
      @spec.forall3(
        "NonEmpty",
        @spec.binder("x", @spec.ty("Nat")),
        @spec.binder("l", @spec.ty("Tree")),
        @spec.binder("r", @spec.ty("Tree")),
        (x, l, r) => {
          @spec.body([@spec.ctor("Node", [x.term(), l.term(), r.term()])])
        },
      ),
    ],
  )
  inspect(
    rel.to_string(),
    content=(
      #|Inductive nonempty : Tree -> Prop :=
      #|| NonEmpty : forall x l r, nonempty (Node x l r).
    ),
  )
}

///|
test "relation show renders hypotheses chain" {
  let rel = @spec.make_relation(
    "bst",
    [
      @spec.make_param("lo", @spec.ty("Nat"), @spec.mode_in()),
      @spec.make_param("hi", @spec.ty("Nat"), @spec.mode_in()),
      @spec.make_param("tree", @spec.ty("Tree"), @spec.mode_out()),
    ],
    [
      @spec.forall0("BstLeaf", () => {
        @spec.body([@spec.v("lo"), @spec.v("hi"), @spec.ctor("Leaf", [])])
      }),
      @spec.forall3(
        "BstNode",
        @spec.binder("x", @spec.ty("Nat")),
        @spec.binder("l", @spec.ty("Tree")),
        @spec.binder("r", @spec.ty("Tree")),
        (x, l, r) => {
          @spec.body(
            [
              @spec.v("lo"),
              @spec.v("hi"),
              @spec.ctor("Node", [x.term(), l.term(), r.term()]),
            ],
            hypotheses=[
              @spec.pred("lt", [@spec.v("lo"), x.term()]),
              @spec.pred("lt", [x.term(), @spec.v("hi")]),
              @spec.rel("bst", [@spec.v("lo"), x.term(), l.term()]),
              @spec.rel("bst", [x.term(), @spec.v("hi"), r.term()]),
            ],
          )
        },
      ),
    ],
  )
  inspect(
    rel,
    content=(
      #|Inductive bst : Nat -> Nat -> Tree -> Prop :=
      #|| BstLeaf : bst lo hi Leaf
      #|| BstNode : forall x l r, lt lo x -> lt x hi -> bst lo x l -> bst x hi r -> bst lo hi (Node x l r).
    ),
  )
}

///|
test "builder forall helper lowers to relation spec" {
  let rel = @spec.inductive(
    "nonempty",
    [@spec.out_param("tree", @spec.ty("Tree"))],
    [
      @spec.forall3(
        "NonEmpty",
        @spec.binder("x", @spec.ty("Nat")),
        @spec.binder("l", @spec.ty("Tree")),
        @spec.binder("r", @spec.ty("Tree")),
        (x, l, r) => {
          @spec.body([@spec.ctor("Node", [x.term(), l.term(), r.term()])])
        },
      ),
    ],
  )
  inspect(
    rel.to_string(),
    content=(
      #|Inductive nonempty : Tree -> Prop :=
      #|| NonEmpty : forall x l r, nonempty (Node x l r).
    ),
  )
}

///|
test "builder forall1 supports repeated variable usage" {
  let rel = @spec.inductive(
    "goodTree",
    [
      @spec.in_param("n1", @spec.ty("Nat")),
      @spec.in_param("n2", @spec.ty("Nat")),
      @spec.out_param("tree", @spec.ty("Tree")),
    ],
    [
      @spec.forall1("GoodLeaf", @spec.binder("n", @spec.ty("Nat")), n => {
        @spec.body([n.term(), n.term(), @spec.ctor("Leaf", [])])
      }),
    ],
  )
  inspect(
    rel.to_string(),
    content=(
      #|Inductive goodTree : Nat -> Nat -> Tree -> Prop :=
      #|| GoodLeaf : forall n, goodTree n n Leaf.
    ),
  )
}
