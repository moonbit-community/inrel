///|
test "relation mode partition follows in/out split" {
  let rel = @spec.make_relation(
    "complete",
    [
      @spec.make_param("depth", @spec.type_named("Nat"), @spec.mode_in()),
      @spec.make_param("tree", @spec.type_named("Tree"), @spec.mode_out()),
    ],
    [],
  )
  inspect(rel.arity(), content="2")
  inspect(rel.input_positions(), content="[0]")
  inspect(rel.output_positions(), content="[1]")
}

///|
test "constructor helper defaults weight to one" {
  let c = @spec.make_constructor("CompleteLeaf", [], [], [
    @spec.term_ctor("O", []),
    @spec.term_ctor("Leaf", []),
  ])
  inspect(c.weight, content="1")
}

///|
test "relation show renders empty inductive body" {
  let rel = @spec.make_relation(
    "empty_rel",
    [
      @spec.make_param(
        "xs",
        @spec.type_app("List", [@spec.type_named("Nat")]),
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
    [@spec.make_param("tree", @spec.type_named("Tree"), @spec.mode_out())],
    [
      @spec.make_constructor(
        "NonEmpty",
        [
          @spec.make_binder("x", @spec.type_named("Nat")),
          @spec.make_binder("l", @spec.type_named("Tree")),
          @spec.make_binder("r", @spec.type_named("Tree")),
        ],
        [],
        [
          @spec.term_ctor("Node", [
            @spec.term_var("x"),
            @spec.term_var("l"),
            @spec.term_var("r"),
          ]),
        ],
      ),
    ],
  )
  inspect(
    rel.to_string(),
    content=(
      #|Inductive nonempty : Tree -> Prop :=
      #| | NonEmpty : forall x l r, nonempty (Node x l r).
    ),
  )
}

///|
test "relation show renders hypotheses chain" {
  let rel = @spec.make_relation(
    "bst",
    [
      @spec.make_param("lo", @spec.type_named("Nat"), @spec.mode_in()),
      @spec.make_param("hi", @spec.type_named("Nat"), @spec.mode_in()),
      @spec.make_param("tree", @spec.type_named("Tree"), @spec.mode_out()),
    ],
    [
      @spec.make_constructor("BstLeaf", [], [], [
        @spec.term_var("lo"),
        @spec.term_var("hi"),
        @spec.term_ctor("Leaf", []),
      ]),
      @spec.make_constructor(
        "BstNode",
        [
          @spec.make_binder("x", @spec.type_named("Nat")),
          @spec.make_binder("l", @spec.type_named("Tree")),
          @spec.make_binder("r", @spec.type_named("Tree")),
        ],
        [
          @spec.hypothesis_predicate("lt", [
            @spec.term_var("lo"),
            @spec.term_var("x"),
          ]),
          @spec.hypothesis_predicate("lt", [
            @spec.term_var("x"),
            @spec.term_var("hi"),
          ]),
          @spec.hypothesis_rel_call("bst", [
            @spec.term_var("lo"),
            @spec.term_var("x"),
            @spec.term_var("l"),
          ]),
          @spec.hypothesis_rel_call("bst", [
            @spec.term_var("x"),
            @spec.term_var("hi"),
            @spec.term_var("r"),
          ]),
        ],
        [
          @spec.term_var("lo"),
          @spec.term_var("hi"),
          @spec.term_ctor("Node", [
            @spec.term_var("x"),
            @spec.term_var("l"),
            @spec.term_var("r"),
          ]),
        ],
      ),
    ],
  )
  inspect(
    rel,
    content=(
      #|Inductive bst : Nat -> Nat -> Tree -> Prop :=
      #| | BstLeaf : bst lo hi Leaf
      #| | BstNode : forall x l r, lt lo x -> lt x hi -> bst lo x l -> bst x hi r -> bst lo hi (Node x l r).
    ),
  )
}
