///|
fn complete_relation_spec() -> @spec.RelationSpec {
  @spec.inductive(
    "complete",
    [
      @spec.in_param("depth", @spec.ty("Nat")),
      @spec.out_param("tree", @spec.ty("Tree")),
    ],
    [
      @spec.constructor_forall0("CompleteLeaf", () => {
        @spec.body([@spec.ctor("O", []), @spec.ctor("Leaf", [])])
      }),
      @spec.constructor_scoped(
        "CompleteNode",
        [
          @spec.binder("n", @spec.ty("Nat")),
          @spec.binder("x", @spec.ty("Nat")),
          @spec.binder("l", @spec.ty("Tree")),
          @spec.binder("r", @spec.ty("Tree")),
        ],
        scope => {
          let n = scope.v("n").term()
          let x = scope.v("x").term()
          let l = scope.v("l").term()
          let r = scope.v("r").term()
          @spec.body([@spec.ctor("S", [n]), @spec.ctor("Node", [x, l, r])], hypotheses=[
            @spec.rel("complete", [n, l]),
            @spec.rel("complete", [n, r]),
          ])
        },
      ),
    ],
  )
}

///|
fn nonempty_relation_spec() -> @spec.RelationSpec {
  @spec.inductive("nonempty", [@spec.out_param("tree", @spec.ty("Tree"))], [
    @spec.constructor_forall3(
      "NonEmpty",
      @spec.binder("x", @spec.ty("Nat")),
      @spec.binder("l", @spec.ty("Tree")),
      @spec.binder("r", @spec.ty("Tree")),
      (x, l, r) => {
        @spec.body([@spec.ctor("Node", [x.term(), l.term(), r.term()])])
      },
    ),
  ])
}

///|
fn half_complete_relation_spec() -> @spec.RelationSpec {
  @spec.inductive(
    "half_complete",
    [
      @spec.in_param("depth", @spec.ty("Nat")),
      @spec.out_param("tree", @spec.ty("Tree")),
    ],
    [
      @spec.constructor_forall0("CompleteLeaf'", () => {
        @spec.body([@spec.ctor("O", []), @spec.ctor("Leaf", [])])
      }),
    ],
  )
}

///|
fn good_stack_relation_spec() -> @spec.RelationSpec {
  @spec.inductive(
    "good_stack",
    [
      @spec.in_param("n", @spec.ty("Nat")),
      @spec.out_param("stack", @spec.ty("Stack")),
    ],
    [
      @spec.constructor_forall0("GoodStackMty", () => {
        @spec.body([@spec.ctor("O", []), @spec.ctor("Mty", [])])
      }),
      @spec.constructor_forall3(
        "GoodStackCons",
        @spec.binder("n1", @spec.ty("Nat")),
        @spec.binder("a", @spec.ty("Atom")),
        @spec.binder("s1", @spec.ty("Stack")),
        (n1, a, s1) => {
          @spec.body(
            [
              @spec.ctor("S", [n1.term()]),
              @spec.ctor("Cons", [a.term(), s1.term()]),
            ],
            hypotheses=[
              @spec.pred("good_atom", [a.term()]),
              @spec.rel("good_stack", [n1.term(), s1.term()]),
            ],
          )
        },
        weight=10,
      ),
      @spec.constructor_forall3(
        "GoodStackRet",
        @spec.binder("n2", @spec.ty("Nat")),
        @spec.binder("pc", @spec.ty("Atom")),
        @spec.binder("s2", @spec.ty("Stack")),
        (n2, pc, s2) => {
          @spec.body(
            [
              @spec.ctor("S", [n2.term()]),
              @spec.ctor("RetCons", [pc.term(), s2.term()]),
            ],
            hypotheses=[
              @spec.pred("good_atom", [pc.term()]),
              @spec.rel("good_stack", [n2.term(), s2.term()]),
            ],
          )
        },
        weight=4,
      ),
    ],
  )
}

///|
fn good_tree_relation_spec() -> @spec.RelationSpec {
  @spec.inductive(
    "goodTree",
    [
      @spec.in_param("n1", @spec.ty("Nat")),
      @spec.in_param("n2", @spec.ty("Nat")),
      @spec.out_param("tree", @spec.ty("Tree")),
    ],
    [
      @spec.constructor_forall1(
        "GoodLeaf",
        @spec.binder("n", @spec.ty("Nat")),
        n => @spec.body([n.term(), n.term(), @spec.ctor("Leaf", [])]),
      ),
    ],
  )
}

///|
fn bst_relation_spec() -> @spec.RelationSpec {
  @spec.inductive(
    "bst",
    [
      @spec.in_param("lo", @spec.ty("Nat")),
      @spec.in_param("hi", @spec.ty("Nat")),
      @spec.out_param("tree", @spec.ty("Tree")),
    ],
    [
      @spec.constructor_forall0("BstLeaf", () => {
        @spec.body([@spec.v("lo"), @spec.v("hi"), @spec.ctor("Leaf", [])])
      }),
      @spec.constructor_forall3(
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
              @spec.pred("<", [@spec.v("lo"), x.term()]),
              @spec.pred("<", [x.term(), @spec.v("hi")]),
              @spec.rel("bst", [@spec.v("lo"), x.term(), l.term()]),
              @spec.rel("bst", [x.term(), @spec.v("hi"), r.term()]),
            ],
          )
        },
      ),
    ],
  )
}

///|
test "compile pipeline derives nonempty tree generator from single constructor" {
  let ast = try! compile_relation_to_bounded_generator(nonempty_relation_spec())
  inspect(
    ast.to_string(),
    content=(
      #|Fixpoint aux_arb size :=
      #|  match size with
      #|  | O =>
      #|    backtrack [
      #|      (1,
      #|        do! x <- arbitrary;
      #|        do! l <- arbitrary;
      #|        do! r <- arbitrary;
      #|        ret (Some (Node x l r))
      #|      )
      #|    ]
      #|  | S size' =>
      #|    backtrack [
      #|      (1,
      #|        do! x <- arbitrary;
      #|        do! l <- arbitrary;
      #|        do! r <- arbitrary;
      #|        ret (Some (Node x l r))
      #|      )
      #|    ]
      #|  end.
    ),
  )
}

///|
test "compile pipeline derives complete generator with size split" {
  let ast = try! compile_relation_to_bounded_generator(complete_relation_spec())
  inspect(
    ast.to_string(),
    content=(
      #|Fixpoint aux_arb size depth :=
      #|  match size with
      #|  | O =>
      #|    backtrack [
      #|      (1,
      #|        match depth with
      #|        | O =>
      #|          ret (Some Leaf)
      #|        | _ =>
      #|          ret None
      #|      )
      #|    ]
      #|  | S size' =>
      #|    backtrack [
      #|      (1,
      #|        match depth with
      #|        | O =>
      #|          ret (Some Leaf)
      #|        | _ =>
      #|          ret None
      #|      )
      #|      ; (1,
      #|        match depth with
      #|        | S n =>
      #|          doM! l <- aux_arb n;
      #|          doM! r <- aux_arb n;
      #|          do! x <- arbitrary;
      #|          ret (Some (Node x l r))
      #|        | _ =>
      #|          ret None
      #|      )
      #|    ]
      #|  end.
    ),
  )
}

///|
test "compile pipeline derives half_complete option failure branch" {
  let ast = try! compile_relation_to_bounded_generator(
    half_complete_relation_spec(),
  )
  inspect(
    ast.to_string(),
    content=(
      #|Fixpoint aux_arb size depth :=
      #|  match size with
      #|  | O =>
      #|    backtrack [
      #|      (1,
      #|        match depth with
      #|        | O =>
      #|          ret (Some Leaf)
      #|        | _ =>
      #|          ret None
      #|      )
      #|    ]
      #|  | S size' =>
      #|    backtrack [
      #|      (1,
      #|        match depth with
      #|        | O =>
      #|          ret (Some Leaf)
      #|        | _ =>
      #|          ret None
      #|      )
      #|    ]
      #|  end.
    ),
  )
}

///|
test "compile pipeline emits equality checks from unify state" {
  let ast = try! compile_relation_to_bounded_generator(
    good_tree_relation_spec(),
  )
  inspect(
    ast.to_string(),
    content=(
      #|Fixpoint aux_arb size n1 n2 :=
      #|  match size with
      #|  | O =>
      #|    backtrack [
      #|      (1,
      #|        if (n1 = n2)? then
      #|          ret (Some Leaf)
      #|        else
      #|          ret None
      #|      )
      #|    ]
      #|  | S size' =>
      #|    backtrack [
      #|      (1,
      #|        if (n1 = n2)? then
      #|          ret (Some Leaf)
      #|        else
      #|          ret None
      #|      )
      #|    ]
      #|  end.
    ),
  )
}

///|
test "compile pipeline integrates hypothesis handling into constructor body" {
  let ast = try! compile_relation_to_bounded_generator(bst_relation_spec())
  inspect(
    ast.to_string(),
    content=(
      #|Fixpoint aux_arb size lo hi :=
      #|  match size with
      #|  | O =>
      #|    backtrack [
      #|      (1,
      #|        ret (Some Leaf)
      #|      )
      #|    ]
      #|  | S size' =>
      #|    backtrack [
      #|      (1,
      #|        ret (Some Leaf)
      #|      )
      #|      ; (1,
      #|        doM! x <- arbitraryST (fun x => lo < x);
      #|        if (x < hi)? then
      #|          doM! l <- aux_arb lo x;
      #|          doM! r <- aux_arb x hi;
      #|          ret (Some (Node x l r))
      #|        else
      #|          ret None
      #|      )
      #|    ]
      #|  end.
    ),
  )
}

///|
test "compile pipeline derives weighted good_stack generator from paper case study" {
  let ast = try! compile_relation_to_bounded_generator(
    good_stack_relation_spec(),
  )
  inspect(
    ast.to_string(),
    content=(
      #|Fixpoint aux_arb size n :=
      #|  match size with
      #|  | O =>
      #|    backtrack [
      #|      (1,
      #|        match n with
      #|        | O =>
      #|          ret (Some Mty)
      #|        | _ =>
      #|          ret None
      #|      )
      #|    ]
      #|  | S size' =>
      #|    backtrack [
      #|      (1,
      #|        match n with
      #|        | O =>
      #|          ret (Some Mty)
      #|        | _ =>
      #|          ret None
      #|      )
      #|      ; (10,
      #|        match n with
      #|        | S n1 =>
      #|          doM! a <- arbitraryST (fun a => good_atom a);
      #|          doM! s1 <- aux_arb n1;
      #|          ret (Some (Cons a s1))
      #|        | _ =>
      #|          ret None
      #|      )
      #|      ; (4,
      #|        match n with
      #|        | S n2 =>
      #|          doM! pc <- arbitraryST (fun pc => good_atom pc);
      #|          doM! s2 <- aux_arb n2;
      #|          ret (Some (RetCons pc s2))
      #|        | _ =>
      #|          ret None
      #|      )
      #|    ]
      #|  end.
    ),
  )
}
