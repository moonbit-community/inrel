///|
using @spec {
  forall0,
  forall1,
  forall3,
  forall4,
  binder,
  body,
  ctor,
  ty,
  in_param,
  out_param,
  inductive,
  pred,
  type RelationSpec,
  rel,
  v,
}

///|
fn complete_tree_spec() -> RelationSpec {
  inductive(
    "complete",
    [in_param("depth", ty("Nat")), out_param("tree", ty("Tree"))],
    [
      forall0("CompleteLeaf", () => body([ctor("O", []), ctor("Leaf", [])])),
      forall4(
        "CompleteNode",
        binder("n", ty("Nat")),
        binder("x", ty("Nat")),
        binder("l", ty("Tree")),
        binder("r", ty("Tree")),
        (n, x, l, r) => {
          body(
            [
              ctor("S", [n.term()]),
              ctor("Node", [x.term(), l.term(), r.term()]),
            ],
            hypotheses=[
              rel("complete", [n.term(), l.term()]),
              rel("complete", [n.term(), r.term()]),
            ],
          )
        },
      ),
    ],
  )
}

///|
fn nonempty_relation_spec() -> RelationSpec {
  inductive("nonempty", [out_param("tree", ty("Tree"))], [
    forall3(
      "NonEmpty",
      binder("x", ty("Nat")),
      binder("l", ty("Tree")),
      binder("r", ty("Tree")),
      (x, l, r) => body([ctor("Node", [x.term(), l.term(), r.term()])]),
    ),
  ])
}

///|
fn half_complete_relation_spec() -> RelationSpec {
  inductive(
    "half_complete",
    [in_param("depth", ty("Nat")), out_param("tree", ty("Tree"))],
    [forall0("CompleteLeaf'", () => body([ctor("O", []), ctor("Leaf", [])]))],
  )
}

///|
fn good_stack_relation_spec() -> RelationSpec {
  inductive(
    "good_stack",
    [in_param("n", ty("Nat")), out_param("stack", ty("Stack"))],
    [
      forall0("GoodStackMty", () => body([ctor("O", []), ctor("Mty", [])])),
      forall3(
        "GoodStackCons",
        binder("n1", ty("Nat")),
        binder("a", ty("Atom")),
        binder("s1", ty("Stack")),
        (n1, a, s1) => {
          body([ctor("S", [n1.term()]), ctor("Cons", [a.term(), s1.term()])], hypotheses=[
            pred("good_atom", [a.term()]),
            rel("good_stack", [n1.term(), s1.term()]),
          ])
        },
        weight=10,
      ),
      forall3(
        "GoodStackRet",
        binder("n2", ty("Nat")),
        binder("pc", ty("Atom")),
        binder("s2", ty("Stack")),
        (n2, pc, s2) => {
          body(
            [ctor("S", [n2.term()]), ctor("RetCons", [pc.term(), s2.term()])],
            hypotheses=[
              pred("good_atom", [pc.term()]),
              rel("good_stack", [n2.term(), s2.term()]),
            ],
          )
        },
        weight=4,
      ),
    ],
  )
}

///|
fn good_tree_relation_spec() -> RelationSpec {
  inductive(
    "goodTree",
    [
      in_param("n1", ty("Nat")),
      in_param("n2", ty("Nat")),
      out_param("tree", ty("Tree")),
    ],
    [
      forall1("GoodLeaf", binder("n", ty("Nat")), n => {
        body([n.term(), n.term(), ctor("Leaf", [])])
      }),
    ],
  )
}

///|
fn bst_relation_spec() -> RelationSpec {
  inductive(
    "bst",
    [
      in_param("lo", ty("Nat")),
      in_param("hi", ty("Nat")),
      out_param("tree", ty("Tree")),
    ],
    [
      forall0("BstLeaf", () => body([v("lo"), v("hi"), ctor("Leaf", [])])),
      forall3(
        "BstNode",
        binder("x", ty("Nat")),
        binder("l", ty("Tree")),
        binder("r", ty("Tree")),
        (x, l, r) => {
          body(
            [v("lo"), v("hi"), ctor("Node", [x.term(), l.term(), r.term()])],
            hypotheses=[
              pred("<", [v("lo"), x.term()]),
              pred("<", [x.term(), v("hi")]),
              rel("bst", [v("lo"), x.term(), l.term()]),
              rel("bst", [x.term(), v("hi"), r.term()]),
            ],
          )
        },
      ),
    ],
  )
}

///|
test "compile pipeline derives nonempty tree generator from single constructor" {
  let ast : BoundedGeneratorAst = try! compile_relation_to_bounded_generator(
    nonempty_relation_spec(),
  )
  debug_inspect(
    ast,
    content=(
      #|{
      #|  aux_name: "aux_arb",
      #|  size_var: "size",
      #|  inputs: [],
      #|  succ_size_var: "size'",
      #|  zero_case: Backtrack(
      #|    [
      #|      {
      #|        weight: 1,
      #|        body: Bind(
      #|          Do,
      #|          "x",
      #|          Arbitrary,
      #|          Bind(
      #|            Do,
      #|            "l",
      #|            Arbitrary,
      #|            Bind(
      #|              Do,
      #|              "r",
      #|              Arbitrary,
      #|              RetSome([Ctor("Node", [Var("x"), Var("l"), Var("r")])]),
      #|            ),
      #|          ),
      #|        ),
      #|      },
      #|    ],
      #|  ),
      #|  succ_case: Backtrack(
      #|    [
      #|      {
      #|        weight: 1,
      #|        body: Bind(
      #|          Do,
      #|          "x",
      #|          Arbitrary,
      #|          Bind(
      #|            Do,
      #|            "l",
      #|            Arbitrary,
      #|            Bind(
      #|              Do,
      #|              "r",
      #|              Arbitrary,
      #|              RetSome([Ctor("Node", [Var("x"), Var("l"), Var("r")])]),
      #|            ),
      #|          ),
      #|        ),
      #|      },
      #|    ],
      #|  ),
      #|}
    ),
  )
}

///|
test "compile pipeline derives complete generator with size split" {
  let ast = try! compile_relation_to_bounded_generator(complete_tree_spec())
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
