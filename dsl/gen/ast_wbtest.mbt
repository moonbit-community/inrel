///|
test "paper-like bounded generator rendering: complete-style" {
  let leaf_case : WeightedCaseAst = {
    weight: 1,
    body: RetSome([Ctor("Leaf", [])]),
  }

  let node_body : GenNode = MatchPattern(
    "in1",
    PCtor("S", [PVar("n")]),
    Bind(
      DoM,
      "l",
      RecursiveCall("aux_arb", ["n"]),
      Bind(
        DoM,
        "r",
        RecursiveCall("aux_arb", ["n"]),
        Bind(
          Do,
          "x",
          Arbitrary,
          RetSome([Ctor("Node", [Var("x"), Var("l"), Var("r")])]),
        ),
      ),
    ),
    RetNone,
  )

  let ast : BoundedGeneratorAst = {
    aux_name: "aux_arb",
    size_var: "size",
    inputs: ["in1"],
    succ_size_var: "size'",
    zero_case: Backtrack([leaf_case]),
    succ_case: Backtrack([leaf_case, { weight: 1, body: node_body }]),
  }

  inspect(
    ast,
    content=(
      #|Fixpoint aux_arb size in1 :=
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
      #|        match in1 with
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
test "paper-like sub-generator rendering: pattern/equality/check chain" {
  let g : GenNode = MatchPattern(
    "in1",
    PCtor("S", [PVar("n")]),
    IfGuard(
      Eq(Var("in1"), Var("in2")),
      Bind(
        Do,
        "x",
        ArbitraryST("x", Call("<", [Var("lo"), Var("x")])),
        IfGuard(
          Decidable(Call("<", [Var("x"), Var("hi")])),
          RetSome([Ctor("Node", [Var("x"), Var("l"), Var("r")])]),
          RetNone,
        ),
      ),
      RetNone,
    ),
    RetNone,
  )

  inspect(
    g.to_string(),
    content=(
      #|match in1 with
      #|| S n =>
      #|  if (in1 = in2)? then
      #|    do! x <- arbitraryST (fun x => lo < x);
      #|    if (x < hi)? then
      #|      ret (Some (Node x l r))
      #|    else
      #|      ret None
      #|  else
      #|    ret None
      #|| _ =>
      #|  ret None
    ),
  )
}
