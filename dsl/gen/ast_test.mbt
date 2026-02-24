///|
test "paper-like bounded generator rendering: complete-style" {
  let leaf_case = @gen.weighted(1, @gen.ret_some([Ctor("Leaf", [])]))
  let node_body = @gen.match_pattern(
    "in1",
    @gen.pctor("S", [@gen.pvar("n")]),
    @gen.bind_dom(
      "l",
      @gen.source_recursive("aux_arb", ["n"]),
      @gen.bind_dom(
        "r",
        @gen.source_recursive("aux_arb", ["n"]),
        @gen.bind_do(
          "x",
          @gen.source_arbitrary(),
          @gen.ret_some([Ctor("Node", [Var("x"), Var("l"), Var("r")])]),
        ),
      ),
    ),
    @gen.ret_none(),
  )
  let ast = @gen.bounded_generator(
    "aux_arb",
    "size",
    ["in1"],
    "size'",
    @gen.backtrack([leaf_case]),
    @gen.backtrack([leaf_case, @gen.weighted(1, node_body)]),
  )
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
  let g = @gen.match_pattern(
    "in1",
    @gen.pctor("S", [@gen.pvar("n")]),
    @gen.if_guard(
      @gen.guard_eq(Var("in1"), Var("in2")),
      @gen.bind_do(
        "x",
        @gen.source_arbitrary_st("x", Call("<", [Var("lo"), Var("x")])),
        @gen.if_guard(
          @gen.guard_decidable(Call("<", [Var("x"), Var("hi")])),
          @gen.ret_some([Ctor("Node", [Var("x"), Var("l"), Var("r")])]),
          @gen.ret_none(),
        ),
      ),
      @gen.ret_none(),
    ),
    @gen.ret_none(),
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
