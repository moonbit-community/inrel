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
