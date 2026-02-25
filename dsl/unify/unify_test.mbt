///|
test "unify state actions mirror figure 2 primitives" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_undef(@spec.ty("Tree"))
  let st = @unify.UnifyState::new(constraints, [0, 1])

  try! st.update_constraint(1, @unify.range_link(0))
  try! st.record_equality(0, 1)
  try! st.record_equality(1, 0)
  try! st.record_pattern(0, @unify.pattern_ctor("S", [@unify.pattern_var(2)]))

  let fresh = st.fresh_unknown(ty=@spec.ty("Tree"))

  inspect(st.lookup(1), content="Some(Link(0))")
  inspect(st.equality_count(), content="1")
  inspect(st.pattern_count(), content="1")
  inspect(st.unknown_count(), content="3")
  inspect(fresh, content="2")
  inspect(st.next_unknown_id(), content="3")
}

///|
test "figure3 unify handles unknown/unknown and unknown/ctor" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_undef(@spec.ty("Tree"))
  constraints[1] = @unify.range_ctor("Leaf", [])
  constraints[2] = @unify.range_undef(@spec.ty("Tree"))
  let st = @unify.UnifyState::new(constraints, [0, 1, 2])

  try! st.unify(@unify.range_link(0), @unify.range_link(1))
  try! st.unify(
    @unify.range_link(2),
    @unify.range_ctor("Node", [@unify.range_ctor("Leaf", [])]),
  )

  inspect(st.lookup(0), content="Some(Link(1))")
  inspect(st.lookup(2), content="Some(Ctor(\"Node\", [Ctor(\"Leaf\", [])]))")
}

///|
test "figure3 unify_r covers fixed/fixed and fixed/ctor branches" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_fixed()
  constraints[2] = @unify.range_fixed()
  constraints[3] = @unify.range_ctor("S", [@unify.range_link(4)])
  constraints[4] = @unify.range_undef(@spec.ty("Nat"))
  let st = @unify.UnifyState::new(constraints, [0, 1, 2, 3, 4])

  try! st.unify_r(0, @unify.range_fixed(), 1, @unify.range_fixed())
  try! st.unify_r(
    2,
    @unify.range_fixed(),
    3,
    @unify.range_ctor("S", [@unify.range_link(4)]),
  )

  inspect(st.equality_count(), content="1")
  inspect(st.pattern_count(), content="1")
  inspect(st.lookup(0), content="Some(Link(1))")
  inspect(st.lookup(4), content="Some(Fixed)")
}

///|
test "figure3 unify_c succeeds on aligned ctors and fails on mismatch" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_undef(@spec.ty("Tree"))
  constraints[1] = @unify.range_undef(@spec.ty("Tree"))
  let st = @unify.UnifyState::new(constraints, [0, 1])

  try! st.unify_c(
    "Pair",
    [@unify.range_link(0), @unify.range_link(1)],
    "Pair",
    [@unify.range_ctor("Leaf", []), @unify.range_ctor("Leaf", [])],
  )
  let bad : Result[Unit, @unify.UnificationError] = try? st.unify_c(
    "Pair",
    [@unify.range_link(0)],
    "Other",
    [@unify.range_link(1)],
  )

  guard bad is Err(_) else { fail("Expected unification failure") }
  inspect(st.lookup(0), content="Some(Ctor(\"Leaf\", []))")
  inspect(st.lookup(1), content="Some(Ctor(\"Leaf\", []))")
}

///|
test "figure3 unify_rc follows links and detects ctor clashes" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_link(1)
  constraints[1] = @unify.range_undef(@spec.ty("Tree"))
  constraints[2] = @unify.range_ctor("Leaf", [])
  let st = @unify.UnifyState::new(constraints, [0, 1, 2])

  try! st.unify_rc(0, @unify.range_link(1), "Node", [
    @unify.range_ctor("Leaf", []),
  ])
  let bad : Result[Unit, @unify.UnificationError] = try? st.unify_rc(
    2,
    @unify.range_ctor("Leaf", []),
    "Node",
    [@unify.range_ctor("Leaf", [])],
  )

  guard bad is Err(_) else { fail("Expected unification failure") }
  inspect(st.lookup(1), content="Some(Ctor(\"Node\", [Ctor(\"Leaf\", [])]))")
}

///|
test "figure3 match_range records pattern and drives match_aux updates" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_undef(@spec.ty("Nat"))
  let st = @unify.UnifyState::new(constraints, [0, 1])

  try! st.match_range(0, "S", [@unify.range_link(1)])

  inspect(st.pattern_count(), content="1")
  inspect(st.lookup(1), content="Some(Fixed)")
}

///|
test "figure3 match_aux returns structured pattern and fixed-branch freshens" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_undef(@spec.ty("Tree"))
  constraints[1] = @unify.range_fixed()
  let st = @unify.UnifyState::new(constraints, [0, 1])

  let p = try! st.match_aux(
    @unify.range_ctor("Wrap", [@unify.range_link(0), @unify.range_link(1)]),
  )

  inspect(p, content="PCtor(\"Wrap\", [PVar(0), PVar(2)])")
  inspect(st.lookup(0), content="Some(Fixed)")
  inspect(st.lookup(2), content="Some(Link(1))")
  inspect(st.equality_count(), content="1")
  inspect(st.unknown_count(), content="3")
}

///|
test "actions reject unknown ids not introduced by fresh" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_fixed()
  let st = @unify.UnifyState::new(constraints, [0])

  let bad_update : Result[Unit, @unify.UnificationError] = try? st.update_constraint(
    42,
    @unify.range_fixed(),
  )
  let bad_eq : Result[Unit, @unify.UnificationError] = try? st.record_equality(
    0, 42,
  )
  let bad_pattern : Result[Unit, @unify.UnificationError] = try? st.record_pattern(
    42,
    @unify.pattern_var(42),
  )

  guard bad_update is Err(_) else { fail("Expected unknown-id error") }
  guard bad_eq is Err(_) else { fail("Expected unknown-id error") }
  guard bad_pattern is Err(_) else { fail("Expected unknown-id error") }
}
