///|
test "unify state actions mirror figure 2 primitives" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_undef(@spec.ty("Tree"))
  let st = @unify.UnifyState::new(constraints, [0, 1])

  st.update_constraint(1, @unify.range_link(0))
  st.record_equality(0, 1)
  st.record_equality(1, 0)
  st.record_pattern(0, @unify.pattern_ctor("S", [@unify.pattern_var(2)]))

  let fresh = st.fresh_unknown(@spec.ty("Tree"))

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

  let ok_uu = st.unify(@unify.range_link(0), @unify.range_link(1))
  let ok_uc = st.unify(
    @unify.range_link(2),
    @unify.range_ctor("Node", [@unify.range_ctor("Leaf", [])]),
  )

  inspect(ok_uu, content="true")
  inspect(ok_uc, content="true")
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

  let ok_ff = st.unify_r(0, @unify.range_fixed(), 1, @unify.range_fixed())
  let ok_fc = st.unify_r(
    2,
    @unify.range_fixed(),
    3,
    @unify.range_ctor("S", [@unify.range_link(4)]),
  )

  inspect(ok_ff, content="true")
  inspect(ok_fc, content="true")
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

  let ok = st.unify_c(
    "Pair",
    [@unify.range_link(0), @unify.range_link(1)],
    "Pair",
    [@unify.range_ctor("Leaf", []), @unify.range_ctor("Leaf", [])],
  )
  let bad = st.unify_c("Pair", [@unify.range_link(0)], "Other", [
    @unify.range_link(1),
  ])

  inspect(ok, content="true")
  inspect(bad, content="false")
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

  let ok = st.unify_rc(0, @unify.range_link(1), "Node", [
    @unify.range_ctor("Leaf", []),
  ])
  let bad = st.unify_rc(2, @unify.range_ctor("Leaf", []), "Node", [
    @unify.range_ctor("Leaf", []),
  ])

  inspect(ok, content="true")
  inspect(bad, content="false")
  inspect(st.lookup(1), content="Some(Ctor(\"Node\", [Ctor(\"Leaf\", [])]))")
}

///|
test "figure3 match_range records pattern and drives match_aux updates" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_undef(@spec.ty("Nat"))
  let st = @unify.UnifyState::new(constraints, [0, 1])

  let ok = st.match_range(0, "S", [@unify.range_link(1)])

  inspect(ok, content="true")
  inspect(st.pattern_count(), content="1")
  inspect(st.lookup(1), content="Some(Fixed)")
}

///|
test "figure3 match_aux returns structured pattern and fixed-branch freshens" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_undef(@spec.ty("Tree"))
  constraints[1] = @unify.range_fixed()
  let st = @unify.UnifyState::new(constraints, [0, 1])

  let p = st.match_aux(
    @unify.range_ctor("Wrap", [@unify.range_link(0), @unify.range_link(1)]),
  )

  inspect(p, content="Some(PCtor(\"Wrap\", [PVar(0), PVar(2)]))")
  inspect(st.lookup(0), content="Some(Fixed)")
  inspect(st.lookup(2), content="Some(Link(1))")
  inspect(st.equality_count(), content="1")
  inspect(st.unknown_count(), content="3")
}
