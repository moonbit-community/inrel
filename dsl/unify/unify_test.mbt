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
