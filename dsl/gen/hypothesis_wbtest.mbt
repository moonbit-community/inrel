///|
fn mk_env(
  var_unknowns : @ihashmap.HashMap[String, Int],
  unknown_names : @ihashmap.HashMap[Int, String],
) -> HypothesisEmitEnv {
  {
    relation_name: "bst",
    aux_name: "aux_arb",
    input_positions: [0, 1],
    output_positions: [2],
    var_unknowns,
    unknown_names,
  }
}

///|
test "emit_hypotheses: all fixed hypothesis emits decidable guard" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_fixed()
  let st = @unify.UnifyState::new(constraints, [0, 1])

  let vars : @ihashmap.HashMap[String, Int] = @ihashmap.HashMap::from_array([
    ("x", 0),
    ("hi", 1),
  ])
  let names : @ihashmap.HashMap[Int, String] = @ihashmap.HashMap::from_array([
    (0, "x"),
    (1, "hi"),
  ])
  let env = mk_env(vars, names)

  let node = try! emit_hypotheses_from_unify(
    st,
    env,
    [@spec.hypothesis_predicate("<", [@spec.v("x"), @spec.v("hi")])],
    RetSome([Var("ok")]),
  )

  inspect(
    node.to_string(),
    content=(
      #|if (x < hi)? then
      #|  ret (Some ok)
      #|else
      #|  ret None
    ),
  )
}

///|
test "emit_hypotheses: single undef uses arbitraryST and resolves links from unify" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_link(0)
  constraints[2] = @unify.range_undef(@spec.ty("Nat"))
  let st = @unify.UnifyState::new(constraints, [0, 1, 2])

  let vars : @ihashmap.HashMap[String, Int] = @ihashmap.HashMap::from_array([
    ("lo", 1),
    ("x", 2),
  ])
  let names : @ihashmap.HashMap[Int, String] = @ihashmap.HashMap::from_array([
    (0, "in1"),
    (1, "lo"),
    (2, "x"),
  ])
  let env = mk_env(vars, names)

  let node = try! emit_hypotheses_from_unify(
    st,
    env,
    [@spec.hypothesis_predicate("<", [@spec.v("lo"), @spec.v("x")])],
    RetSome([Var("x")]),
  )

  inspect(
    node.to_string(),
    content=(
      #|doM! x <- arbitraryST (fun x => in1 < x);
      #|ret (Some x)
    ),
  )
  inspect(st.lookup(2), content="Some(Fixed)")
}

///|
test "emit_hypotheses: recursive RelCall with one undef emits aux call" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_fixed()
  constraints[2] = @unify.range_undef(@spec.ty("Tree"))
  let st = @unify.UnifyState::new(constraints, [0, 1, 2])

  let vars : @ihashmap.HashMap[String, Int] = @ihashmap.HashMap::from_array([
    ("lo", 0),
    ("hi", 1),
    ("t", 2),
  ])
  let names : @ihashmap.HashMap[Int, String] = @ihashmap.HashMap::from_array([
    (0, "lo"),
    (1, "hi"),
    (2, "t"),
  ])
  let env = mk_env(vars, names)

  let node = try! emit_hypotheses_from_unify(
    st,
    env,
    [
      @spec.hypothesis_rel_call("bst", [
        @spec.v("lo"),
        @spec.v("hi"),
        @spec.v("t"),
      ]),
    ],
    RetSome([Var("t")]),
  )

  inspect(
    node.to_string(),
    content=(
      #|doM! t <- aux_arb lo hi;
      #|ret (Some t)
    ),
  )
  inspect(st.lookup(2), content="Some(Fixed)")
}

///|
test "emit_hypotheses: multiple undef prefers recursive final call" {
  let constraints : Map[Int, @unify.Range] = {}
  constraints[0] = @unify.range_undef(@spec.ty("Nat"))
  constraints[1] = @unify.range_undef(@spec.ty("Nat"))
  constraints[2] = @unify.range_undef(@spec.ty("Tree"))
  let st = @unify.UnifyState::new(constraints, [0, 1, 2])

  let vars : @ihashmap.HashMap[String, Int] = @ihashmap.HashMap::from_array([
    ("lo", 0),
    ("hi", 1),
    ("t", 2),
  ])
  let names : @ihashmap.HashMap[Int, String] = @ihashmap.HashMap::from_array([
    (0, "lo"),
    (1, "hi"),
    (2, "t"),
  ])
  let env = mk_env(vars, names)

  let node = try! emit_hypotheses_from_unify(
    st,
    env,
    [
      @spec.hypothesis_rel_call("bst", [
        @spec.v("lo"),
        @spec.v("hi"),
        @spec.v("t"),
      ]),
    ],
    RetSome([Var("t")]),
  )

  inspect(
    node.to_string(),
    content=(
      #|do! lo <- arbitrary;
      #|do! hi <- arbitrary;
      #|doM! t <- aux_arb lo hi;
      #|ret (Some t)
    ),
  )
  inspect(st.lookup(0), content="Some(Fixed)")
  inspect(st.lookup(1), content="Some(Fixed)")
  inspect(st.lookup(2), content="Some(Fixed)")
}
