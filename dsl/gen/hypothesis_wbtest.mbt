///|
fn mk_env(
  x_to_u : @ihashmap.HashMap[String, Int32],
  u_to_name : @ihashmap.HashMap[Int32, String],
) -> HypothesisEmitEnv {
  {
    r_name: "bst",
    aux_name: "aux_arb",
    in_pos: [0, 1],
    out_pos: [2],
    x_to_u,
    u_to_name,
  }
}

///|
test "emit_hypotheses: all fixed hypothesis emits decidable guard" {
  let constraints : Map[Int32, @unify.Range] = Map([])
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_fixed()
  let st = @unify.UnifyState::new(constraints, [0, 1])

  let vars : @ihashmap.HashMap[String, Int32] = @ihashmap.HashMap([
    ("x", 0),
    ("hi", 1),
  ])
  let names : @ihashmap.HashMap[Int32, String] = @ihashmap.HashMap([
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
  let constraints : Map[Int32, @unify.Range] = Map([])
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_link(0)
  constraints[2] = @unify.range_undef(@spec.ty("Nat"))
  let st = @unify.UnifyState::new(constraints, [0, 1, 2])

  let vars : @ihashmap.HashMap[String, Int32] = @ihashmap.HashMap([
    ("lo", 1),
    ("x", 2),
  ])
  let names : @ihashmap.HashMap[Int32, String] = @ihashmap.HashMap([
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
  inspect(display_option(st.lookup(2)), content="Some(Fixed)")
}

///|
test "emit_hypotheses: recursive RelCall with one undef emits aux call" {
  let constraints : Map[Int32, @unify.Range] = Map([])
  constraints[0] = @unify.range_fixed()
  constraints[1] = @unify.range_fixed()
  constraints[2] = @unify.range_undef(@spec.ty("Tree"))
  let st = @unify.UnifyState::new(constraints, [0, 1, 2])

  let vars : @ihashmap.HashMap[String, Int32] = @ihashmap.HashMap([
    ("lo", 0),
    ("hi", 1),
    ("t", 2),
  ])
  let names : @ihashmap.HashMap[Int32, String] = @ihashmap.HashMap([
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
  inspect(display_option(st.lookup(2)), content="Some(Fixed)")
}

///|
test "emit_hypotheses: multiple undef prefers recursive final call" {
  let constraints : Map[Int32, @unify.Range] = Map([])
  constraints[0] = @unify.range_undef(@spec.ty("Nat"))
  constraints[1] = @unify.range_undef(@spec.ty("Nat"))
  constraints[2] = @unify.range_undef(@spec.ty("Tree"))
  let st = @unify.UnifyState::new(constraints, [0, 1, 2])

  let vars : @ihashmap.HashMap[String, Int32] = @ihashmap.HashMap([
    ("lo", 0),
    ("hi", 1),
    ("t", 2),
  ])
  let names : @ihashmap.HashMap[Int32, String] = @ihashmap.HashMap([
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
  inspect(display_option(st.lookup(0)), content="Some(Fixed)")
  inspect(display_option(st.lookup(1)), content="Some(Fixed)")
  inspect(display_option(st.lookup(2)), content="Some(Fixed)")
}

///|
fn[T : Show] display_option(value : T?) -> String {
  match value {
    None => "None"
    Some(value) => "Some(\{value})"
  }
}
