///|
fn u_name(
  u_to_name : @ihashmap.HashMap[@unify.Unknown, String],
  u : @unify.Unknown,
) -> String {
  u_to_name.get(u).unwrap_or("?\{u}")
}

///|
fn resolve_u(
  state : @unify.UnifyState,
  u : @unify.Unknown,
) -> (@unify.Unknown, @unify.Range) raise GenCompileError {
  resolve_u_loop(state, u, [])
}

///|
fn resolve_u_loop(
  state : @unify.UnifyState,
  u_cur : @unify.Unknown,
  visited : Array[@unify.Unknown],
) -> (@unify.Unknown, @unify.Range) raise GenCompileError {
  guard !visited.contains(u_cur) else {
    fail_gen("Cycle detected while resolving unknown u\{u_cur}")
  }
  visited.push(u_cur)

  guard state.lookup(u_cur) is Some(range) else {
    fail_gen("Missing constraint for unknown u\{u_cur}")
  }

  match range {
    @unify.Link(next) => resolve_u_loop(state, next, visited)
    _ => (u_cur, range)
  }
}

///|
fn term_to_range(
  term : @spec.Term,
  x_to_u : @ihashmap.HashMap[String, @unify.Unknown],
) -> @unify.Range raise GenCompileError {
  match term {
    @spec.Var(name) => {
      guard x_to_u.get(name) is Some(unknown) else {
        fail_gen("Unknown variable in constructor conclusion: \{name}")
      }
      @unify.range_link(unknown)
    }
    @spec.Ctor(name, args) =>
      @unify.range_ctor(name, args.map(arg => term_to_range(arg, x_to_u)))
  }
}

///|
fn pattern_ast(
  p : @unify.Pattern,
  u_to_name : @ihashmap.HashMap[@unify.Unknown, String],
) -> PatternAst {
  match p {
    @unify.PVar(unknown) => PVar(u_name(u_to_name, unknown))
    @unify.PCtor(name, args) =>
      PCtor(name, args.map(arg => pattern_ast(arg, u_to_name)))
  }
}

///|
fn expr_of_range(
  state : @unify.UnifyState,
  u_to_name : @ihashmap.HashMap[@unify.Unknown, String],
  range : @unify.Range,
) -> ExprAst raise GenCompileError {
  match range {
    Link(unknown) => expr_of_unknown(state, u_to_name, unknown)
    Ctor(name, args) =>
      Ctor(name, args.map(arg => expr_of_range(state, u_to_name, arg)))
    Fixed | Undef(_) => Var("_")
  }
}

///|
fn expr_of_unknown(
  state : @unify.UnifyState,
  u_to_name : @ihashmap.HashMap[@unify.Unknown, String],
  u : @unify.Unknown,
) -> ExprAst raise GenCompileError {
  let (root, range) = resolve_u(state, u)
  match range {
    Fixed | Undef(_) => Var(u_name(u_to_name, root))
    Ctor(name, args) =>
      Ctor(name, args.map(arg => expr_of_range(state, u_to_name, arg)))
    Link(next) => expr_of_unknown(state, u_to_name, next)
  }
}

///|
fn collect_undef_unknowns(
  state : @unify.UnifyState,
) -> Array[@unify.Unknown] raise GenCompileError {
  state.unknowns
  .to_array()
  .fold(init=[], (acc, unknown) => {
    let (root, range) = resolve_u(state, unknown)
    if range is Undef(_) && !acc.contains(root) {
      acc.push(root)
    }
    acc
  })
}

///|
fn emit_final_assembly(
  state : @unify.UnifyState,
  u_to_name : @ihashmap.HashMap[@unify.Unknown, String],
  out_us : Array[@unify.Unknown],
) -> GenNode raise GenCompileError {
  let undef_roots = collect_undef_unknowns(state)
  undef_roots.each(unknown => {
    state.update_constraint(unknown, @unify.range_fixed()) catch {
      err =>
        fail_gen(
          "Failed to finalize undef root u\{unknown} during assembly: \{err}",
        )
    }
  })

  let payload = out_us.map(out_u => expr_of_unknown(state, u_to_name, out_u))
  let base = RetSome(payload)
  undef_roots.rev_fold(init=base, (acc, unknown) => {
    Bind(Do, u_name(u_to_name, unknown), Arbitrary, acc)
  })
}

///|
fn emit_equalities(
  state : @unify.UnifyState,
  u_to_name : @ihashmap.HashMap[@unify.Unknown, String],
  tail : GenNode,
) -> GenNode {
  state.equalities
  .to_array()
  .rev_fold(init=tail, (acc, eq) => {
    let (u1, u2) = eq
    IfGuard(
      Eq(Var(u_name(u_to_name, u1)), Var(u_name(u_to_name, u2))),
      acc,
      RetNone,
    )
  })
}

///|
fn emit_patterns(
  state : @unify.UnifyState,
  u_to_name : @ihashmap.HashMap[@unify.Unknown, String],
  tail : GenNode,
) -> GenNode {
  state.patterns.rev_fold(init=tail, (acc, entry) => {
    MatchPattern(
      u_name(u_to_name, entry.0),
      pattern_ast(entry.1, u_to_name),
      acc,
      RetNone,
    )
  })
}

///|
fn is_tail_marker(node : GenNode, marker : String) -> Bool {
  guard node is RetSome(values) else { false }
  guard values is [Var(name)] else { false }
  name == marker
}

///|
fn replace_tail_marker(
  node : GenNode,
  marker : String,
  replacement : GenNode,
) -> GenNode {
  if is_tail_marker(node, marker) {
    replacement
  } else {
    match node {
      RetNone | RetSome(_) => node
      Backtrack(cases) =>
        Backtrack(
          cases.map(c => {
            weight: c.weight,
            body: replace_tail_marker(c.body, marker, replacement),
          }),
        )
      MatchPattern(scrutinee, pattern, on_match, on_fail) =>
        MatchPattern(
          scrutinee,
          pattern,
          replace_tail_marker(on_match, marker, replacement),
          replace_tail_marker(on_fail, marker, replacement),
        )
      IfGuard(cond, on_true, on_false) =>
        IfGuard(
          cond,
          replace_tail_marker(on_true, marker, replacement),
          replace_tail_marker(on_false, marker, replacement),
        )
      Bind(kind, name, source, next) =>
        Bind(kind, name, source, replace_tail_marker(next, marker, replacement))
    }
  }
}
