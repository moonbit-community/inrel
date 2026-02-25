///|
fn c_name_of_unknown(
  unknown_names : @ihashmap.HashMap[@unify.Unknown, String],
  unknown : @unify.Unknown,
) -> String {
  match unknown_names.get(unknown) {
    Some(name) => name
    None => "u\{unknown}"
  }
}

///|
fn c_resolve_unknown(
  state : @unify.UnifyState,
  unknown : @unify.Unknown,
) -> (@unify.Unknown, @unify.Range) raise GenCompileError {
  c_resolve_unknown_loop(state, unknown, [])
}

///|
fn c_resolve_unknown_loop(
  state : @unify.UnifyState,
  current : @unify.Unknown,
  visited : Array[@unify.Unknown],
) -> (@unify.Unknown, @unify.Range) raise GenCompileError {
  guard !visited.contains(current) else {
    fail_gen("Cycle detected while resolving unknown u\{current}")
  }
  visited.push(current)

  guard state.lookup(current) is Some(range) else {
    fail_gen("Missing constraint for unknown u\{current}")
  }

  match range {
    @unify.Link(next) => c_resolve_unknown_loop(state, next, visited)
    _ => (current, range)
  }
}

///|
fn c_term_to_range(
  term : @spec.Term,
  var_unknowns : @ihashmap.HashMap[String, @unify.Unknown],
) -> @unify.Range raise GenCompileError {
  match term {
    @spec.Var(name) => {
      guard var_unknowns.get(name) is Some(unknown) else {
        fail_gen("Unknown variable in constructor conclusion: \{name}")
      }
      @unify.range_link(unknown)
    }
    @spec.Ctor(name, args) =>
      @unify.range_ctor(
        name,
        args.map(arg => c_term_to_range(arg, var_unknowns)),
      )
  }
}

///|
fn c_pattern_to_ast(
  pattern : @unify.Pattern,
  unknown_names : @ihashmap.HashMap[@unify.Unknown, String],
) -> PatternAst {
  match pattern {
    @unify.PVar(unknown) => PVar(c_name_of_unknown(unknown_names, unknown))
    @unify.PCtor(name, args) =>
      PCtor(name, args.map(arg => c_pattern_to_ast(arg, unknown_names)))
  }
}

///|
fn c_result_expr_from_range(
  state : @unify.UnifyState,
  unknown_names : @ihashmap.HashMap[@unify.Unknown, String],
  range : @unify.Range,
) -> ExprAst raise GenCompileError {
  match range {
    Link(unknown) => c_result_expr_from_unknown(state, unknown_names, unknown)
    Ctor(name, args) =>
      Ctor(
        name,
        args.map(arg => c_result_expr_from_range(state, unknown_names, arg)),
      )
    Fixed | Undef(_) => Var("_")
  }
}

///|
fn c_result_expr_from_unknown(
  state : @unify.UnifyState,
  unknown_names : @ihashmap.HashMap[@unify.Unknown, String],
  unknown : @unify.Unknown,
) -> ExprAst raise GenCompileError {
  let (root, range) = c_resolve_unknown(state, unknown)
  match range {
    Fixed | Undef(_) => Var(c_name_of_unknown(unknown_names, root))
    Ctor(name, args) =>
      Ctor(
        name,
        args.map(arg => c_result_expr_from_range(state, unknown_names, arg)),
      )
    Link(next) => c_result_expr_from_unknown(state, unknown_names, next)
  }
}

///|
fn c_collect_remaining_undefs(
  state : @unify.UnifyState,
) -> Array[@unify.Unknown] raise GenCompileError {
  state.unknowns
  .to_array()
  .fold(init=[], (acc, unknown) => {
    let (root, range) = c_resolve_unknown(state, unknown)
    if range is Undef(_) && !acc.contains(root) {
      acc.push(root)
    }
    acc
  })
}

///|
fn c_wrap_final_assembly(
  state : @unify.UnifyState,
  unknown_names : @ihashmap.HashMap[@unify.Unknown, String],
  output_unknowns : Array[@unify.Unknown],
) -> GenNode raise GenCompileError {
  let undef_roots = c_collect_remaining_undefs(state)
  undef_roots.each(unknown => {
    state.update_constraint(unknown, @unify.range_fixed()) catch {
      err =>
        fail_gen(
          "Failed to finalize undef root u\{unknown} during assembly: \{err}",
        )
    }
  })

  let payload = output_unknowns.map(out_unknown => {
    c_result_expr_from_unknown(state, unknown_names, out_unknown)
  })
  let base = RetSome(payload)
  undef_roots.rev_fold(init=base, (acc, unknown) => {
    Bind(Do, c_name_of_unknown(unknown_names, unknown), Arbitrary, acc)
  })
}

///|
fn c_wrap_equalities(
  state : @unify.UnifyState,
  unknown_names : @ihashmap.HashMap[@unify.Unknown, String],
  tail : GenNode,
) -> GenNode {
  state.equalities
  .to_array()
  .rev_fold(init=tail, (acc, eq) => {
    IfGuard(
      Eq(
        Var(c_name_of_unknown(unknown_names, eq.0)),
        Var(c_name_of_unknown(unknown_names, eq.1)),
      ),
      acc,
      RetNone,
    )
  })
}

///|
fn c_wrap_patterns(
  state : @unify.UnifyState,
  unknown_names : @ihashmap.HashMap[@unify.Unknown, String],
  tail : GenNode,
) -> GenNode {
  state.patterns.rev_fold(init=tail, (acc, entry) => {
    MatchPattern(
      c_name_of_unknown(unknown_names, entry.0),
      c_pattern_to_ast(entry.1, unknown_names),
      acc,
      RetNone,
    )
  })
}

///|
fn c_is_tail_marker(node : GenNode, marker : String) -> Bool {
  guard node is RetSome(values) else { false }
  guard values is [Var(name)] else { false }
  name == marker
}

///|
fn c_replace_tail_marker(
  node : GenNode,
  marker : String,
  replacement : GenNode,
) -> GenNode {
  if c_is_tail_marker(node, marker) {
    replacement
  } else {
    match node {
      RetNone | RetSome(_) => node
      Backtrack(cases) =>
        Backtrack(
          cases.map(c => {
            weight: c.weight,
            body: c_replace_tail_marker(c.body, marker, replacement),
          }),
        )
      MatchPattern(scrutinee, pattern, on_match, on_fail) =>
        MatchPattern(
          scrutinee,
          pattern,
          c_replace_tail_marker(on_match, marker, replacement),
          c_replace_tail_marker(on_fail, marker, replacement),
        )
      IfGuard(cond, on_true, on_false) =>
        IfGuard(
          cond,
          c_replace_tail_marker(on_true, marker, replacement),
          c_replace_tail_marker(on_false, marker, replacement),
        )
      Bind(kind, name, source, next) =>
        Bind(
          kind,
          name,
          source,
          c_replace_tail_marker(next, marker, replacement),
        )
    }
  }
}
