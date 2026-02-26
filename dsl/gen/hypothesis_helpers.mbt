///|
fn resolve_unknown(
  state : @unify.UnifyState,
  unknown : @unify.Unknown,
) -> (@unify.Unknown, @unify.Range) raise GenCompileError {
  resolve_unknown_loop(state, unknown, [])
}

///|
fn resolve_unknown_loop(
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
    @unify.Link(next) => resolve_unknown_loop(state, next, visited)
    _ => (current, range)
  }
}

///|
fn append_unique_unknowns(
  dst : Array[@unify.Unknown],
  src : Array[@unify.Unknown],
) -> Array[@unify.Unknown] {
  src.fold(init=dst, (acc, unknown) => {
    if !acc.contains(unknown) {
      acc.push(unknown)
    }
    acc
  })
}

///|
fn term_unknowns(
  env : HypothesisEmitEnv,
  term : @spec.Term,
) -> Array[@unify.Unknown] raise GenCompileError {
  match term {
    @spec.Var(name) => [env.unknown_of_var(name)]
    @spec.Ctor(_, args) =>
      args.fold(init=[], (acc, arg) => {
        append_unique_unknowns(acc, term_unknowns(env, arg))
      })
  }
}

///|
fn hypothesis_unknowns(
  env : HypothesisEmitEnv,
  hypothesis : @spec.HypothesisSpec,
) -> Array[@unify.Unknown] raise GenCompileError {
  match hypothesis {
    @spec.RelCall(_, args) | @spec.Predicate(_, args) =>
      args.fold(init=[], (acc, arg) => {
        append_unique_unknowns(acc, term_unknowns(env, arg))
      })
  }
}

///|
fn undef_unknowns(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  hypothesis : @spec.HypothesisSpec,
) -> Array[@unify.Unknown] raise GenCompileError {
  hypothesis_unknowns(env, hypothesis).fold(init=[], (acc, unknown) => {
    let (root, range) = resolve_unknown(state, unknown)
    if range is @unify.Undef(_) && !acc.contains(root) {
      acc.push(root)
    }
    acc
  })
}

///|
fn range_to_expr(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  range : @unify.Range,
  override_unknown : @unify.Unknown,
  override_name : String,
) -> ExprAst raise GenCompileError {
  match range {
    @unify.Link(unknown) =>
      unknown_to_expr(state, env, unknown, override_unknown, override_name)
    @unify.Ctor(name, args) =>
      Ctor(
        name,
        args.map(arg => {
          range_to_expr(state, env, arg, override_unknown, override_name)
        }),
      )
    @unify.Undef(_) | @unify.Fixed => Var("_")
  }
}

///|
fn unknown_to_expr(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  unknown : @unify.Unknown,
  override_unknown : @unify.Unknown,
  override_name : String,
) -> ExprAst raise GenCompileError {
  let (root, range) = resolve_unknown(state, unknown)
  if root == override_unknown {
    Var(override_name)
  } else {
    match range {
      @unify.Undef(_) | @unify.Fixed => Var(env.name_of_unknown(root))
      @unify.Ctor(name, args) =>
        Ctor(
          name,
          args.map(arg => {
            range_to_expr(state, env, arg, override_unknown, override_name)
          }),
        )
      @unify.Link(next) =>
        unknown_to_expr(state, env, next, override_unknown, override_name)
    }
  }
}

///|
fn term_to_expr(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  term : @spec.Term,
  override_unknown : @unify.Unknown,
  override_name : String,
) -> ExprAst raise GenCompileError {
  match term {
    @spec.Var(name) =>
      unknown_to_expr(
        state,
        env,
        env.unknown_of_var(name),
        override_unknown,
        override_name,
      )
    @spec.Ctor(name, args) =>
      Ctor(
        name,
        args.map(arg => {
          term_to_expr(state, env, arg, override_unknown, override_name)
        }),
      )
  }
}

///|
fn direct_var_unknown(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  term : @spec.Term,
) -> @unify.Unknown? raise GenCompileError {
  match term {
    @spec.Var(name) => {
      let (root, _) = resolve_unknown(state, env.unknown_of_var(name))
      Some(root)
    }
    @spec.Ctor(_, _) => None
  }
}

///|
fn hypothesis_expr(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  hypothesis : @spec.HypothesisSpec,
  override_unknown : @unify.Unknown,
  override_name : String,
) -> ExprAst raise GenCompileError {
  match hypothesis {
    @spec.RelCall(name, args) | @spec.Predicate(name, args) =>
      Call(
        name,
        args.map(arg => {
          term_to_expr(state, env, arg, override_unknown, override_name)
        }),
      )
  }
}

///|
fn check_expr(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  hypothesis : @spec.HypothesisSpec,
) -> ExprAst raise GenCompileError {
  hypothesis_expr(state, env, hypothesis, -1, "")
}

///|
fn choose_uk(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  hypothesis : @spec.HypothesisSpec,
  undefined_unknowns : Array[@unify.Unknown],
) -> @unify.Unknown? raise GenCompileError {
  match hypothesis {
    @spec.RelCall(name, args) => {
      guard name == env.r_name else { None }
      for pos in env.out_pos {
        guard pos >= 0 && pos < args.length() else { continue }
        guard direct_var_unknown(state, env, args[pos]) is Some(unknown) else {
          continue
        }
        if undefined_unknowns.contains(unknown) {
          return Some(unknown)
        }
      }
      None
    }
    @spec.Predicate(_, _) => None
  }
}

///|
fn recursive_source(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  args : Array[@spec.Term],
) -> BindSourceAst raise GenCompileError {
  let call_args = env.in_pos.map(pos => {
    guard pos >= 0 && pos < args.length() else {
      fail_gen("Recursive call input index out of bounds: \{pos}")
    }
    term_to_expr(state, env, args[pos], -1, "").to_string()
  })
  RecursiveCall(env.aux_name, call_args)
}

///|
fn final_call_source(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  hypothesis : @spec.HypothesisSpec,
  target_unknown : @unify.Unknown,
) -> BindSourceAst raise GenCompileError {
  let target_name = env.name_of_unknown(target_unknown)
  match hypothesis {
    @spec.RelCall(name, args) if name == env.r_name => {
      let target_is_recursive_output = env.out_pos.fold(init=false, (acc, pos) => {
        if acc || pos < 0 || pos >= args.length() {
          acc
        } else {
          match direct_var_unknown(state, env, args[pos]) {
            Some(unknown) => unknown == target_unknown
            None => false
          }
        }
      })
      if target_is_recursive_output {
        recursive_source(state, env, args)
      } else {
        ArbitraryST(
          target_name,
          hypothesis_expr(state, env, hypothesis, target_unknown, target_name),
        )
      }
    }
    @spec.RelCall(_, _) | @spec.Predicate(_, _) =>
      ArbitraryST(
        target_name,
        hypothesis_expr(state, env, hypothesis, target_unknown, target_name),
      )
  }
}

///|
fn fix_unknowns(
  state : @unify.UnifyState,
  us : Array[@unify.Unknown],
) -> Unit raise GenCompileError {
  us.each(u => {
    state.update_constraint(u, @unify.range_fixed()) catch {
      err =>
        fail_gen(
          "Failed to fix unknown u\{u} while emitting hypotheses: \{err}",
        )
    }
  })
}

///|
fn emit_final_call(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  hypothesis : @spec.HypothesisSpec,
  uk : @unify.Unknown,
  next : GenNode,
) -> GenNode raise GenCompileError {
  let uk_name = env.name_of_unknown(uk)
  let source = final_call_source(state, env, hypothesis, uk)
  Bind(DoM, uk_name, source, next)
}
