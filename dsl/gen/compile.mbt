///|
/// Compilation options for Figure 1 / Figure 4 assembly.
pub(all) struct CompileOptions {
  aux_name : String
  size_var : String
  succ_size_var : String
} derive(Eq, ToJson)

///|
pub fn default_compile_options() -> CompileOptions {
  { aux_name: "aux_arb", size_var: "size", succ_size_var: "size'", }
}

///|
fn has_recursive_hypothesis(
  r_name : String,
  ctor_spec : @spec.ConstructorSpec,
) -> Bool {
  for hypothesis in ctor_spec.hypotheses {
    guard hypothesis is @spec.RelCall(name, _) && name == r_name else {
      continue
    }
    break true
  } nobreak {
    false
  }
}

///|
fn init_constructor_state(
  rel : @spec.RelationSpec,
  ctor_spec : @spec.ConstructorSpec,
) -> (
  @unify.UnifyState,
  Array[@unify.Unknown],
  @ihashmap.HashMap[String, @unify.Unknown],
  @ihashmap.HashMap[@unify.Unknown, String],
) {
  let kappa : Map[@unify.Unknown, @unify.Range] = Map([])
  let us : Array[@unify.Unknown] = []
  let param_us : Array[@unify.Unknown] = []
  let mut x_to_u : @ihashmap.HashMap[String, @unify.Unknown] = @ihashmap.HashMap([],
  )
  let mut u_to_name : @ihashmap.HashMap[@unify.Unknown, String] = @ihashmap.HashMap([],
  )

  let mut next_u = 0
  for p in rel.params {
    let u = next_u
    next_u += 1
    us.push(u)
    param_us.push(u)
    x_to_u = x_to_u.add(p.name, u)
    u_to_name = u_to_name.add(u, p.name)
    match p.mode {
      @spec.In => kappa[u] = @unify.range_fixed()
      @spec.Out => kappa[u] = @unify.range_undef(p.ty)
    }
  }

  for b in ctor_spec.binders {
    let u = next_u
    next_u += 1
    us.push(u)
    x_to_u = x_to_u.add(b.name, u)
    u_to_name = u_to_name.add(u, b.name)
    kappa[u] = @unify.range_undef(b.ty)
  }

  let st0 = @unify.UnifyState::new(kappa, us, next_unknown=next_u)
  (st0, param_us, x_to_u, u_to_name)
}

///|
/// Compile one constructor into a Section 4.7 sub-generator body.
///
/// Returns `None` when constructor unification fails (constructor not inhabitable
/// under the current mode assignment), following Figure 4's failure branch.
pub fn compile_constructor_case(
  rel : @spec.RelationSpec,
  ctor_spec : @spec.ConstructorSpec,
  options~ : CompileOptions = default_compile_options(),
) -> WeightedCaseAst? raise {
  guard ctor_spec.conclusion.length() == rel.params.length() else {
    fail_gen(
      "Constructor \{ctor_spec.name} arity mismatch: conclusion has \{ctor_spec.conclusion.length()} terms, relation has \{rel.params.length()} params",
    )
  }

  let (st0, param_us, x_to_u, u_to_name) = init_constructor_state(
    rel, ctor_spec,
  )

  for i in 0..<rel.params.length() {
    let lhs_range = term_to_range(ctor_spec.conclusion[i], x_to_u)
    let rhs_u = param_us[i]
    let unify_result : Result[Unit, @unify.UnificationError] = Ok(
      st0.unify(lhs_range, @unify.range_link(rhs_u)),
    ) catch {
      e => Err(e)
    }
    guard unify_result is Ok(_) else { return None }
  }

  let out_pos = rel.output_positions()
  let out_us = out_pos.map(pos => param_us[pos])
  let marker_name = "__final_assembly_marker"
  let marker_tail : GenNode = RetSome([Var(marker_name)])

  let hypothesis_env : HypothesisEmitEnv = {
    r_name: rel.name,
    aux_name: options.aux_name,
    in_pos: rel.input_positions(),
    out_pos,
    x_to_u,
    u_to_name,
  }

  let g_after_hyp = emit_hypotheses_from_unify(
    st0,
    hypothesis_env,
    ctor_spec.hypotheses,
    marker_tail,
  )
  let g_final = emit_final_assembly(st0, u_to_name, out_us)
  let g_with_final = replace_tail_marker(g_after_hyp, marker_name, g_final)
  let g_with_eq = emit_equalities(st0, u_to_name, g_with_final)
  let g_with_pat = emit_patterns(st0, u_to_name, g_with_eq)
  Some({ weight: ctor_spec.weight, body: g_with_pat, })
}

///|
/// Compile a relation spec into bounded generator AST (Figure 1 / Figure 4).
///
/// Zero-size branch includes only non-recursive constructors; successor-size
/// branch includes all inhabitable constructors.
pub fn compile_relation_to_bounded_generator(
  rel : @spec.RelationSpec,
  options~ : CompileOptions = default_compile_options(),
) -> BoundedGeneratorAst raise {
  let succ_g : Array[WeightedCaseAst] = []
  let zero_g : Array[WeightedCaseAst] = []

  for ctor_spec in rel.constructors {
    guard compile_constructor_case(rel, ctor_spec, options~) is Some(case_ast) else {
      continue
    }
    succ_g.push(case_ast)
    if !has_recursive_hypothesis(rel.name, ctor_spec) {
      zero_g.push(case_ast)
    }
  }

  let input_names = rel.input_positions().map(pos => rel.params[pos].name)
  {
    aux_name: options.aux_name,
    size_var: options.size_var,
    inputs: input_names,
    succ_size_var: options.succ_size_var,
    zero_case: Backtrack(zero_g),
    succ_case: Backtrack(succ_g),
  }
}
