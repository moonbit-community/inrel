///|
/// Compilation options for Figure 1 / Figure 4 assembly.
pub(all) struct CompileOptions {
  aux_name : String
  size_var : String
  succ_size_var : String
} derive(Eq, Show, ToJson)

///|
pub fn default_compile_options() -> CompileOptions {
  { aux_name: "aux_arb", size_var: "size", succ_size_var: "size'" }
}

///|
fn c_has_recursive_hypothesis(
  relation_name : String,
  ctor_spec : @spec.ConstructorSpec,
) -> Bool {
  for hypothesis in ctor_spec.hypotheses {
    match hypothesis {
      @spec.RelCall(name, _) if name == relation_name => return true
      _ => ()
    }
  }
  false
}

///|
fn c_build_constructor_state(
  relation : @spec.RelationSpec,
  ctor_spec : @spec.ConstructorSpec,
) -> (
  @unify.UnifyState,
  Array[@unify.Unknown],
  @ihashmap.HashMap[String, @unify.Unknown],
  @ihashmap.HashMap[@unify.Unknown, String],
) {
  let constraints : Map[@unify.Unknown, @unify.Range] = {}
  let unknowns : Array[@unify.Unknown] = []
  let param_unknowns : Array[@unify.Unknown] = []
  let mut var_unknowns : @ihashmap.HashMap[String, @unify.Unknown] = @ihashmap.HashMap::new()
  let mut unknown_names : @ihashmap.HashMap[@unify.Unknown, String] = @ihashmap.HashMap::new()

  let mut next_unknown = 0
  for p in relation.params {
    let unknown = next_unknown
    next_unknown += 1
    unknowns.push(unknown)
    param_unknowns.push(unknown)
    var_unknowns = var_unknowns.add(p.name, unknown)
    unknown_names = unknown_names.add(unknown, p.name)
    match p.mode {
      @spec.In => constraints[unknown] = @unify.range_fixed()
      @spec.Out => constraints[unknown] = @unify.range_undef(p.ty)
    }
  }

  for b in ctor_spec.binders {
    let unknown = next_unknown
    next_unknown += 1
    unknowns.push(unknown)
    var_unknowns = var_unknowns.add(b.name, unknown)
    unknown_names = unknown_names.add(unknown, b.name)
    constraints[unknown] = @unify.range_undef(b.ty)
  }

  let st = @unify.UnifyState::new(constraints, unknowns, next_unknown~)
  (st, param_unknowns, var_unknowns, unknown_names)
}

///|
/// Compile one constructor into a Section 4.7 sub-generator body.
///
/// Returns `None` when constructor unification fails (constructor not inhabitable
/// under the current mode assignment), following Figure 4's failure branch.
pub fn compile_constructor_case(
  relation : @spec.RelationSpec,
  ctor_spec : @spec.ConstructorSpec,
  options? : CompileOptions = default_compile_options(),
) -> WeightedCaseAst? raise GenCompileError {
  guard ctor_spec.conclusion.length() == relation.params.length() else {
    fail_gen(
      "Constructor \{ctor_spec.name} arity mismatch: conclusion has \{ctor_spec.conclusion.length()} terms, relation has \{relation.params.length()} params",
    )
  }

  let (st, param_unknowns, var_unknowns, unknown_names) = c_build_constructor_state(
    relation, ctor_spec,
  )

  for i in 0..<relation.params.length() {
    let lhs_range = c_term_to_range(ctor_spec.conclusion[i], var_unknowns)
    let rhs_unknown = param_unknowns[i]
    guard st.unify(lhs_range, @unify.range_link(rhs_unknown)) else {
      return None
    }
  }

  let output_positions = relation.output_positions()
  let output_unknowns = output_positions.map(pos => param_unknowns[pos])
  let marker_name = "__final_assembly_marker"
  let marker_tail : GenNode = RetSome([Var(marker_name)])

  let hypothesis_env : HypothesisEmitEnv = {
    relation_name: relation.name,
    aux_name: options.aux_name,
    input_positions: relation.input_positions(),
    output_positions,
    var_unknowns,
    unknown_names,
  }

  let with_hypotheses = emit_hypotheses_from_unify(
    st,
    hypothesis_env,
    ctor_spec.hypotheses,
    marker_tail,
  )
  let final_assembly = c_wrap_final_assembly(st, unknown_names, output_unknowns)
  let with_final = c_replace_tail_marker(
    with_hypotheses, marker_name, final_assembly,
  )
  let with_equalities = c_wrap_equalities(st, unknown_names, with_final)
  let with_patterns = c_wrap_patterns(st, unknown_names, with_equalities)
  Some({ weight: ctor_spec.weight, body: with_patterns })
}

///|
/// Compile a relation spec into bounded generator AST (Figure 1 / Figure 4).
///
/// Zero-size branch includes only non-recursive constructors; successor-size
/// branch includes all inhabitable constructors.
pub fn compile_relation_to_bounded_generator(
  relation : @spec.RelationSpec,
  options? : CompileOptions = default_compile_options(),
) -> BoundedGeneratorAst raise GenCompileError {
  let succ_cases : Array[WeightedCaseAst] = []
  let zero_cases : Array[WeightedCaseAst] = []

  for ctor_spec in relation.constructors {
    guard compile_constructor_case(relation, ctor_spec, options~)
      is Some(case_ast) else {
      continue
    }
    succ_cases.push(case_ast)
    if !c_has_recursive_hypothesis(relation.name, ctor_spec) {
      zero_cases.push(case_ast)
    }
  }

  let input_names = relation
    .input_positions()
    .map(pos => relation.params[pos].name)
  {
    aux_name: options.aux_name,
    size_var: options.size_var,
    inputs: input_names,
    succ_size_var: options.succ_size_var,
    zero_case: Backtrack(zero_cases),
    succ_case: Backtrack(succ_cases),
  }
}
