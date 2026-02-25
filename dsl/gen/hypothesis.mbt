///|
/// Environment for Section 4.5 hypothesis emission.
///
/// Correspondence (paper Section 4.5 / Figure 4):
/// - `relation_name` / `aux_name`: relation `R` and recursive generator `aux_arb`
/// - `input_positions` / `output_positions`: mode partition (`in` / `out`)
/// - `var_unknowns`: variables from hypotheses to unification unknown ids
/// - `unknown_names`: pretty names used in emitted generator binds/terms
pub(all) struct HypothesisEmitEnv {
  relation_name : String
  aux_name : String
  input_positions : Array[Int]
  output_positions : Array[Int]
  var_unknowns : @ihashmap.HashMap[String, @unify.Unknown]
  unknown_names : @ihashmap.HashMap[@unify.Unknown, String]
} derive(Eq)

///|
fn HypothesisEmitEnv::name_of_unknown(
  self : HypothesisEmitEnv,
  unknown : @unify.Unknown,
) -> String {
  match self.unknown_names.get(unknown) {
    Some(name) => name
    None => "u\{unknown}"
  }
}

///|
fn HypothesisEmitEnv::unknown_of_var(
  self : HypothesisEmitEnv,
  var_name : String,
) -> @unify.Unknown raise GenCompileError {
  guard self.var_unknowns.get(var_name) is Some(unknown) else {
    fail_gen("Unknown variable in hypothesis environment: \{var_name}")
  }
  unknown
}

///|
fn emit_hypotheses_from(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  hypotheses : Array[@spec.HypothesisSpec],
  index : Int,
  tail : GenNode,
) -> GenNode raise GenCompileError {
  if index >= hypotheses.length() {
    tail
  } else {
    let hypothesis = hypotheses[index]
    let undefined_unknowns = undefined_unknowns_in_hypothesis(
      state, env, hypothesis,
    )
    if undefined_unknowns.is_empty() {
      let next = emit_hypotheses_from(state, env, hypotheses, index + 1, tail)
      IfGuard(
        Decidable(hypothesis_expr(state, env, hypothesis, -1, "")),
        next,
        RetNone,
      )
    } else {
      let target = match
        choose_recursive_target(state, env, hypothesis, undefined_unknowns) {
        Some(unknown) => unknown
        None => undefined_unknowns[undefined_unknowns.length() - 1]
      }
      let others = undefined_unknowns.filter(unknown => unknown != target)
      others.each(unknown => {
        state.update_constraint(unknown, @unify.range_fixed())
      })
      state.update_constraint(target, @unify.range_fixed())

      let next = emit_hypotheses_from(state, env, hypotheses, index + 1, tail)
      let target_name = env.name_of_unknown(target)
      let source = final_call_source(state, env, hypothesis, target)
      let target_bind = Bind(DoM, target_name, source, next)
      others.rev_fold(init=target_bind, (acc, unknown) => {
        Bind(Do, env.name_of_unknown(unknown), Arbitrary, acc)
      })
    }
  }
}

///|
/// Emit Section 4.5 hypothesis-handling code and update `UnifyState`.
///
/// Correspondence (paper Figure 4):
/// - `emit hypotheses [] κ = final assembly κ`
/// - `emit hypotheses ((S e)::ss) κ = ...`
///
/// Branches implemented:
/// - `0` undefined unknowns in `e`: emit a `Decidable` check.
/// - `1` undefined unknown: instantiate via recursive call when possible,
///   otherwise `arbitraryST`.
/// - `>=2` undefined unknowns: instantiate all-but-one with `arbitrary`,
///   then instantiate the final one (recursive call prioritized).
pub fn emit_hypotheses_from_unify(
  state : @unify.UnifyState,
  env : HypothesisEmitEnv,
  hypotheses : Array[@spec.HypothesisSpec],
  tail : GenNode,
) -> GenNode raise GenCompileError {
  emit_hypotheses_from(state, env, hypotheses, 0, tail)
}
