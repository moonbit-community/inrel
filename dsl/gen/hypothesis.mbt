///|
/// Environment for Section 4.5 hypothesis emission.
///
/// Correspondence (paper Section 4.5 / Figure 4):
/// - `r_name` / `aux_name`: relation `R` and recursive generator `aux_arb`
/// - `in_pos` / `out_pos`: mode partition (`in` / `out`)
/// - `x_to_u`: hypothesis variables to unification unknown ids
/// - `u_to_name`: pretty names used in emitted generator binds/terms
pub(all) struct HypothesisEmitEnv {
  r_name : String
  aux_name : String
  in_pos : Array[Int]
  out_pos : Array[Int]
  x_to_u : @ihashmap.HashMap[String, @unify.Unknown]
  u_to_name : @ihashmap.HashMap[@unify.Unknown, String]
} derive(Eq)

///|
fn HypothesisEmitEnv::name_of_unknown(
  self : HypothesisEmitEnv,
  unknown : @unify.Unknown,
) -> String {
  match self.u_to_name.get(unknown) {
    Some(name) => name
    None => "u\{unknown}"
  }
}

///|
fn HypothesisEmitEnv::unknown_of_var(
  self : HypothesisEmitEnv,
  var_name : String,
) -> @unify.Unknown raise GenCompileError {
  guard self.x_to_u.get(var_name) is Some(unknown) else {
    fail_gen("Unknown variable in hypothesis environment: \{var_name}")
  }
  unknown
}

///|
priv struct HypothesisEmitContext {
  state : @unify.UnifyState
  env : HypothesisEmitEnv
  tail : GenNode
}

///|
fn HypothesisEmitContext::emit_hypotheses(
  self : HypothesisEmitContext,
  hypotheses : ArrayView[@spec.HypothesisSpec],
) -> GenNode raise GenCompileError {
  match hypotheses {
    [] => self.tail
    [se, .. ss] => {
      let us : Array[@unify.Unknown] = undef_unknowns(self.state, self.env, se)
      if us.is_empty() {
        // Figure 4 (first branch):
        // if ∀u ∈ e. κ[u] ≠ undef then
        //   if (S e)? then emit hypotheses ss κ else ret None
        // Here, `us = {u ∈ e | κ[u] = undef}`, so `us.is_empty()` is exactly
        // `∀u ∈ e. κ[u] ≠ undef`.

        let next = self.emit_hypotheses(ss)
        IfGuard(Decidable(check_expr(self.state, self.env, se)), next, RetNone)
      } else {
        let uk = match choose_uk(self.state, self.env, se, us) {
          Some(unknown) => unknown
          None => us[us.length() - 1]
        }

        // Figure 4:
        // let {u1..uk} = {u in e | kappa[u] = undef}
        // emit hypotheses ss kappa[ui <- fixed]
        fix_unknowns(self.state, us)

        let next = self.emit_hypotheses(ss)
        let emit_uk = emit_final_call(self.state, self.env, se, uk, next)
        us
        .filter(u => u != uk)
        .rev_fold(init=emit_uk, (acc, u) => {
          Bind(Do, self.env.name_of_unknown(u), Arbitrary, acc)
        })
      }
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
  let ctx : HypothesisEmitContext = { state, env, tail }
  ctx.emit_hypotheses(hypotheses[:])
}
