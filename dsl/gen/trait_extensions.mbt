///|
pub extend BindFlavor with Debug::{to_repr}

///|
pub extend BindFlavor with Eq::{not_equal, equal}

///|
pub extend BindFlavor with ToJson::{to_json}

///|
pub extend BindSourceAst with Debug::{to_repr}

///|
pub extend BindSourceAst with Eq::{not_equal, equal}

///|
pub extend BindSourceAst with Show::{to_string, output}

///|
pub extend BindSourceAst with ToJson::{to_json}

///|
pub extend BoundedGeneratorAst with Debug::{to_repr}

///|
pub extend BoundedGeneratorAst with Eq::{not_equal, equal}

///|
pub extend BoundedGeneratorAst with Show::{to_string, output}

///|
pub extend BoundedGeneratorAst with ToJson::{to_json}

///|
pub extend ExprAst with Debug::{to_repr}

///|
pub extend ExprAst with Eq::{not_equal, equal}

///|
pub extend ExprAst with Show::{to_string, output}

///|
pub extend ExprAst with ToJson::{to_json}

///|
pub extend GenNode with Debug::{to_repr}

///|
pub extend GenNode with Eq::{not_equal, equal}

///|
pub extend GenNode with Show::{to_string, output}

///|
pub extend GenNode with ToJson::{to_json}

///|
pub extend GuardAst with Debug::{to_repr}

///|
pub extend GuardAst with Eq::{not_equal, equal}

///|
pub extend GuardAst with Show::{to_string, output}

///|
pub extend GuardAst with ToJson::{to_json}

///|
pub extend HypothesisEmitEnv with Eq::{not_equal, equal}

///|
pub extend PatternAst with Debug::{to_repr}

///|
pub extend PatternAst with Eq::{not_equal, equal}

///|
pub extend PatternAst with Show::{to_string, output}

///|
pub extend PatternAst with ToJson::{to_json}

///|
pub extend RuntimeValue with Debug::{to_repr}

///|
pub extend RuntimeValue with Eq::{not_equal, equal}

///|
pub extend RuntimeValue with RuntimeDecode::{from_runtime}

///|
pub extend RuntimeValue with RuntimeEncode::{to_runtime}

///|
pub extend RuntimeValue with Show::{to_string, output}

///|
pub extend RuntimeValue with ToJson::{to_json}

///|
pub extend WeightedCaseAst with Debug::{to_repr}

///|
pub extend WeightedCaseAst with Eq::{not_equal, equal}

///|
pub extend WeightedCaseAst with ToJson::{to_json}
