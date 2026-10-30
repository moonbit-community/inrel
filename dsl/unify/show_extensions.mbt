///|
pub extend UnificationError with Eq::{equal, not_equal}

///|
pub extend UnificationError with Show::{output, to_string}

///|
pub extend UnificationError with ToJson::{to_json}

///|
pub extend Pattern with Eq::{equal, not_equal}

///|
pub extend Pattern with Show::{output, to_string}

///|
pub extend Pattern with ToJson::{to_json}

///|
pub extend Range with Eq::{equal, not_equal}

///|
pub extend Range with Show::{output, to_string}

///|
pub extend Range with ToJson::{to_json}
