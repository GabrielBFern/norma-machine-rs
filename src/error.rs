use crate::Rule;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum NormaMachineError {
    #[error("Source contains no data")]
    EmptySource,
    #[error(transparent)]
    Parse(#[from] Box<pest::error::Error<Rule>>),
}

// Add manual boxing convert
impl From<pest::error::Error<Rule>> for NormaMachineError {
    fn from(e: pest::error::Error<Rule>) -> NormaMachineError {
        NormaMachineError::Parse(Box::new(e))
    }
}
