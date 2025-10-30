use rustc_span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FluxPanicType {
    BoundsCheck,
    DivisionByZero,
    RemainderByZero,
    ExplicitPanic,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FluxHint {
    pub function: String,
    pub span: Span,
    pub assertion: String,
    pub panic_type: FluxPanicType,
}