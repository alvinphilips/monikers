#[derive(Debug, Clone, Copy)]
pub enum Object {
    Integer(usize),
    Boolean(bool),
    Null,
}