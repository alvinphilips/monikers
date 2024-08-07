use crate::{ast::Node, object::Object};

pub struct Evaluator {

}

impl Evaluator {
    pub fn eval(&mut self, _node: impl Node) -> Object {
        Object::Null
    }
}