use std::collections::HashMap;
use std::rc::Rc;

use crate::value;

#[derive(Clone, Debug)]
pub struct Env {
    store: HashMap<String, value::Value>,
    next: Option<Rc<Env>>,
}

impl Env {
    pub fn new() -> Env { 
       Env {
            store: HashMap::new(),
            next: None,
        }
    }

    pub fn update(&mut self, key: String, val: value::Value) {
        self.store.insert(key, val);
    }

    pub fn get(&self, key: &str) -> Option<value::Value> {
        let mut current = Some(self);
        while let Some(e) = current {
            if let Some(v) = e.store.get(key) {
                return Some(v.clone());
            }
            current = e.next.as_ref().and_then(|p| Some(p.as_ref()));
        }
        None
    }

    pub fn fork(current: &mut Rc<Env>) -> Env {
        let next = Some(current.clone());
        Env {
            store: HashMap::new(),
            next: next,
        }
    }
}

pub fn update(env: &mut Rc<Env>,  key: String, val: value::Value) {
    if let Some(e) = Rc::get_mut(env) {
        e.update(key, val);
    } else {
        let mut e = Env::fork(env);
        e.update(key, val);
        *env = Rc::new(e);
    }
}
