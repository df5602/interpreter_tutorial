use std::fmt;
use std::collections::HashMap;
use std::collections::hash_map::Entry;

use tokens::Type;
use interpreter::Value;

#[derive(Clone)]
pub struct SymbolTableEntry {
    pub var_type: Type,
    pub value: Value,
}

impl fmt::Display for SymbolTableEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.value, self.var_type)
    }
}

pub struct SymbolTable {
    table: HashMap<String, SymbolTableEntry>,
}

impl SymbolTable {
    pub fn new() -> Self {
        SymbolTable { table: HashMap::new() }
    }

    pub fn insert(&mut self, name: String, var_type: Type) -> Result<(), String> {
        match self.table.entry(name) {
            Entry::Vacant(entry) => {
                entry.insert(SymbolTableEntry {
                                 var_type: var_type,
                                 value: Value::NotInitialized,
                             });
                Ok(())
            }
            Entry::Occupied(entry) => Err(format!("Redeclaration of variable `{}`.", entry.key())),
        }
    }

    pub fn update(&mut self, name: String, value: Value) -> bool {
        match self.table.entry(name) {
            Entry::Occupied(mut entry) => {
                entry.get_mut().value = value;
                true
            }
            Entry::Vacant(_) => false,
        }
    }

    pub fn value(&self, name: &str) -> Option<Value> {
        match self.table.get(name) {
            Some(entry) => Some(entry.value.clone()),
            None => None,
        }
    }

    pub fn symbol_type(&self, name: &str) -> Option<Type> {
        match self.table.get(name) {
            Some(entry) => Some(entry.var_type.clone()),
            None => None,
        }
    }

    pub fn print_symbols(&self) {
        for (name, value) in &self.table {
            println!("{}: {} = {}", name, value.var_type, value.value);
        }
    }
}