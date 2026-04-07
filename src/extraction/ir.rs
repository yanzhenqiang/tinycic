//! Intermediate Representation for Code Extraction
//!
//! IR is a simplified representation that sits between CIC terms and target languages.
//! It removes type-theoretic details (like Prop, Sort, Pi types) while preserving
//! computational content.

use std::rc::Rc;

/// IR type - simplified types for code generation
#[derive(Debug, Clone, PartialEq)]
pub enum IrType {
    /// Unit type (void in C, but with one value)
    Unit,
    /// Boolean type
    Bool,
    /// Integer type (arbitrary precision)
    Int,
    /// Natural number type (non-negative integer)
    Nat,
    /// Function type: A -> B
    Arrow(Rc<IrType>, Rc<IrType>),
    /// Product type: A * B (tuple)
    Product(Vec<Rc<IrType>>),
    /// Sum type: A + B (tagged union)
    Sum(Vec<Rc<IrType>>),
    /// Named type (reference to externally defined type)
    Named(String),
    /// Pointer type (for recursive structures)
    Pointer(Rc<IrType>),
}

/// IR expression - computational content
#[derive(Debug, Clone, PartialEq)]
pub enum IrExpr {
    /// Variable reference (De Bruijn index)
    Var(u32),
    /// Named variable (for readability)
    NamedVar(String),
    /// Unit value
    Unit,
    /// Boolean literal
    Bool(bool),
    /// Integer literal
    Int(i64),
    /// Natural number literal
    Nat(u64),
    /// Function application
    App(Rc<IrExpr>, Rc<IrExpr>),
    /// Lambda abstraction: λx. body
    Lambda {
        param_name: String,
        param_ty: Rc<IrType>,
        body: Rc<IrExpr>,
    },
    /// Let binding: let x = value in body
    Let {
        name: String,
        ty: Rc<IrType>,
        value: Rc<IrExpr>,
        body: Rc<IrExpr>,
    },
    /// Pattern match
    Match {
        scrutinee: Rc<IrExpr>,
        cases: Vec<IrCase>,
    },
    /// Constructor application (for sum types)
    Constructor {
        type_name: String,
        ctor_index: usize,
        args: Vec<Rc<IrExpr>>,
    },
    /// Projection (for product types)
    Proj(Rc<IrExpr>, usize),
    /// Primitive operation
    PrimOp(PrimOp, Vec<Rc<IrExpr>>),
    /// If-then-else
    If {
        cond: Rc<IrExpr>,
        then_branch: Rc<IrExpr>,
        else_branch: Rc<IrExpr>,
    },
    /// Fixpoint (for recursive functions)
    Fix {
        name: String,
        ty: Rc<IrType>,
        body: Rc<IrExpr>,
    },
}

/// Case in a pattern match
#[derive(Debug, Clone, PartialEq)]
pub struct IrCase {
    /// Constructor index
    pub ctor_index: usize,
    /// Bound variable names (for readability)
    pub bound_vars: Vec<String>,
    /// Case body
    pub body: Rc<IrExpr>,
}

/// Primitive operations
#[derive(Debug, Clone, PartialEq)]
pub enum PrimOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Neg,
    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    // Boolean
    And,
    Or,
    Not,
    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    BitNot,
    ShiftL,
    ShiftR,
}

/// IR function definition
#[derive(Debug, Clone, PartialEq)]
pub struct IrFunction {
    /// Function name
    pub name: String,
    /// Parameters
    pub params: Vec<(String, Rc<IrType>)>,
    /// Return type
    pub ret_ty: Rc<IrType>,
    /// Function body
    pub body: Rc<IrExpr>,
}

/// IR datatype definition (inductive type)
#[derive(Debug, Clone, PartialEq)]
pub struct IrDatatype {
    /// Type name
    pub name: String,
    /// Type parameters
    pub type_params: Vec<String>,
    /// Constructors
    pub constructors: Vec<IrConstructor>,
}

/// Constructor for IR datatype
#[derive(Debug, Clone, PartialEq)]
pub struct IrConstructor {
    /// Constructor name
    pub name: String,
    /// Constructor fields
    pub fields: Vec<Rc<IrType>>,
}

/// IR module - collection of definitions
#[derive(Debug, Clone, Default)]
pub struct IrModule {
    /// Datatype definitions
    pub datatypes: Vec<IrDatatype>,
    /// Function definitions
    pub functions: Vec<IrFunction>,
    /// Global constants
    pub globals: Vec<(String, Rc<IrType>, Rc<IrExpr>)>,
}

impl IrModule {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_datatype(&mut self, dt: IrDatatype) {
        self.datatypes.push(dt);
    }

    pub fn add_function(&mut self, func: IrFunction) {
        self.functions.push(func);
    }

    pub fn add_global(&mut self, name: String, ty: Rc<IrType>, value: Rc<IrExpr>) {
        self.globals.push((name, ty, value));
    }
}

impl IrType {
    /// Create a function type
    pub fn arrow(domain: Rc<IrType>, codomain: Rc<IrType>) -> Rc<IrType> {
        Rc::new(IrType::Arrow(domain, codomain))
    }

    /// Create a named type
    pub fn named(name: &str) -> Rc<IrType> {
        Rc::new(IrType::Named(name.to_string()))
    }

    /// Create a product type
    pub fn product(types: Vec<Rc<IrType>>) -> Rc<IrType> {
        Rc::new(IrType::Product(types))
    }
}

impl IrExpr {
    /// Create a variable reference
    pub fn var(idx: u32) -> Rc<IrExpr> {
        Rc::new(IrExpr::Var(idx))
    }

    /// Create a named variable
    pub fn named_var(name: &str) -> Rc<IrExpr> {
        Rc::new(IrExpr::NamedVar(name.to_string()))
    }

    /// Create an application
    pub fn app(func: Rc<IrExpr>, arg: Rc<IrExpr>) -> Rc<IrExpr> {
        Rc::new(IrExpr::App(func, arg))
    }

    /// Create a lambda
    pub fn lambda(param_name: &str, param_ty: Rc<IrType>, body: Rc<IrExpr>) -> Rc<IrExpr> {
        Rc::new(IrExpr::Lambda {
            param_name: param_name.to_string(),
            param_ty,
            body,
        })
    }

    /// Create a let binding
    pub fn let_(name: &str, ty: Rc<IrType>, value: Rc<IrExpr>, body: Rc<IrExpr>) -> Rc<IrExpr> {
        Rc::new(IrExpr::Let {
            name: name.to_string(),
            ty,
            value,
            body,
        })
    }

    /// Create an integer literal
    pub fn int(n: i64) -> Rc<IrExpr> {
        Rc::new(IrExpr::Int(n))
    }

    /// Create a natural number literal
    pub fn nat(n: u64) -> Rc<IrExpr> {
        Rc::new(IrExpr::Nat(n))
    }

    /// Create a primitive operation
    pub fn prim_op(op: PrimOp, args: Vec<Rc<IrExpr>>) -> Rc<IrExpr> {
        Rc::new(IrExpr::PrimOp(op, args))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ir_type_arrow() {
        let nat_ty = Rc::new(IrType::Nat);
        let arrow = IrType::arrow(nat_ty.clone(), nat_ty);
        match arrow.as_ref() {
            IrType::Arrow(_, _) => {}
            _ => panic!("Expected Arrow type"),
        }
    }

    #[test]
    fn test_ir_expr_lambda() {
        let nat_ty = Rc::new(IrType::Nat);
        let body = IrExpr::nat(42);
        let lambda = IrExpr::lambda("x", nat_ty, body);

        match lambda.as_ref() {
            IrExpr::Lambda { param_name, .. } => {
                assert_eq!(param_name, "x");
            }
            _ => panic!("Expected Lambda expression"),
        }
    }

    #[test]
    fn test_ir_module() {
        let mut module = IrModule::new();

        // Add a datatype
        let nat_dt = IrDatatype {
            name: "Nat".to_string(),
            type_params: vec![],
            constructors: vec![
                IrConstructor {
                    name: "zero".to_string(),
                    fields: vec![],
                },
                IrConstructor {
                    name: "succ".to_string(),
                    fields: vec![Rc::new(IrType::Named("Nat".to_string()))],
                },
            ],
        };
        module.add_datatype(nat_dt);

        assert_eq!(module.datatypes.len(), 1);
    }
}
