use core::fmt;
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    rc::Rc,
};

/// Dependently-typed Lambda Calculus AST.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    /// A named variable.
    Var(String),

    /// The type of types.
    Star,

    /// A function type.
    Pi {
        var: String,
        ty: Rc<Expr>,
        body: Rc<Expr>,
    },

    /// A function abstraction.
    Lambda {
        var: String,
        ty: Rc<Expr>,
        body: Rc<Expr>,
    },

    /// A function application.
    App(Rc<Expr>, Rc<Expr>),

    /// The natural number type.
    Nat,

    /// The first natural number.
    Zero,

    /// The sucessor of a `Nat`.
    Succ(Rc<Expr>),

    /// An inductive proof.
    ElimNat(Rc<Expr>, Rc<Expr>, Rc<Expr>, Rc<Expr>),
}

impl Expr {
    /// Get set of free variables in expression.
    /// Returns a heap-allocated hash set of names;
    /// use `collect_free_vars` to join multiple sets.
    pub fn free_vars(&self) -> HashSet<String> {
        let mut set = HashSet::new();
        self.collect_free_vars(&mut set);
        set
    }

    /// Recursively collect free variables in pre-allocated set.
    pub fn collect_free_vars(&self, set: &mut HashSet<String>) {
        match self {
            Expr::Star | Expr::Nat | Expr::Zero => {}
            Expr::Var(x) => {
                set.insert(x.clone());
            }
            Expr::Pi { var, ty, body } | Expr::Lambda { var, ty, body } => {
                body.collect_free_vars(set);
                set.remove(var);
                ty.collect_free_vars(set);
            }
            Expr::App(e1, e2) => {
                e1.collect_free_vars(set);
                e2.collect_free_vars(set);
            }
            Expr::Succ(e) => {
                e.collect_free_vars(set);
            }
            Expr::ElimNat(e1, e2, e3, e4) => {
                e1.collect_free_vars(set);
                e2.collect_free_vars(set);
                e3.collect_free_vars(set);
                e4.collect_free_vars(set);
            }
        }
    }

    /// Substitute term `value` for `name` in expression.
    /// Alpha-renames sub-expressions as needed.
    pub fn substitute(&self, name: &str, value: &Expr) -> Expr {
        match self {
            Expr::Var(x) => {
                if x == name {
                    value.clone()
                } else {
                    Expr::Var(x.clone())
                }
            }
            Expr::Pi { var, ty, body } => {
                let mut free_vars = HashSet::new();
                value.collect_free_vars(&mut free_vars);

                // Handle alpha-equivalence.
                if var == name || free_vars.contains(var) {
                    self.collect_free_vars(&mut free_vars);
                    let fresh_var = Expr::gen_fresh_var(var, &free_vars);
                    let renamed_body = body.substitute(var, &Expr::Var(fresh_var.clone()));
                    Expr::Pi {
                        var: fresh_var,
                        ty: Rc::new(ty.substitute(name, value)),
                        body: Rc::new(renamed_body.substitute(name, value)),
                    }
                } else {
                    Expr::Pi {
                        var: var.clone(),
                        ty: Rc::new(ty.substitute(name, value)),
                        body: Rc::new(body.substitute(name, value)),
                    }
                }
            }
            Expr::Lambda { var, ty, body } => {
                let mut free_vars = HashSet::new();
                value.collect_free_vars(&mut free_vars);

                // Handle alpha-equivalence.
                if var == name || free_vars.contains(var) {
                    self.collect_free_vars(&mut free_vars);
                    let fresh_var = Expr::gen_fresh_var(var, &free_vars);
                    let renamed_body = body.substitute(var, &Expr::Var(fresh_var.clone()));
                    Expr::Lambda {
                        var: fresh_var,
                        ty: Rc::new(ty.substitute(name, value)),
                        body: Rc::new(renamed_body.substitute(name, value)),
                    }
                } else {
                    Expr::Lambda {
                        var: var.clone(),
                        ty: Rc::new(ty.substitute(name, value)),
                        body: Rc::new(body.substitute(name, value)),
                    }
                }
            }
            Expr::App(e1, e2) => Expr::App(
                Rc::new(e1.substitute(name, value)),
                Rc::new(e2.substitute(name, value)),
            ),
            Expr::Succ(e) => Expr::Succ(Rc::new(e.substitute(name, value))),
            Expr::ElimNat(e1, e2, e3, e4) => Expr::ElimNat(
                Rc::new(e1.substitute(name, value)),
                Rc::new(e2.substitute(name, value)),
                Rc::new(e3.substitute(name, value)),
                Rc::new(e4.substitute(name, value)),
            ),
            Expr::Star | Expr::Nat | Expr::Zero => self.clone(),
        }
    }

    /// Evaluate expression with full beta-reduction.
    /// Errors if it does not terminate within 1000 steps.
    pub fn reduce(&self) -> Result<Expr, Error> {
        const MAX_STEPS: i32 = 1000;
        self.limit_reduce(MAX_STEPS)
    }

    /// Evaluate expression with full beta-reduction.
    /// Errors if it does not terminate within the limit.
    pub fn limit_reduce(&self, max_steps: i32) -> Result<Expr, Error> {
        let mut expr = self.clone();
        let mut steps = 0;

        loop {
            if steps >= max_steps {
                return Err(Error::InfiniteLoop(expr));
            }

            // Attempt to take a step.
            match expr.step() {
                Ok(reduced) => {
                    if Expr::is_equal(&expr, &reduced) {
                        break;
                    }
                    expr = reduced;
                    steps += 1;
                }
                Err(_) => {
                    break;
                }
            }
        }

        Ok(expr)
    }

    /// Evaluate one step with full beta-reduction.
    pub fn step(&self) -> Result<Expr, Error> {
        match self {
            Expr::App(e1, e2) => match &**e1 {
                Expr::Lambda { var, ty: _, body } => {
                    // Apply beta-reduction.
                    Ok(body.substitute(var, &e2))
                }
                _ => {
                    // Attempt to reduce `e1`.
                    if let Ok(reduced_e1) = e1.step() {
                        return Ok(Expr::App(Rc::new(reduced_e1), Rc::clone(e2)));
                    }

                    // Attempt to reduce `e2`.
                    if let Ok(reduced_e2) = e2.step() {
                        return Ok(Expr::App(Rc::clone(e1), Rc::new(reduced_e2)));
                    }

                    Err(Error::CannotReduce(self.clone()))
                }
            },
            Expr::Succ(e) => {
                // Attempt to reduce inner expression.
                let reduced_e = e.step()?;
                Ok(Expr::Succ(Rc::new(reduced_e)))
            }
            Expr::ElimNat(e1, e2, e3, e4) => match &**e4 {
                Expr::Zero => Ok((**e2).clone()),
                Expr::Succ(e4_inner) => {
                    // Apply inductive hypothesis.
                    let elim = Expr::ElimNat(
                        Rc::clone(e1),
                        Rc::clone(e2),
                        Rc::clone(e3),
                        Rc::clone(e4_inner),
                    );

                    // Construct the application.
                    let app = Expr::App(
                        Rc::new(Expr::App(Rc::clone(e3), Rc::clone(e4))),
                        Rc::new(elim),
                    );

                    Ok(app)
                }
                _ => {
                    // Attempt to reduce `e1`.
                    if let Ok(reduced_e1) = e1.step() {
                        return Ok(Expr::ElimNat(
                            Rc::new(reduced_e1),
                            Rc::clone(e2),
                            Rc::clone(e3),
                            e4.clone(),
                        ));
                    }

                    // Attempt to reduce `e2`.
                    if let Ok(reduced_e2) = e2.step() {
                        return Ok(Expr::ElimNat(
                            Rc::clone(e1),
                            Rc::new(reduced_e2),
                            Rc::clone(e3),
                            e4.clone(),
                        ));
                    }

                    // Attempt to reduce `e3`.
                    if let Ok(reduced_e3) = e3.step() {
                        return Ok(Expr::ElimNat(
                            Rc::clone(e1),
                            Rc::clone(e2),
                            Rc::new(reduced_e3),
                            e4.clone(),
                        ));
                    }

                    // Attempt to reduce `e4`.
                    if let Ok(reduced_e4) = e4.step() {
                        return Ok(Expr::ElimNat(
                            Rc::clone(e1),
                            Rc::clone(e2),
                            Rc::clone(e3),
                            Rc::new(reduced_e4),
                        ));
                    }

                    Err(Error::CannotReduce(self.clone()))
                }
            },
            Expr::Pi { var, ty, body } => {
                // Attempt to reduce the type.
                if let Ok(reduced_ty) = ty.step() {
                    return Ok(Expr::Pi {
                        var: var.clone(),
                        ty: Rc::new(reduced_ty),
                        body: Rc::clone(body),
                    });
                }

                // Attempt to reduce the body.
                if let Ok(reduced_body) = body.step() {
                    return Ok(Expr::Pi {
                        var: var.clone(),
                        ty: Rc::clone(ty),
                        body: Rc::new(reduced_body),
                    });
                }

                Err(Error::CannotReduce(self.clone()))
            }
            Expr::Lambda { var, ty, body } => {
                // Attempt to reduce the type.
                if let Ok(reduced_ty) = ty.step() {
                    return Ok(Expr::Lambda {
                        var: var.clone(),
                        ty: Rc::new(reduced_ty),
                        body: Rc::clone(body),
                    });
                }

                // Attempt to reduce the body.
                if let Ok(reduced_body) = body.step() {
                    return Ok(Expr::Lambda {
                        var: var.clone(),
                        ty: Rc::clone(ty),
                        body: Rc::new(reduced_body),
                    });
                }

                Err(Error::CannotReduce(self.clone()))
            }
            Expr::Var(_) | Expr::Star | Expr::Nat | Expr::Zero => {
                Err(Error::CannotReduce(self.clone()))
            }
        }
    }

    /// Type check expression in the empty environment.
    pub fn type_check(&self) -> Result<Expr, Error> {
        let mut env = Environment::new();
        self.env_type_check(&mut env)
    }

    /// Type check expression in environment `env`.
    pub fn env_type_check(&self, env: &mut Environment) -> Result<Expr, Error> {
        match self {
            Expr::Var(x) => match env.get(x) {
                Some(ty) => Ok((*ty).clone()),
                None => Err(Error::VarNotFound(x.clone())),
            },
            Expr::Star => Ok(Expr::Star),
            Expr::Pi { var, ty, body } => {
                // Ensure `ty` is a type.
                let ty_kind = ty.env_type_check(env)?;
                if !Expr::type_equal(&ty_kind, &Expr::Star, env)? {
                    return Err(Error::TypeMismatch {
                        expected: Expr::Star,
                        found: ty_kind,
                    });
                }

                // Extend environment with argument type.
                let reduced_ty = Rc::new(ty.reduce()?);
                env.extend(var.clone(), reduced_ty);

                // Ensure `body` is a type.
                let body_kind = body.env_type_check(env)?;
                if !Expr::type_equal(&body_kind, &Expr::Star, env)? {
                    return Err(Error::TypeMismatch {
                        expected: Expr::Star,
                        found: body_kind,
                    });
                }

                // Contract the environment.
                env.pop(&var);

                Ok(Expr::Star)
            }
            Expr::Lambda { var, ty, body } => {
                // Ensure `ty` is a type.
                let ty_kind = ty.env_type_check(env)?;
                if !Expr::type_equal(&ty_kind, &Expr::Star, env)? {
                    return Err(Error::TypeMismatch {
                        expected: Expr::Star,
                        found: ty_kind,
                    });
                }

                // Extend environment with argument type.
                let reduced_ty = Rc::new(ty.reduce()?);
                env.extend(var.clone(), Rc::clone(&reduced_ty));

                // Construct pi-type from body.
                let body_ty = body.env_type_check(env)?;
                let body_ty_kind = body_ty.env_type_check(env)?;
                if !Expr::type_equal(&body_ty_kind, &Expr::Star, env)? {
                    return Err(Error::TypeMismatch {
                        expected: Expr::Star,
                        found: body_ty_kind,
                    });
                }

                // Contract the environment.
                env.pop(&var);

                Ok(Expr::Pi {
                    var: var.clone(),
                    ty: Rc::clone(&reduced_ty),
                    body: Rc::new(body_ty),
                }.reduce()?)
            }
            Expr::App(e1, e2) => {
                let ty1 = e1.env_type_check(env)?;
                let ty2 = e2.env_type_check(env)?;

                match ty1 {
                    // Ensure `e1` is a function.
                    Expr::Pi { var, ty, body } => {
                        if !Expr::type_equal(&ty, &ty2, env)? {
                            return Err(Error::TypeMismatch {
                                expected: (*ty).clone(),
                                found: ty2,
                            });
                        }

                        // Substitute and reduce.
                        Ok(body.substitute(&var, e2).reduce()?)
                    }
                    _ => Err(Error::InvalidApplication((**e1).clone())),
                }
            }
            Expr::Nat => Ok(Expr::Star),
            Expr::Zero => Ok(Expr::Nat),
            Expr::Succ(e) => {
                // Ensure `e` is a number.
                let ty = e.env_type_check(env)?;
                if !Expr::type_equal(&ty, &Expr::Nat, env)? {
                    return Err(Error::InvalidSucc);
                }

                Ok(Expr::Nat)
            }
            Expr::ElimNat(e1, e2, e3, e4) => {
                let e1_ty = e1.env_type_check(env)?;
                match e1_ty {
                    Expr::Pi { var: _, ty, body } => {
                        // Ensure `e1` is a function from numbers to types.
                        if !Expr::type_equal(&ty, &Expr::Nat, env)? {
                            return Err(Error::TypeMismatch {
                                expected: Expr::Nat,
                                found: (*ty).clone(),
                            });
                        }

                        if !Expr::type_equal(&body, &Expr::Star, env)? {
                            return Err(Error::TypeMismatch {
                                expected: Expr::Star,
                                found: (*body).clone(),
                            });
                        }

                        // Ensure `e2` is a base case (i.e., `e1 0`).
                        // let e1_zero = body.substitute(&var, &Expr::Zero).reduce()?;
                        let e1_zero = Rc::new(Expr::App(Rc::clone(e1), Rc::new(Expr::Zero))).reduce()?;
                        let e2_ty = e2.env_type_check(env)?;

                        if !Expr::type_equal(&e1_zero, &e2_ty, env)? {
                            return Err(Error::TypeMismatch {
                                expected: e1_zero,
                                found: e2_ty,
                            });
                        }

                        // Ensure `e3` is an inductive step.
                        let e3_ty = e3.env_type_check(env)?;
                        let reduced_e1 = Rc::new(e1.reduce()?);
                        let expected_e3_ty = Expr::Pi {
                            var: "x".to_string(),
                            ty: Rc::new(Expr::Nat),
                            body: Rc::new(Expr::Pi {
                                var: "_".to_string(),
                                ty: Rc::new(Expr::App(
                                    Rc::clone(&reduced_e1),
                                    Rc::new(Expr::Var("x".to_string())),
                                )),
                                body: Rc::new(Expr::App(
                                    Rc::clone(&reduced_e1),
                                    Rc::new(Expr::Succ(Rc::new(Expr::Var("x".to_string())))),
                                )),
                            }),
                        }
                        .reduce()?;

                        if !Expr::type_equal(&expected_e3_ty, &e3_ty, env)? {
                            return Err(Error::TypeMismatch {
                                expected: expected_e3_ty,
                                found: e3_ty,
                            });
                        }

                        // Ensure `e4` is a number.
                        let e4_ty = e4.env_type_check(env)?;
                        if !Expr::type_equal(&e4_ty, &Expr::Nat, env)? {
                            return Err(Error::TypeMismatch {
                                expected: Expr::Nat,
                                found: e4_ty,
                            });
                        }

                        let reduced_e4 = Rc::new(e4.reduce()?);
                        Ok(Expr::App(Rc::clone(&reduced_e1), Rc::clone(&reduced_e4)).reduce()?)
                    }
                    _ => Err(Error::CannotType(
                        "First argument of elimNat must be a Pi-type from Nat -> Type.".to_string(),
                    )),
                }
            }
        }
    }

    /// Type expression with all type variables resolved.
    fn env_type_resolve(&self, env: &mut Environment) -> Result<Expr, Error> {
        match self {
            Expr::Var(x) => match env.get(x) {
                Some(ty) => Ok((*ty).clone()),
                None => Err(Error::VarNotFound(x.clone())),
            },
            Expr::Pi { var, ty, body } => {
                let resolved_ty = Rc::new(ty.env_type_resolve(env)?.reduce()?);
                
                // Extend environment.
                env.extend(var.clone(), Rc::clone(&resolved_ty));
                let resolved_body = body.env_type_resolve(env)?;

                // Contract environment.
                env.pop(var);

                Ok(Expr::Pi {
                    var: var.clone(),
                    ty: Rc::clone(&resolved_ty),
                    body: Rc::new(resolved_body),
                })
            },
            Expr::Lambda { var, ty, body } => {
                let resolved_ty = Rc::new(ty.env_type_resolve(env)?.reduce()?);
                
                // Extend environment.
                env.extend(var.clone(), Rc::clone(&resolved_ty));
                let resolved_body = body.env_type_resolve(env)?;

                // Contract environment.
                env.pop(var);

                Ok(Expr::Lambda {
                    var: var.clone(),
                    ty: Rc::clone(&resolved_ty),
                    body: Rc::new(resolved_body),
                })
            },
            Expr::App(e1, e2) => Ok(Expr::App(
                Rc::new(e1.env_type_resolve(env)?),
                Rc::new(e2.env_type_resolve(env)?),
            )),
            Expr::Succ(e) => Ok(e.env_type_resolve(env)?),
            Expr::ElimNat(e1, e2, e3, e4) => Ok(Expr::ElimNat(
                Rc::new(e1.env_type_resolve(env)?),
                Rc::new(e2.env_type_resolve(env)?),
                Rc::new(e3.env_type_resolve(env)?),
                Rc::new(e4.env_type_resolve(env)?),
            )),
            Expr::Star | Expr::Nat | Expr::Zero => Ok(self.clone()),
        }
    }

    /// Check if two expressions are alpha-equivalent.
    pub fn is_equal(e1: &Expr, e2: &Expr) -> bool {
        match (e1, e2) {
            (Expr::Var(x), Expr::Var(y)) => x == y,
            (Expr::Star, Expr::Star) | (Expr::Nat, Expr::Nat) | (Expr::Zero, Expr::Zero) => true,
            (
                Expr::Pi {
                    var: var1,
                    ty: ty1,
                    body: body1,
                },
                Expr::Pi {
                    var: var2,
                    ty: ty2,
                    body: body2,
                },
            )
            | (
                Expr::Lambda {
                    var: var1,
                    ty: ty1,
                    body: body1,
                },
                Expr::Lambda {
                    var: var2,
                    ty: ty2,
                    body: body2,
                },
            ) => {
                if var1 == var2 {
                    return Expr::is_equal(ty1, ty2) && Expr::is_equal(body1, body2);
                }

                // Generate a fresh name to compare.
                let mut free_vars = HashSet::new();
                body1.collect_free_vars(&mut free_vars);
                body2.collect_free_vars(&mut free_vars);
                let fresh_var = Expr::gen_fresh_var(var1, &free_vars);

                // Rebuild each sub-expression.
                let renamed_body1 = body1.substitute(&var1, &Expr::Var(fresh_var.clone()));
                let renamed_body2 = body2.substitute(&var2, &Expr::Var(fresh_var.clone()));
                Expr::is_equal(ty1, ty2) && Expr::is_equal(&renamed_body1, &renamed_body2)
            }
            (Expr::App(a1, b1), Expr::App(a2, b2)) => {
                Expr::is_equal(a1, a2) && Expr::is_equal(b1, b2)
            }
            (Expr::Succ(n1), Expr::Succ(n2)) => Expr::is_equal(n1, n2),
            (Expr::ElimNat(a1, b1, c1, d1), Expr::ElimNat(a2, b2, c2, d2)) => {
                Expr::is_equal(a1, a2)
                    && Expr::is_equal(b1, b2)
                    && Expr::is_equal(c1, c2)
                    && Expr::is_equal(d1, d2)
            }
            (_, _) => false,
        }
    }

    /// Check alpha-equivalence of type expressions with free type variables.
    pub fn type_equal(e1: &Expr, e2: &Expr, env: &mut Environment) -> Result<bool, Error> {
        Ok(Expr::is_equal(&e1.env_type_resolve(env)?, &e2.env_type_resolve(env)?))
    }

    /// Helper to generate fresh variable names.
    fn gen_fresh_var(var: &str, used: &HashSet<String>) -> String {
        let mut i = 0;
        loop {
            let fresh_var = format!("{}_{}", var, i);
            if !used.contains(&fresh_var) {
                return fresh_var;
            }
            i += 1;
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Var(x) => write!(f, "{}", x),
            Expr::Star => write!(f, "⋆"),
            Expr::Pi { var, ty, body } => {
                write!(f, "({} : {}) -> {}", var, ty, body)
            }
            Expr::Lambda { var, ty, body } => {
                write!(f, "λ({} : {}). {}", var, ty, body)
            }
            Expr::App(e1, e2) => write!(f, "({}) ({})", e1, e2),
            Expr::Nat => write!(f, "N"),
            Expr::Zero => write!(f, "0"),
            Expr::Succ(e) => write!(f, "succ {}", e),
            Expr::ElimNat(e1, e2, e3, e4) => {
                write!(f, "elimNat ({}) ({}) ({}) ({})", e1, e2, e3, e4)
            }
        }
    }
}

/// Variable environment.
pub struct Environment {
    bindings: HashMap<String, Vec<Rc<Expr>>>,
}

impl Environment {
    /// Construct a new environment.
    pub fn new() -> Self {
        Environment {
            bindings: HashMap::new(),
        }
    }

    /// Insert a new type into the environment.
    pub fn extend(&mut self, var: String, ty: Rc<Expr>) {
        self.bindings.entry(var).or_insert_with(Vec::new).push(ty);
    }

    /// Get the most recent type of variable in environment.
    pub fn get(&self, var: &str) -> Option<Rc<Expr>> {
        // let ty = self.bindings.get(var).and_then(|vec| vec.last());
        // match ty {
        //     Some(expr) => match &**expr {
        //         Expr::Var(x) => self.get(x),
        //         _ => Some(Rc::clone(expr)),
        //     },
        //     None => None,
        // }
        self.bindings.get(var).and_then(|vec| vec.last()).cloned()
    }

    /// Pop the most recent type of variable in environment.
    pub fn pop(&mut self, var: &str) {
        if let Some(types) = self.bindings.get_mut(var) {
            types.pop();
            if types.is_empty() {
                self.bindings.remove(var);
            }
        }
    }
}

/// Failure to type-check an expression.
#[derive(Debug)]
pub enum Error {
    VarNotFound(String),
    TypeMismatch { expected: Expr, found: Expr },
    CannotType(String),
    CannotReduce(Expr),
    InfiniteLoop(Expr),
    InvalidApplication(Expr),
    InvalidSucc,
    InvalidElimNat,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::VarNotFound(x) => write!(f, "Variable `{}` not found in environment.", x),
            Error::TypeMismatch { expected, found } => {
                write!(
                    f,
                    "Type mismatch: expected `{}`, found `{}`.",
                    expected, found
                )
            }
            Error::CannotType(msg) => write!(f, "Cannot type `{}`.", msg),
            Error::CannotReduce(expr) => write!(f, "Cannot reduce expression `{}`.", expr),
            Error::InfiniteLoop(expr) => write!(f, "Detected infinite loop in `{}`.", expr),
            Error::InvalidApplication(expr) => {
                write!(f, "Invalid application: `{}` is not a function.", expr)
            }
            Error::InvalidSucc => write!(f, "Cannot `succ` with given argument."),
            Error::InvalidElimNat => write!(f, "Cannot `elimNat` with given arguments."),
        }
    }
}

impl std::error::Error for Error {}
