use super::environment::Environment;
use super::expr::*;
use std::collections::HashMap;
use std::rc::Rc;


/// A simple parser for Lean-like expressions in the REPL.
///
/// Supported syntax:
///   - Constants/variables: Nat, zero, succ, x
///   - Application: f a b (left-associative)
///   - Lambda: \x : Nat . x   or   fun x => x
///   - Pi: Nat -> Nat   or   (x : Nat) -> Nat
///   - Let: let x := zero in x   or   let x : Nat := zero in x
///   - Have: have h : P := proof in e
///   - Match: match e : T with | ctor1 => e1 | ctor2 x => e2
///   - Sort: Type, Prop
///   - Parens: (e)
///   - Numeric literals: 0, 1, 2, ... (expand to succ^n zero in parser)

#[derive(Debug, Clone)]
pub enum ParsedExpr {
    BVar(u64),
    Const(String),
    /// Numeric literal (e.g. 3). Expansion to succ^n zero is deferred to to_expr
    /// so the environment can resolve the actual constructor names.
    NatLit(u64),
    App(Box<ParsedExpr>, Box<ParsedExpr>),
    Lambda(String, Box<ParsedExpr>, Box<ParsedExpr>), // name, type, body
    Pi(String, Box<ParsedExpr>, Box<ParsedExpr>),     // name, type, body
    Let(String, Box<ParsedExpr>, Box<ParsedExpr>, Box<ParsedExpr>), // name, ty, val, body
    Sort(u64), // 0 = Prop, 1 = Type
    /// match scrutinee : motive with | pat1 => e1 | pat2 x => e2
    Match(Box<ParsedExpr>, Box<ParsedExpr>, Vec<(ParsedExpr, ParsedExpr)>),
    /// by tactic1; tactic2; ...
    TacticBlock(Vec<String>),
    /// Metavariable / solve variable: ?name
    MVar(String),
    /// calc block: calc ty; lhs0 = rhs0 := proof0; rhs1 = rhs1 := proof1; ...
    /// Each step is (lhs, rhs, proof). lhs of step i+1 must equal rhs of step i.
    /// Desugars to nested eq_subst calls.
    Calc(Box<ParsedExpr>, Vec<(ParsedExpr, ParsedExpr, ParsedExpr)>),
    /// Well-founded fixpoint: fix f (x : T) measure m => e
    /// Desugars to a wellFounded_fix application over a Nat measure.
    Fix {
        name: String,
        param: String,
        param_ty: Box<ParsedExpr>,
        measure: Box<ParsedExpr>,
        body: Box<ParsedExpr>,
    },
}

/// Dedicated name-resolution pass.
/// Resolves a raw identifier into an Expr by checking, in order:
/// 1. Bound variables (local lambda/pi binders)
/// 2. Environment bindings (user-defined aliases from env_bindings)
/// 3. Constructor names (bare ctor -> Type.ctor, constructors only)
/// 4. General constant names (bare name -> unique constant match)
/// 5. Exact hierarchical constant name in the environment
/// 6. Fallback: construct a hierarchical Const without verification
fn resolve_name(
    name: &str,
    env_bindings: &HashMap<String, Expr>,
    env: &Environment,
    bound_vars: &[String],
) -> Expr {
    // 1. Bound variables (de Bruijn index = distance from right/end)
    for (i, bv) in bound_vars.iter().enumerate().rev() {
        if bv == name {
            return Expr::mk_bvar((bound_vars.len() - 1 - i) as u64);
        }
    }

    // 2. Environment bindings (exact match)
    if let Some(e) = env_bindings.get(name) {
        return e.clone();
    }

    // 3. Constructor namespace resolution (bare ctor -> Type.ctor)
    if let Some(resolved) = env.resolve_ctor_name(name) {
        return Expr::mk_const(resolved, vec![]);
    }

    // 4. General constant resolution (any kind of constant)
    if !name.contains('.') {
        if let Some(resolved) = env.resolve_constant_name(name) {
            return Expr::mk_const(resolved, vec![]);
        }
    }

    // 5. Exact hierarchical constant name
    let name_parts: Vec<&str> = name.split('.').collect();
    let lean_name = if name_parts.len() == 1 {
        Name::new(name_parts[0])
    } else {
        let mut n = Name::new(name_parts[0]);
        for part in &name_parts[1..] {
            n = n.extend(part);
        }
        n
    };

    if env.find(&lean_name).is_some() {
        return Expr::mk_const(lean_name, vec![]);
    }

    // 6. Fallback
    Expr::mk_const(lean_name, vec![])
}

impl ParsedExpr {
    /// Convert parsed expression to Expr, resolving names via environment.
    /// `env_bindings` maps user-facing names to Expr constants.
    /// `env` is the kernel Environment for looking up constructors/recursors.
    /// `bound_vars` maps local bound variable names to de Bruijn indices.
    pub fn to_expr(&self, env_bindings: &HashMap<String, Expr>, env: &Environment, bound_vars: &mut Vec<String>) -> Expr {
        self.to_expr_with_fn(env_bindings, env, bound_vars, None)
    }

    pub fn to_expr_with_fn(&self, env_bindings: &HashMap<String, Expr>, env: &Environment, bound_vars: &mut Vec<String>, recursive_fn: Option<&str>) -> Expr {
        match self {
            ParsedExpr::BVar(n) => Expr::mk_bvar(*n),
            ParsedExpr::Const(name) => resolve_name(name, env_bindings, env, bound_vars),
            ParsedExpr::NatLit(n) => {
                // Resolve Nat constructors from the environment registry.
                let zero_name = env.get_constructor(&Name::new("Nat"), 0)
                    .unwrap_or_else(|| Name::new("Nat").extend("zero"));
                let succ_name = env.get_constructor(&Name::new("Nat"), 1)
                    .unwrap_or_else(|| Name::new("Nat").extend("succ"));
                let mut result = Expr::mk_const(zero_name, vec![]);
                for _ in 0..*n {
                    result = Expr::mk_app(Expr::mk_const(succ_name.clone(), vec![]), result);
                }
                result
            }
            ParsedExpr::App(f, a) => {
                let f_expr = f.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                let a_expr = a.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                Expr::mk_app(f_expr, a_expr)
            }
            ParsedExpr::Lambda(name, ty, body) => {
                let ty_expr = ty.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                bound_vars.push(name.clone());
                let body_expr = body.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                bound_vars.pop();
                Expr::Lambda(Name::new(name), BinderInfo::Default, Rc::new(ty_expr), Rc::new(body_expr))
            }
            ParsedExpr::Pi(name, ty, body) => {
                let ty_expr = ty.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                bound_vars.push(name.clone());
                let body_expr = body.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                bound_vars.pop();
                Expr::Pi(Name::new(name), BinderInfo::Default, Rc::new(ty_expr), Rc::new(body_expr))
            }
            ParsedExpr::Let(name, ty, val, body) => {
                let ty_expr = ty.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                let val_expr = val.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                bound_vars.push(name.clone());
                let body_expr = body.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                bound_vars.pop();
                Expr::Let(Name::new(name), Rc::new(ty_expr), Rc::new(val_expr), Rc::new(body_expr), false)
            }
            ParsedExpr::Sort(u) => {
                if *u == 0 {
                    Expr::mk_prop()
                } else {
                    Expr::mk_type()
                }
            }
            ParsedExpr::Match(scrutinee, motive, branches) => {
                self.desugar_match(scrutinee, motive, branches, env_bindings, env, bound_vars, recursive_fn)
            }
            ParsedExpr::TacticBlock(_) => {
                panic!("TacticBlock should be handled by the REPL, not converted directly to Expr")
            }
            ParsedExpr::MVar(name) => Expr::mk_mvar(Name::new(name)),
            ParsedExpr::Calc(ty, steps) => {
                if steps.is_empty() {
                    panic!("calc block must have at least one step");
                }
                let ty_expr = ty.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                let first_lhs_parsed = &steps[0].0;
                let mut result = steps[0].2.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                for i in 1..steps.len() {
                    let prev_rhs = steps[i - 1].1.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                    let curr_rhs = steps[i].1.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                    let proof = steps[i].2.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                    // Build P = \y : ty . Eq ty first_lhs y
                    let p_body = ParsedExpr::App(
                        Box::new(ParsedExpr::App(
                            Box::new(ParsedExpr::App(
                                Box::new(ParsedExpr::Const("Eq".to_string())),
                                Box::new((**ty).clone()),
                            )),
                            Box::new(first_lhs_parsed.clone()),
                        )),
                        Box::new(ParsedExpr::Const("y".to_string())),
                    );
                    bound_vars.push("y".to_string());
                    let p_expr = p_body.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
                    bound_vars.pop();
                    let p_lambda = Expr::Lambda(Name::new("y"), BinderInfo::Default, Rc::new(ty_expr.clone()), Rc::new(p_expr));
                    // eq_subst ty prev_rhs curr_rhs P proof result
                    let eq_subst_call = Expr::mk_app(
                        Expr::mk_app(
                            Expr::mk_app(
                                Expr::mk_app(
                                    Expr::mk_app(
                                        Expr::mk_app(
                                            Expr::mk_const(Name::new("eq_subst"), vec![]),
                                            ty_expr.clone(),
                                        ),
                                        prev_rhs,
                                    ),
                                    curr_rhs,
                                ),
                                p_lambda,
                            ),
                            proof,
                        ),
                        result,
                    );
                    result = eq_subst_call;
                }
                result
            }
            ParsedExpr::Fix { name, param, param_ty, measure, body } => {
                self.desugar_fix(name, param, param_ty, measure, body, env_bindings, env, bound_vars, recursive_fn)
            }
        }
    }

    /// Resolve a bare constructor name to its fully-qualified Name.
    /// Delegates to the environment registry.
    fn resolve_ctor_name(bare: &str, _env_bindings: &HashMap<String, Expr>, env: &Environment) -> Option<Name> {
        env.resolve_ctor_name(bare)
    }

    fn desugar_match(&self, scrutinee: &ParsedExpr, motive: &ParsedExpr, branches: &[(ParsedExpr, ParsedExpr)], env_bindings: &HashMap<String, Expr>, env: &Environment, bound_vars: &mut Vec<String>, recursive_fn: Option<&str>) -> Expr {
        // Extract constructor info from first pattern
        let (first_ctor_name, _) = extract_ctor_and_vars(&branches[0].0);
        let mut ctor_name_obj = Name::new(&first_ctor_name);

        // If bare name not found, try namespace resolution via env_bindings
        if env.find(&ctor_name_obj).is_none() {
            if let Some(resolved) = Self::resolve_ctor_name(&first_ctor_name, env_bindings, env) {
                ctor_name_obj = resolved;
            }
        }

        let ctor_info = match env.find(&ctor_name_obj) {
            Some(info) => info,
            None => panic!("Constructor not found in environment: {}", first_ctor_name),
        };
        let ctor_val = match ctor_info.to_constructor_val() {
            Some(v) => v,
            None => panic!("Not a constructor: {}", first_ctor_name),
        };
        let induct_name = ctor_val.induct.clone();

        // Find recursor
        let rec_name = Name::new("rec").extend(&induct_name.to_string());
        let rec_info = match env.find(&rec_name) {
            Some(info) => info,
            None => panic!("Recursor not found: {}", rec_name.to_string()),
        };
        let _rec_val = match rec_info.to_recursor_val() {
            Some(v) => v,
            None => panic!("Not a recursor: {}", rec_name.to_string()),
        };

        // Get all constructor names in order
        let ind_info = match env.find(&induct_name) {
            Some(info) => info,
            None => panic!("Inductive type not found: {}", induct_name.to_string()),
        };
        let ind_val = match ind_info.to_inductive_val() {
            Some(v) => v,
            None => panic!("Not an inductive type: {}", induct_name.to_string()),
        };
        let all_ctors = ind_val.ctors.clone();

        // Build motive lambda: λ (_m : induct_ty) . motive_expr
        let induct_ty_expr = Expr::mk_const(induct_name.clone(), vec![]);
        let motive_expr = motive.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
        let motive_lambda = Expr::Lambda(
            Name::new("_m"), BinderInfo::Default,
            Rc::new(induct_ty_expr),
            Rc::new(motive_expr.clone()),
        );

        // Build minors for each constructor
        let mut minors = Vec::new();
        for ctor_name in &all_ctors {
            let ctor_name_str = ctor_name.to_string();
            let branch = branches.iter()
                .find(|(pat, _)| {
                    let (c, _) = extract_ctor_and_vars(pat);
                    if c == ctor_name_str {
                        return true;
                    }
                    // Namespace resolution: resolve bare pattern name
                    if let Some(resolved) = Self::resolve_ctor_name(&c, env_bindings, env) {
                        return resolved.to_string() == ctor_name_str;
                    }
                    false
                })
                .unwrap_or_else(|| panic!("Missing branch for constructor: {}", ctor_name_str));

            let (_, vars) = extract_ctor_and_vars(&branch.0);
            let param_types = get_ctor_param_types(env, ctor_name);
            let k = vars.len();
            let r = param_types.iter().filter(|pt| expr_contains_const(pt, &induct_name)).count();

            // Compute mapping from recursive param index to (pattern_bvar, ih_bvar) in final minor body
            let mut recursive_pairs = Vec::new();
            for p in 0..k {
                if expr_contains_const(&param_types[p], &induct_name) {
                    let pattern_bvar = (r + k - 1 - p) as u64;
                    let ih_bvar = param_types[p+1..].iter().filter(|pt| expr_contains_const(pt, &induct_name)).count() as u64;
                    recursive_pairs.push((pattern_bvar, ih_bvar));
                }
            }

            // Bind pattern variables
            let _external_bound_count = bound_vars.len();
            for var in &vars {
                bound_vars.push(var.clone());
            }
            let mut body_expr = branch.1.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
            for _ in &vars {
                bound_vars.pop();
            }

            let num_ih = param_types.iter().filter(|pt| expr_contains_const(pt, &induct_name)).count();
            let total_lambdas = vars.len() + num_ih;

            // Lift all BVars to make room for the lambda wrappers we are about to add.
            body_expr = body_expr.lift_loose_bvars(total_lambdas as u64, 0);

            // Replace pattern-variable BVars (which now point past the lambdas) with references
            // to the corresponding lambda parameters.
            for (i, _var) in vars.iter().enumerate() {
                // The variable's de Bruijn index before lifting is (vars.len() - 1 - i).
                // After lifting by total_lambdas, its index becomes:
                let old_idx = (vars.len() - 1 - i) as u64 + total_lambdas as u64;
                let new_idx = (num_ih + vars.len() - 1 - i) as u64;
                body_expr = replace_bvar(&body_expr, old_idx, new_idx, 0);
            }

            let mut minor = body_expr;

            // For constructors with recursive fields, add ih lambdas BEFORE pattern variable lambdas.
            // ih is innermost because it binds over the branch body, while pattern variables
            // bind over both the body and ih.
            for param_ty in param_types.iter().rev() {
                if expr_contains_const(param_ty, &induct_name) {
                    let ih_ty = motive_expr.clone();
                    minor = Expr::Lambda(Name::new("ih"), BinderInfo::Default, Rc::new(ih_ty), Rc::new(minor));
                }
            }

            // Wrap with lambdas for pattern variables (in reverse order)
            for (i, var) in vars.iter().enumerate().rev() {
                let ty = if i < param_types.len() {
                    param_types[i].clone()
                } else {
                    Expr::mk_type() // fallback
                };
                minor = Expr::Lambda(Name::new(var), BinderInfo::Default, Rc::new(ty), Rc::new(minor));
            }

            // Replace recursive calls with ih variables in the minor premise body
            if let Some(fn_name) = recursive_fn {
                if !recursive_pairs.is_empty() {
                    minor = replace_recursive_calls(&minor, fn_name, &recursive_pairs);
                }
            }

            minors.push(minor);
        }

        // Build recursor application: rec motive minor_0 minor_1 ... scrutinee
        let mut app = Expr::mk_const(rec_name, vec![]);
        app = Expr::mk_app(app, motive_lambda);
        for minor in minors {
            app = Expr::mk_app(app, minor);
        }
        let scrut_expr = scrutinee.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
        Expr::mk_app(app, scrut_expr)
    }

    fn desugar_fix(
        &self,
        name: &str,
        param: &str,
        param_ty: &ParsedExpr,
        measure: &ParsedExpr,
        body: &ParsedExpr,
        env_bindings: &HashMap<String, Expr>,
        env: &Environment,
        bound_vars: &mut Vec<String>,
        recursive_fn: Option<&str>,
    ) -> Expr {
        let existing_pos = bound_vars.iter().rposition(|v| v == param);

        let a_expr = param_ty.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);
        let m_expr = measure.to_expr_with_fn(env_bindings, env, bound_vars, recursive_fn);

        let c_mvar = Expr::mk_mvar(Name::new(&format!("_fix_C_{}", name)));

        let lt_const = Expr::mk_const(Name::new("lt"), vec![]);

        // R = fun y => fun x => lt (m y) (m x)
        let r_expr = Expr::mk_lambda(
            Name::new("y"),
            a_expr.clone(),
            Expr::mk_lambda(
                Name::new("x"),
                a_expr.clone(),
                Expr::mk_app(
                    Expr::mk_app(
                        lt_const.clone(),
                        Expr::mk_app(m_expr.clone(), Expr::mk_bvar(1)),
                    ),
                    Expr::mk_app(m_expr.clone(), Expr::mk_bvar(0)),
                ),
            ),
        );

        // Push param binder if it is not already bound in the outer context
        let pushed_param = if existing_pos.is_none() {
            bound_vars.push(param.to_string());
            true
        } else {
            false
        };

        // Push the recursive-step binder
        let rec_name = format!("_fix_rec_{}", name);
        bound_vars.push(rec_name);

        // Translate the body. Recursive calls to `name` inside nested match
        // expressions are handled by match desugaring; remaining calls are
        // replaced by applications of the step binder below.
        let mut body_expr = body.to_expr_with_fn(env_bindings, env, bound_vars, Some(name));

        // Pop the recursive binder
        bound_vars.pop();

        // Determine de Bruijn indices of rec and the fix parameter inside body_expr.
        // rec was the innermost binder, so it is always BVar(0).
        let rec_bvar_body = 0u64;
        let param_bvar_body = if pushed_param {
            1u64
        } else {
            (bound_vars.len() - existing_pos.unwrap()) as u64
        };

        body_expr = replace_fix_rec_calls(&body_expr, name, rec_bvar_body, param_bvar_body, &m_expr);

        if pushed_param {
            bound_vars.pop();
        }

        // Build the type of the recursive-step binder.
        // It lives in the context after popping the rec binder (and the param binder if we pushed it).
        let param_bvar_rec_ty = if pushed_param {
            0u64
        } else {
            (bound_vars.len() - 1 - existing_pos.unwrap()) as u64
        };

        let rec_ty = Expr::mk_pi(
            Name::new("y"),
            a_expr.clone(),
            Expr::mk_pi(
                Name::new("_"),
                Expr::mk_app(
                    Expr::mk_app(
                        lt_const.clone(),
                        Expr::mk_app(m_expr.clone(), Expr::mk_bvar(1)),
                    ),
                    Expr::mk_app(m_expr.clone(), Expr::mk_bvar(param_bvar_rec_ty + 2)),
                ),
                Expr::mk_app(c_mvar.clone(), Expr::mk_bvar(1)),
            ),
        );

        // Build the step function F
        let f_expr = if pushed_param {
            Expr::mk_lambda(
                Name::new(param),
                a_expr.clone(),
                Expr::mk_lambda(
                    Name::new(&format!("_rec_{}", name)),
                    rec_ty,
                    body_expr,
                ),
            )
        } else {
            Expr::mk_lambda(
                Name::new(&format!("_rec_{}", name)),
                rec_ty,
                body_expr,
            )
        };

        // wf = wellFounded_measure A m
        let wf_expr = Expr::mk_app(
            Expr::mk_app(Expr::mk_const(Name::new("wellFounded_measure"), vec![]), a_expr.clone()),
            m_expr.clone(),
        );

        // Inner application: wellFounded_fix A C R wf F x
        let fix_app = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(
                        Expr::mk_app(
                            Expr::mk_app(
                                Expr::mk_const(Name::new("wellFounded_fix"), vec![]),
                                a_expr.clone(),
                            ),
                            c_mvar,
                        ),
                        r_expr,
                    ),
                    wf_expr,
                ),
                f_expr,
            ),
            Expr::mk_bvar(param_bvar_rec_ty),
        );

        if pushed_param {
            Expr::mk_lambda(Name::new(param), a_expr, fix_app)
        } else {
            fix_app
        }
    }
}

/// Extract constructor name and bound variable names from a pattern.
/// e.g., `zero` -> ("zero", []), `succ n` -> ("succ", ["n"]), `ofNat m` -> ("ofNat", ["m"])
fn extract_ctor_and_vars(pat: &ParsedExpr) -> (String, Vec<String>) {
    match pat {
        ParsedExpr::Const(name) => (name.clone(), vec![]),
        ParsedExpr::App(f, a) => {
            let (ctor, mut vars) = extract_ctor_and_vars(f);
            match a.as_ref() {
                ParsedExpr::Const(var) => vars.push(var.clone()),
                _ => panic!("Pattern must be a constructor applied to variables, got {:?}", a),
            }
            (ctor, vars)
        }
        _ => panic!("Invalid pattern: {:?}", pat),
    }
}

/// Get the parameter types of a constructor from the environment.
fn get_ctor_param_types(env: &Environment, ctor_name: &Name) -> Vec<Expr> {
    let ctor_info = env.find(ctor_name).expect("Constructor not found");
    let ctor_val = ctor_info.to_constructor_val().expect("Not a constructor");
    let mut domains = Vec::new();
    let mut current = &ctor_val.constant_val.ty;
    while let Expr::Pi(_, _, domain, body) = current {
        domains.push((**domain).clone());
        current = body;
    }
    domains
}

/// Check if an expression contains a reference to a given constant name.
fn expr_contains_const(e: &Expr, name: &Name) -> bool {
    match e {
        Expr::Const(n, _) => n == name,
        Expr::App(f, a) => expr_contains_const(f, name) || expr_contains_const(a, name),
        Expr::Lambda(_, _, ty, body) => expr_contains_const(ty, name) || expr_contains_const(body, name),
        Expr::Pi(_, _, ty, body) => expr_contains_const(ty, name) || expr_contains_const(body, name),
        Expr::Let(_, ty, val, body, _) => expr_contains_const(ty, name) || expr_contains_const(val, name) || expr_contains_const(body, name),
        Expr::Proj(_, _, e) => expr_contains_const(e, name),
        Expr::MData(_, e) => expr_contains_const(e, name),
        _ => false,
    }
}

/// Flatten an application chain into (head, args).
fn flatten_app<'a>(expr: &'a Expr) -> (&'a Expr, Vec<&'a Expr>) {
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(f, a) = head {
        args.push(a.as_ref());
        head = f.as_ref();
    }
    args.reverse();
    (head, args)
}

/// Rebuild an application chain from head and args.
fn rebuild_app(head: Expr, args: Vec<Expr>) -> Expr {
    let mut result = head;
    for arg in args {
        result = Expr::mk_app(result, arg);
    }
    result
}

/// Replace all occurrences of a specific BVar index with another, respecting binder depth.
fn replace_bvar(expr: &Expr, from: u64, to: u64, depth: u64) -> Expr {
    match expr {
        Expr::BVar(i) => {
            if *i == from + depth {
                Expr::mk_bvar(to + depth)
            } else {
                expr.clone()
            }
        }
        Expr::App(f, a) => Expr::App(
            Rc::new(replace_bvar(f, from, to, depth)),
            Rc::new(replace_bvar(a, from, to, depth)),
        ),
        Expr::Lambda(name, bi, ty, body) => Expr::Lambda(
            name.clone(),
            *bi,
            Rc::new(replace_bvar(ty, from, to, depth)),
            Rc::new(replace_bvar(body, from, to, depth + 1)),
        ),
        Expr::Pi(name, bi, ty, body) => Expr::Pi(
            name.clone(),
            *bi,
            Rc::new(replace_bvar(ty, from, to, depth)),
            Rc::new(replace_bvar(body, from, to, depth + 1)),
        ),
        Expr::Let(name, ty, value, body, nondep) => Expr::Let(
            name.clone(),
            Rc::new(replace_bvar(ty, from, to, depth)),
            Rc::new(replace_bvar(value, from, to, depth)),
            Rc::new(replace_bvar(body, from, to, depth + 1)),
            *nondep,
        ),
        Expr::MData(d, e) => Expr::MData(d.clone(), Rc::new(replace_bvar(e, from, to, depth))),
        Expr::Proj(s, i, e) => Expr::Proj(s.clone(), *i, Rc::new(replace_bvar(e, from, to, depth))),
        _ => expr.clone(),
    }
}

/// Replace recursive function calls with ih variables in a minor premise.
/// `recursive_pairs` is a list of (pattern_bvar, ih_bvar) for each recursive field.
/// The minor premise includes the lambda wrappers for pattern variables and ih.
/// BVar indices in the minor body are already correct (pattern variables reference
/// their lambda parameters), so no depth offset is needed at the top level.
fn replace_recursive_calls(expr: &Expr, fn_name: &str, recursive_pairs: &[(u64, u64)]) -> Expr {
    replace_recursive_calls_core(expr, fn_name, recursive_pairs, 0)
}

fn replace_recursive_calls_core(expr: &Expr, fn_name: &str, recursive_pairs: &[(u64, u64)], depth: u64) -> Expr {
    match expr {
        Expr::App(_, _) => {
            let (head, args) = flatten_app(expr);
            if let Expr::Const(name, _) = head {
                if name.to_string() == fn_name {
                    for arg in &args {
                        if let Expr::BVar(bv) = arg {
                            for (pattern_bvar, ih_bvar) in recursive_pairs {
                                if *bv == *pattern_bvar + depth {
                                    return Expr::mk_bvar(*ih_bvar + depth);
                                }
                            }
                        }
                    }
                }
            }
            let new_head = replace_recursive_calls_core(head, fn_name, recursive_pairs, depth);
            let new_args: Vec<Expr> = args.iter()
                .map(|a| replace_recursive_calls_core(a, fn_name, recursive_pairs, depth))
                .collect();
            rebuild_app(new_head, new_args)
        }
        Expr::Lambda(name, bi, ty, body) => {
            Expr::Lambda(
                name.clone(),
                *bi,
                Rc::new(replace_recursive_calls_core(ty, fn_name, recursive_pairs, depth)),
                Rc::new(replace_recursive_calls_core(body, fn_name, recursive_pairs, depth + 1)),
            )
        }
        Expr::Pi(name, bi, ty, body) => {
            Expr::Pi(
                name.clone(),
                *bi,
                Rc::new(replace_recursive_calls_core(ty, fn_name, recursive_pairs, depth)),
                Rc::new(replace_recursive_calls_core(body, fn_name, recursive_pairs, depth + 1)),
            )
        }
        Expr::Let(name, ty, value, body, nondep) => {
            Expr::Let(
                name.clone(),
                Rc::new(replace_recursive_calls_core(ty, fn_name, recursive_pairs, depth)),
                Rc::new(replace_recursive_calls_core(value, fn_name, recursive_pairs, depth)),
                Rc::new(replace_recursive_calls_core(body, fn_name, recursive_pairs, depth + 1)),
                *nondep,
            )
        }
        Expr::MData(d, e) => {
            Expr::MData(d.clone(), Rc::new(replace_recursive_calls_core(e, fn_name, recursive_pairs, depth)))
        }
        Expr::Proj(s, i, e) => {
            Expr::Proj(s.clone(), *i, Rc::new(replace_recursive_calls_core(e, fn_name, recursive_pairs, depth)))
        }
        _ => expr.clone(),
    }
}

/// Replace remaining recursive function calls inside a `fix` body with applications
/// of the well-founded step binder. Each call `f a` becomes `rec a proof`, where
/// `proof` is a real termination proof when we can synthesize one.
fn replace_fix_rec_calls(
    expr: &Expr,
    fn_name: &str,
    rec_bvar: u64,
    x_bvar: u64,
    measure: &Expr,
) -> Expr {
    let lt_const = Expr::mk_const(Name::new("lt"), vec![]);
    let sorry_const = Expr::mk_const(Name::new("sorry_prop"), vec![]);
    replace_fix_rec_calls_core(expr, fn_name, rec_bvar, x_bvar, measure, &lt_const, &sorry_const)
}

/// Try to synthesize a real termination proof `lt (m rec_arg) (m x)`.
/// Currently supports the common pattern where the measure is `list_length A`
/// and the recursive argument is `list_filter A p tail`.
fn try_mk_termination_proof(rec_arg: &Expr, measure: &Expr) -> Option<Expr> {
    // Recognize measure = list_length A
    let (measure_head, measure_args) = flatten_app(measure);
    if let Expr::Const(name, _) = measure_head {
        if name.to_string() != "list_length" {
            return None;
        }
    } else {
        return None;
    }
    if measure_args.len() != 1 {
        return None;
    }
    let a_expr = measure_args[0].clone();

    // Recognize rec_arg = list_filter A p tail
    let (arg_head, arg_args) = flatten_app(rec_arg);
    if let Expr::Const(name, _) = arg_head {
        if name.to_string() != "list_filter" {
            return None;
        }
    } else {
        return None;
    }
    if arg_args.len() != 3 {
        return None;
    }
    let filter_a = arg_args[0];
    let filter_p = arg_args[1].clone();
    let filter_tail = arg_args[2].clone();

    if &a_expr != filter_a {
        return None;
    }

    let list_length = Expr::mk_const(Name::new("list_length"), vec![]);
    let list_filter = Expr::mk_const(Name::new("list_filter"), vec![]);
    let list_filter_length_le = Expr::mk_const(Name::new("list_filter_length_le"), vec![]);
    let le_succ = Expr::mk_const(Name::new("le_succ"), vec![]);

    let len_filter_tail = Expr::mk_app(
        Expr::mk_app(list_length.clone(), a_expr.clone()),
        Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(list_filter.clone(), a_expr.clone()),
                filter_p.clone(),
            ),
            filter_tail.clone(),
        ),
    );

    let len_tail = Expr::mk_app(
        Expr::mk_app(list_length.clone(), a_expr.clone()),
        filter_tail.clone(),
    );

    let filter_le = Expr::mk_app(
        Expr::mk_app(
            Expr::mk_app(list_filter_length_le, a_expr.clone()),
            filter_p.clone(),
        ),
        filter_tail.clone(),
    );

    Some(Expr::mk_app(
        Expr::mk_app(Expr::mk_app(le_succ, len_filter_tail), len_tail),
        filter_le,
    ))
}

fn replace_fix_rec_calls_core(
    expr: &Expr,
    fn_name: &str,
    rec_bvar: u64,
    x_bvar: u64,
    measure: &Expr,
    lt_const: &Expr,
    sorry_const: &Expr,
) -> Expr {
    match expr {
        Expr::App(_, _) => {
            let (head, args) = flatten_app(expr);
            if let Expr::Const(name, _) = head {
                if name.to_string() == fn_name && !args.is_empty() {
                    let rec_arg = replace_fix_rec_calls_core(
                        args[0], fn_name, rec_bvar, x_bvar, measure, lt_const, sorry_const
                    );
                    let proof = try_mk_termination_proof(&rec_arg, measure)
                        .unwrap_or_else(|| {
                            Expr::mk_app(
                                sorry_const.clone(),
                                Expr::mk_app(
                                    Expr::mk_app(
                                        lt_const.clone(),
                                        Expr::mk_app(measure.clone(), rec_arg.clone()),
                                    ),
                                    Expr::mk_app(measure.clone(), Expr::mk_bvar(x_bvar)),
                                ),
                            )
                        });
                    let mut result = Expr::mk_app(Expr::mk_bvar(rec_bvar), rec_arg);
                    result = Expr::mk_app(result, proof);
                    for arg in &args[1..] {
                        let new_arg = replace_fix_rec_calls_core(
                            arg, fn_name, rec_bvar, x_bvar, measure, lt_const, sorry_const
                        );
                        result = Expr::mk_app(result, new_arg);
                    }
                    return result;
                }
            }
            let new_head = replace_fix_rec_calls_core(
                head, fn_name, rec_bvar, x_bvar, measure, lt_const, sorry_const
            );
            let new_args: Vec<Expr> = args.iter()
                .map(|a| replace_fix_rec_calls_core(
                    a, fn_name, rec_bvar, x_bvar, measure, lt_const, sorry_const
                ))
                .collect();
            rebuild_app(new_head, new_args)
        }
        Expr::Lambda(name, bi, ty, body) => {
            Expr::Lambda(
                name.clone(),
                *bi,
                Rc::new(replace_fix_rec_calls_core(ty, fn_name, rec_bvar, x_bvar, measure, lt_const, sorry_const)),
                Rc::new(replace_fix_rec_calls_core(body, fn_name, rec_bvar + 1, x_bvar + 1, measure, lt_const, sorry_const)),
            )
        }
        Expr::Pi(name, bi, ty, body) => {
            Expr::Pi(
                name.clone(),
                *bi,
                Rc::new(replace_fix_rec_calls_core(ty, fn_name, rec_bvar, x_bvar, measure, lt_const, sorry_const)),
                Rc::new(replace_fix_rec_calls_core(body, fn_name, rec_bvar + 1, x_bvar + 1, measure, lt_const, sorry_const)),
            )
        }
        Expr::Let(name, ty, value, body, nondep) => {
            Expr::Let(
                name.clone(),
                Rc::new(replace_fix_rec_calls_core(ty, fn_name, rec_bvar, x_bvar, measure, lt_const, sorry_const)),
                Rc::new(replace_fix_rec_calls_core(value, fn_name, rec_bvar, x_bvar, measure, lt_const, sorry_const)),
                Rc::new(replace_fix_rec_calls_core(body, fn_name, rec_bvar + 1, x_bvar + 1, measure, lt_const, sorry_const)),
                *nondep,
            )
        }
        Expr::MData(d, e) => {
            Expr::MData(d.clone(), Rc::new(replace_fix_rec_calls_core(e, fn_name, rec_bvar, x_bvar, measure, lt_const, sorry_const)))
        }
        Expr::Proj(s, i, e) => {
            Expr::Proj(s.clone(), *i, Rc::new(replace_fix_rec_calls_core(e, fn_name, rec_bvar, x_bvar, measure, lt_const, sorry_const)))
        }
        _ => expr.clone(),
    }
}

/// A parsed top-level declaration.
#[derive(Debug, Clone)]
pub enum ParsedDecl {
    Def {
        name: String,
        params: Vec<(String, ParsedExpr)>, // (param_name, param_type)
        ret_ty: Option<ParsedExpr>,
        value: ParsedExpr,
    },
    Theorem {
        name: String,
        params: Vec<(String, ParsedExpr)>,
        ret_ty: ParsedExpr,
        value: ParsedExpr,
    },
    Inductive {
        name: String,
        ty: ParsedExpr,
        ctors: Vec<(String, ParsedExpr)>,
        num_params: usize,
    },
    Axiom {
        name: String,
        ty: ParsedExpr,
    },
    /// Structure declaration: desugars to inductive + projections
    Structure {
        name: String,
        ty: ParsedExpr,
        fields: Vec<(String, ParsedExpr)>,
    },
    /// Mutual inductive block: multiple inductive types that can reference each other
    MutualInductive {
        types: Vec<(String, ParsedExpr, Vec<(String, ParsedExpr)>, usize)>,
        // (name, ty, ctors, num_params)
    },
    /// Solve declaration: like theorem but allows unassigned metavariables (solve variables)
    Solve {
        name: String,
        params: Vec<(String, ParsedExpr)>,
        ret_ty: ParsedExpr,
        value: ParsedExpr,
    },
    /// Variable declaration: parameters that are implicitly added to all subsequent defs/theorems
    Variable {
        params: Vec<(String, ParsedExpr)>,
    },
    /// Infix operator declaration: infix "+" => add
    Infix {
        symbol: String,
        func_name: String,
        precedence: i32,
        left_assoc: bool,
    },
    /// Section declaration: opens a new scope for variables and notations
    Section {
        name: Option<String>,
    },
    /// End declaration: closes the current section
    End {
        name: Option<String>,
    },
    /// Import declaration: import another .cic file
    Import {
        path: String,
    },
    /// Notation declaration: notation "symbol" => expr
    Notation {
        symbol: String,
        expansion: ParsedExpr,
    },
}

#[derive(Debug, Clone)]
pub struct Parser {
    input: Vec<char>,
    pos: usize,
    /// User-defined infix operators: symbol -> (precedence, function_name, left_assoc)
    infix_ops: HashMap<String, (i32, String, bool)>,
    /// User-defined notations: symbol -> expansion expression
    notations: HashMap<String, ParsedExpr>,
}

impl Parser {
    pub fn new(input: &str) -> Self {
        Parser {
            input: input.chars().collect(),
            pos: 0,
            infix_ops: HashMap::new(),
            notations: HashMap::new(),
        }
    }

    pub fn new_with_infix_ops(input: &str, infix_ops: HashMap<String, (i32, String, bool)>) -> Self {
        Parser {
            input: input.chars().collect(),
            pos: 0,
            infix_ops,
            notations: HashMap::new(),
        }
    }

    pub fn new_with_state(input: &str, infix_ops: HashMap<String, (i32, String, bool)>, notations: HashMap<String, ParsedExpr>) -> Self {
        Parser {
            input: input.chars().collect(),
            pos: 0,
            infix_ops,
            notations,
        }
    }

    /// Parse a single expression.
    /// Find the start position of the current line (position after last '\n' or 0)
    fn line_start(&self, pos: usize) -> usize {
        let mut i = pos;
        while i > 0 {
            i -= 1;
            if self.input.get(i) == Some(&'\n') {
                return i + 1;
            }
        }
        0
    }

    /// Column of the current position (0-based, measured as chars from line start).
    fn current_col(&self) -> usize {
        self.pos - self.line_start(self.pos)
    }

    /// Line number of the current position (1-based).
    fn current_line(&self) -> usize {
        let mut line = 1;
        for i in 0..self.pos {
            if self.input.get(i) == Some(&'\n') {
                line += 1;
            }
        }
        line
    }

    /// Skip whitespace and comments starting from `pos` without mutating the
    /// parser or cloning the input. Returns the first position that is neither
    /// whitespace nor inside a comment.
    fn skip_ws_and_comments_at(&self, mut pos: usize) -> usize {
        loop {
            while pos < self.input.len() && self.input[pos].is_whitespace() {
                pos += 1;
            }
            // Skip line comments: -- ...\n
            if pos + 1 < self.input.len()
                && self.input[pos] == '-'
                && self.input[pos + 1] == '-'
            {
                while pos < self.input.len() && self.input[pos] != '\n' {
                    pos += 1;
                }
                continue;
            }
            // Skip block comments: /- ... -/ (nested)
            if pos + 1 < self.input.len()
                && self.input[pos] == '/'
                && self.input[pos + 1] == '-'
            {
                pos += 2;
                let mut depth = 1;
                while depth > 0 && pos + 1 < self.input.len() {
                    if self.input[pos] == '/' && self.input[pos + 1] == '-' {
                        pos += 2;
                        depth += 1;
                    } else if self.input[pos] == '-' && self.input[pos + 1] == '/' {
                        pos += 2;
                        depth -= 1;
                    } else {
                        pos += 1;
                    }
                }
                continue;
            }
            break;
        }
        pos
    }

    /// Peek the column of the next non-whitespace, non-comment token without
    /// advancing the parser. Returns (column, keyword_if_any).
    fn peek_next_token_col(&self) -> (usize, Option<&'static str>) {
        let pos = self.skip_ws_and_comments_at(self.pos);
        let col = pos - self.line_start(pos);
        let kw = ["def", "theorem", "solve", "inductive", "structure", "axiom",
                  "intro", "intros", "exact", "apply", "refl", "reflexivity", "rfl",
                  "assumption", "rewrite", "rw", "induction", "cases", "have", "exists",
                  "import"]
            .iter()
            .find(|kw| {
                let kw_chars: Vec<char> = kw.chars().collect();
                if pos + kw_chars.len() > self.input.len() {
                    return false;
                }
                for (i, kc) in kw_chars.iter().enumerate() {
                    if self.input[pos + i] != *kc {
                        return false;
                    }
                }
                // Make sure it's not a prefix of a longer identifier
                if let Some(&c) = self.input.get(pos + kw_chars.len()) {
                    if c.is_alphanumeric() || c == '_' || c == '\'' {
                        return false;
                    }
                }
                true
            })
            .copied();
        (col, kw)
    }

    pub fn parse_expr(&mut self) -> Result<ParsedExpr, String> {
        self.parse_pi_or_arrow()
    }

    /// Parse a file into a list of declarations.
    pub fn parse_file(&mut self) -> Result<Vec<ParsedDecl>, String> {
        let mut decls = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek().is_none() {
                break;
            }
            let decl = self.parse_decl().map_err(|e| {
                format!("line {} col {}: {}", self.current_line(), self.current_col(), e)
            })?;
            decls.push(decl);
        }
        Ok(decls)
    }

    fn skip_whitespace_and_comments(&mut self) {
        self.skip_whitespace();
    }

    pub fn parse_decl(&mut self) -> Result<ParsedDecl, String> {
        self.skip_whitespace_and_comments();
        if self.starts_with_keyword("def") {
            self.parse_def_decl()
        } else if self.starts_with_keyword("theorem") {
            self.parse_theorem_decl()
        } else if self.starts_with_keyword("inductive") {
            self.parse_inductive_decl()
        } else if self.starts_with_keyword("structure") {
            self.parse_structure_decl()
        } else if self.starts_with_keyword("axiom") {
            self.parse_axiom_decl()
        } else if self.starts_with_keyword("mutual") {
            self.parse_mutual_inductive_decl()
        } else if self.starts_with_keyword("solve") {
            self.parse_solve_decl()
        } else if self.starts_with_keyword("variable") {
            self.parse_variable_decl()
        } else if self.starts_with_keyword("notation") {
            self.parse_notation_decl()
        } else if self.starts_with_keyword("infixl") {
            self.parse_infix_decl(true)
        } else if self.starts_with_keyword("infix") {
            self.parse_infix_decl(false)
        } else if self.starts_with_keyword("section") {
            self.parse_section_decl()
        } else if self.starts_with_keyword("end") {
            self.parse_end_decl()
        } else if self.starts_with_keyword("import") {
            self.parse_import_decl()
        } else {
            Err(format!("Expected declaration, got {:?}", self.peek()))
        }
    }

    fn parse_def_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(3); // consume "def"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let (params, ret_ty, value) = self.parse_decl_body()?;
        Ok(ParsedDecl::Def { name, params, ret_ty, value })
    }

    fn parse_theorem_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(7); // consume "theorem"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let (params, ret_ty, value) = self.parse_decl_body()?;
        let ret_ty = ret_ty.ok_or("Theorem must have an explicit return type".to_string())?;
        Ok(ParsedDecl::Theorem { name, params, ret_ty, value })
    }

    fn parse_solve_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(5); // consume "solve"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let (params, ret_ty, value) = self.parse_decl_body()?;
        let ret_ty = ret_ty.ok_or("Solve must have an explicit return type".to_string())?;
        Ok(ParsedDecl::Solve { name, params, ret_ty, value })
    }

    fn parse_variable_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(8); // consume "variable"
        self.skip_whitespace();

        let mut params = Vec::new();
        while self.peek() == Some('(') || self.peek() == Some('{') {
            let implicit = self.peek() == Some('{');
            self.advance();
            let mut names = vec![self.parse_ident_raw()?];
            self.skip_whitespace();
            while self.peek() != Some(':') {
                names.push(self.parse_ident_raw()?);
                self.skip_whitespace();
            }
            self.advance(); // consume ':'
            let pty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            let close = if implicit { '}' } else { ')' };
            if self.peek() != Some(close) {
                return Err(format!("Expected '{}'", close));
            }
            self.advance();
            for name in names {
                params.push((name, pty.clone()));
            }
            self.skip_whitespace();
        }

        if params.is_empty() {
            return Err("variable declaration must have at least one parameter".to_string());
        }

        Ok(ParsedDecl::Variable { params })
    }

    fn parse_infix_decl(&mut self, left_assoc: bool) -> Result<ParsedDecl, String> {
        let kw_len = if left_assoc { 6 } else { 5 }; // "infixl" or "infix"
        self.advance_by(kw_len);
        self.skip_whitespace();

        // Parse operator symbol (quoted string)
        let symbol = if self.peek() == Some('"') {
            self.advance(); // consume '"'
            let mut s = String::new();
            while let Some(c) = self.peek() {
                if c == '"' {
                    self.advance();
                    break;
                }
                s.push(c);
                self.advance();
            }
            s
        } else {
            // Also allow bare symbols like +, -, <=
            let mut s = String::new();
            while let Some(c) = self.peek() {
                if c.is_whitespace() || c == '=' || c == '>' || c == '(' || c == ')' || c == '{' || c == '}' {
                    break;
                }
                s.push(c);
                self.advance();
            }
            s
        };

        if symbol.is_empty() {
            return Err("Expected operator symbol after infix".to_string());
        }

        self.skip_whitespace();

        // Optional precedence: infix "+" 6 => add
        let precedence = if let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                let mut prec_str = String::new();
                while let Some(d) = self.peek() {
                    if d.is_ascii_digit() {
                        prec_str.push(d);
                        self.advance();
                    } else {
                        break;
                    }
                }
                prec_str.parse().unwrap_or(6)
            } else {
                6
            }
        } else {
            6
        };

        self.skip_whitespace();

        // Expect "=>" followed by function name
        if !self.starts_with_keyword("=>") {
            return Err("Expected '=>' after infix operator symbol".to_string());
        }
        self.advance_by(2);
        self.skip_whitespace();

        let func_name = self.parse_ident_raw()?;

        // Register in parser so subsequent expressions can use it
        self.infix_ops.insert(symbol.clone(), (precedence, func_name.clone(), left_assoc));

        Ok(ParsedDecl::Infix { symbol, func_name, precedence, left_assoc })
    }

    fn parse_notation_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(8); // consume "notation"
        self.skip_whitespace();

        // Parse notation symbol (quoted string)
        let symbol = if self.peek() == Some('"') {
            self.advance(); // consume '"'
            let mut s = String::new();
            while let Some(c) = self.peek() {
                if c == '"' {
                    self.advance();
                    break;
                }
                s.push(c);
                self.advance();
            }
            s
        } else {
            return Err("Expected quoted string after notation".to_string());
        };

        if symbol.is_empty() {
            return Err("Empty notation symbol".to_string());
        }

        self.skip_whitespace();

        // Expect "=>" followed by expansion expression
        if !self.starts_with_keyword("=>") {
            return Err("Expected '=>' after notation symbol".to_string());
        }
        self.advance_by(2);
        self.skip_whitespace();

        let expansion = self.parse_expr()?;

        // Register notation in parser
        self.notations.insert(symbol.clone(), expansion.clone());

        Ok(ParsedDecl::Notation { symbol, expansion })
    }

    fn parse_section_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(7); // consume "section"
        self.skip_whitespace();

        // Optional section name
        let name = if self.peek().map_or(false, |c| c.is_alphabetic() || c == '_') {
            Some(self.parse_ident_raw()?)
        } else {
            None
        };

        Ok(ParsedDecl::Section { name })
    }

    fn parse_end_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(3); // consume "end"
        self.skip_whitespace();

        // Optional section name
        let name = if self.peek().map_or(false, |c| c.is_alphabetic() || c == '_') {
            Some(self.parse_ident_raw()?)
        } else {
            None
        };

        Ok(ParsedDecl::End { name })
    }

    fn parse_import_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(6); // consume "import"
        self.skip_whitespace();

        let path = self.parse_ident_raw()?;

        Ok(ParsedDecl::Import { path })
    }

    fn parse_axiom_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(5); // consume "axiom"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        if self.peek() != Some(':') {
            return Err("Expected ':' after axiom name".to_string());
        }
        self.advance();
        let ty = self.parse_pi_or_arrow()?;
        Ok(ParsedDecl::Axiom { name, ty })
    }

    /// Parse the common body of def/theorem: params [: ret_ty] := value
    fn parse_decl_body(&mut self) -> Result<(Vec<(String, ParsedExpr)>, Option<ParsedExpr>, ParsedExpr), String> {
        // Parse optional parameters: (x : T) or {x : T}, also (x y : T)
        let mut params = Vec::new();
        while self.peek() == Some('(') || self.peek() == Some('{') {
            let implicit = self.peek() == Some('{');
            self.advance(); // consume '(' or '{'
            let mut names = vec![self.parse_ident_raw()?];
            self.skip_whitespace();
            while self.peek() != Some(':') {
                names.push(self.parse_ident_raw()?);
                self.skip_whitespace();
            }
            self.advance(); // consume ':'
            let pty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            let close = if implicit { '}' } else { ')' };
            if self.peek() != Some(close) {
                return Err(format!("Expected '{}'", close));
            }
            self.advance();
            for name in names {
                params.push((name, pty.clone()));
            }
            self.skip_whitespace();
        }

        // Optional return type (distinguish ':' from ':=')
        let ret_ty = if self.peek() == Some(':') && self.input.get(self.pos + 1) != Some(&'=') {
            self.advance();
            Some(self.parse_pi_or_arrow()?)
        } else {
            None
        };

        self.skip_whitespace();
        if !self.starts_with_keyword(":=") {
            return Err("Expected ':=' in declaration".to_string());
        }
        self.advance_by(2);
        let value = self.parse_expr()?;

        Ok((params, ret_ty, value))
    }

    fn parse_inductive_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(9); // consume "inductive"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        // Parse optional parameters
        let mut params = Vec::new();
        while self.peek() == Some('(') || self.peek() == Some('{') {
            let implicit = self.peek() == Some('{');
            self.advance();
            let mut names = vec![self.parse_ident_raw()?];
            self.skip_whitespace();
            while self.peek() != Some(':') {
                names.push(self.parse_ident_raw()?);
                self.skip_whitespace();
            }
            self.advance();
            let pty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            let close = if implicit { '}' } else { ')' };
            if self.peek() != Some(close) {
                return Err(format!("Expected '{}'", close));
            }
            self.advance();
            for name in names {
                params.push((name, pty.clone()));
            }
            self.skip_whitespace();
        }

        // Return type (usually Type or Prop)
        let ty = if self.peek() == Some(':') {
            self.advance();
            self.parse_pi_or_arrow()?
        } else {
            ParsedExpr::Sort(1) // default to Type
        };

        self.skip_whitespace();
        if !self.starts_with_keyword("where") {
            return Err("Expected 'where' after inductive type".to_string());
        }
        self.advance_by(5);
        self.skip_whitespace();

        // Parse constructors: | ctor : type | ctor : type
        let mut ctors = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek() != Some('|') {
                break;
            }
            self.advance(); // consume '|'
            self.skip_whitespace();
            let ctor_name = self.parse_ident_raw()?;
            self.skip_whitespace();
            if self.peek() != Some(':') {
                return Err("Expected ':' in constructor".to_string());
            }
            self.advance();
            let ctor_ty = self.parse_pi_or_arrow()?;
            ctors.push((ctor_name, ctor_ty));
        }

        // Wrap constructor types with parameters if any
        let final_ty = if params.is_empty() {
            ty
        } else {
            let mut result = ty;
            for (pname, pty) in params.iter().rev() {
                result = ParsedExpr::Pi(pname.clone(), Box::new(pty.clone()), Box::new(result));
            }
            result
        };

        let final_ctors = ctors.into_iter().map(|(n, t)| {
            if params.is_empty() {
                (n, t)
            } else {
                let mut ct = t;
                for (pname, pty) in params.iter().rev() {
                    ct = ParsedExpr::Pi(pname.clone(), Box::new(pty.clone()), Box::new(ct));
                }
                (n, ct)
            }
        }).collect();

        Ok(ParsedDecl::Inductive { name, ty: final_ty, ctors: final_ctors, num_params: params.len() })
    }

    fn parse_mutual_inductive_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(6); // consume "mutual"
        self.skip_whitespace();

        let mut types = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.starts_with_keyword("end") {
                self.advance_by(3);
                break;
            }
            if !self.starts_with_keyword("inductive") {
                return Err("Expected 'inductive' or 'end' in mutual block".to_string());
            }
            self.advance_by(9); // consume "inductive"
            self.skip_whitespace();
            let name = self.parse_ident_raw()?;
            self.skip_whitespace();

            // Parse optional parameters
            let mut params = Vec::new();
            while self.peek() == Some('(') || self.peek() == Some('{') {
                let implicit = self.peek() == Some('{');
                self.advance();
                let mut names = vec![self.parse_ident_raw()?];
                self.skip_whitespace();
                while self.peek() != Some(':') {
                    names.push(self.parse_ident_raw()?);
                    self.skip_whitespace();
                }
                self.advance();
                let pty = self.parse_pi_or_arrow()?;
                self.skip_whitespace();
                let close = if implicit { '}' } else { ')' };
                if self.peek() != Some(close) {
                    return Err(format!("Expected '{}'", close));
                }
                self.advance();
                for pname in names {
                    params.push((pname, pty.clone()));
                }
                self.skip_whitespace();
            }

            // Return type
            let ty = if self.peek() == Some(':') {
                self.advance();
                self.parse_pi_or_arrow()?
            } else {
                ParsedExpr::Sort(1)
            };

            self.skip_whitespace();
            if !self.starts_with_keyword("where") {
                return Err("Expected 'where' after inductive type in mutual block".to_string());
            }
            self.advance_by(5);
            self.skip_whitespace();

            // Parse constructors
            let mut ctors = Vec::new();
            loop {
                self.skip_whitespace_and_comments();
                if self.peek() != Some('|') {
                    break;
                }
                self.advance();
                self.skip_whitespace();
                let ctor_name = self.parse_ident_raw()?;
                self.skip_whitespace();
                if self.peek() != Some(':') {
                    return Err("Expected ':' in constructor".to_string());
                }
                self.advance();
                let ctor_ty = self.parse_pi_or_arrow()?;
                ctors.push((ctor_name, ctor_ty));
            }

            // Wrap constructor types with parameters
            let final_ty = if params.is_empty() {
                ty
            } else {
                let mut result = ty;
                for (pname, pty) in params.iter().rev() {
                    result = ParsedExpr::Pi(pname.clone(), Box::new(pty.clone()), Box::new(result));
                }
                result
            };

            let final_ctors = ctors.into_iter().map(|(n, t)| {
                if params.is_empty() {
                    (n, t)
                } else {
                    let mut ct = t;
                    for (pname, pty) in params.iter().rev() {
                        ct = ParsedExpr::Pi(pname.clone(), Box::new(pty.clone()), Box::new(ct));
                    }
                    (n, ct)
                }
            }).collect();

            types.push((name, final_ty, final_ctors, params.len()));
        }

        Ok(ParsedDecl::MutualInductive { types })
    }

    fn parse_structure_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(9); // consume "structure"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        // Optional parent type (ignored for now)
        let ty = if self.peek() == Some(':') {
            self.advance();
            self.parse_pi_or_arrow()?
        } else {
            ParsedExpr::Sort(1) // default to Type
        };

        self.skip_whitespace();
        if self.peek() != Some(':') || self.input.get(self.pos + 1) != Some(&'=') {
            return Err("Expected ':=/' after structure name".to_string());
        }
        self.advance_by(2); // consume ":="
        self.skip_whitespace();

        // Parse fields: (field_name : field_type)
        let mut fields = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek() != Some('(') {
                break;
            }
            self.advance(); // consume '('
            self.skip_whitespace();
            let fname = self.parse_ident_raw()?;
            self.skip_whitespace();
            if self.peek() != Some(':') {
                return Err("Expected ':' in structure field".to_string());
            }
            self.advance();
            let fty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            if self.peek() != Some(')') {
                return Err("Expected ')' after field".to_string());
            }
            self.advance(); // consume ')'
            fields.push((fname, fty));
        }

        if fields.is_empty() {
            return Err("Structure must have at least one field".to_string());
        }

        Ok(ParsedDecl::Structure { name, ty, fields })
    }

    fn peek(&self) -> Option<char> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn skip_whitespace(&mut self) {
        loop {
            while let Some(c) = self.peek() {
                if c.is_whitespace() {
                    self.advance();
                } else {
                    break;
                }
            }
            // Skip line comments: -- ...\n
            if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'-') {
                while let Some(c) = self.peek() {
                    self.advance();
                    if c == '\n' {
                        break;
                    }
                }
                continue;
            }
            // Skip block comments: /- ... -/
            if self.peek() == Some('/') && self.input.get(self.pos + 1) == Some(&'-') {
                self.advance();
                self.advance();
                let mut depth = 1;
                while depth > 0 {
                    if let Some(c) = self.peek() {
                        if c == '/' && self.input.get(self.pos + 1) == Some(&'-') {
                            self.advance();
                            self.advance();
                            depth += 1;
                        } else if c == '-' && self.input.get(self.pos + 1) == Some(&'/') {
                            self.advance();
                            self.advance();
                            depth -= 1;
                        } else {
                            self.advance();
                        }
                    } else {
                        break;
                    }
                }
                continue;
            }
            break;
        }
    }

    fn consume(&mut self, expected: char) -> Result<(), String> {
        self.skip_whitespace();
        if let Some(c) = self.peek() {
            if c == expected {
                self.advance();
                return Ok(());
            }
        }
        Err(format!("Expected '{}', got {:?}", expected, self.peek()))
    }

    fn parse_pi_or_arrow(&mut self) -> Result<ParsedExpr, String> {
        self.skip_whitespace();

        // Check for tactic block: by tactic1; tactic2; ...
        if self.starts_with_keyword("by") {
            return self.parse_tactic_block();
        }

        // Check for dependent pi: (x : A) -> B
        if self.peek() == Some('(') {
            let saved_pos = self.pos;
            self.advance(); // consume '('
            self.skip_whitespace();

            // Try to parse as dependent pi
            if let Ok(name) = self.parse_ident_raw() {
                self.skip_whitespace();
                if self.peek() == Some(':') {
                    self.advance(); // consume ':'
                    let ty = self.parse_pi_or_arrow()?;
                    self.consume(')')?;
                    self.skip_whitespace();

                    if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'>') {
                        self.advance();
                        self.advance();
                        let body = self.parse_pi_or_arrow()?;
                        return Ok(ParsedExpr::Pi(name, Box::new(ty), Box::new(body)));
                    } else if self.peek() == Some(',') {
                        self.advance();
                        let body = self.parse_pi_or_arrow()?;
                        return Ok(ParsedExpr::Pi(name, Box::new(ty), Box::new(body)));
                    }
                }
            }

            // Not a pi, restore and parse as parens
            self.pos = saved_pos;
        }

        let left = self.parse_infix(0)?;
        self.skip_whitespace();

        // Arrow: A -> B
        if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'>') {
            self.advance();
            self.advance();
            let right = self.parse_pi_or_arrow()?;
            return Ok(ParsedExpr::Pi("_".to_string(), Box::new(left), Box::new(right)));
        }

        Ok(left)
    }

    /// Parse a tactic block: by tactic1; tactic2; ...
    fn parse_tactic_block(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(2); // consume "by"
        self.skip_whitespace();

        let mut tactics = Vec::new();
        loop {
            self.skip_whitespace_and_comments();

            // Check if we've reached a keyword that ends the tactic block
            if self.peek().is_none()
                || self.starts_with_keyword("def")
                || self.starts_with_keyword("theorem")
                || self.starts_with_keyword("solve")
                || self.starts_with_keyword("inductive")
                || self.starts_with_keyword("structure")
                || self.starts_with_keyword("axiom")
                || self.starts_with_keyword("import")
            {
                break;
            }

            // Indentation column where this tactic starts. Continuation lines must
            // be indented strictly more than this; lines at this column (or less)
            // that begin with a tactic keyword start a new tactic.
            let tactic_start_col = self.current_col();

            // Parse a single tactic command (everything until ';' or block end)
            let mut tactic_str = String::new();
            let mut paren_depth = 0;
            let start_pos = self.pos;
            loop {
                if self.peek().is_none() {
                    break;
                }

                let c = self.peek().unwrap();

                if c == '(' {
                    paren_depth += 1;
                } else if c == ')' {
                    if paren_depth == 0 {
                        break;
                    }
                    paren_depth -= 1;
                } else if c == ';' && paren_depth == 0 {
                    self.advance(); // consume ';'
                    break;
                } else if c == '\n' && paren_depth == 0 {
                    // Append the newline and advance, then inspect the next line.
                    tactic_str.push(c);
                    self.advance();
                    // A new tactic begins when the next token is at the same or
                    // lower indentation as this tactic and is a known tactic or
                    // top-level declaration keyword.
                    let (next_col, next_kw) = self.peek_next_token_col();
                    let do_break = next_col <= tactic_start_col
                        && (next_kw.is_some()
                            || self.peek().is_none()
                            || self.starts_with_keyword("def")
                            || self.starts_with_keyword("theorem")
                            || self.starts_with_keyword("solve")
                            || self.starts_with_keyword("inductive")
                            || self.starts_with_keyword("structure")
                            || self.starts_with_keyword("axiom")
                            || self.starts_with_keyword("import"));
                    if do_break {
                        break;
                    }
                    // Otherwise this is a continuation line: fall through and keep
                    // appending characters.
                    continue;
                }

                tactic_str.push(c);
                self.advance();
            }

            let tactic_str = tactic_str.trim().to_string();
            if !tactic_str.is_empty() {
                tactics.push(tactic_str);
            }

            // If the inner loop made no progress, we are stuck at a terminator
            // (e.g. an unmatched ')') that does not belong to this tactic block.
            // Stop parsing the block to avoid an infinite loop.
            if self.pos == start_pos {
                break;
            }

            // If we hit EOF without ';', stop
            if self.peek().is_none() {
                break;
            }
        }

        if tactics.is_empty() {
            return Err("Empty tactic block".to_string());
        }

        Ok(ParsedExpr::TacticBlock(tactics))
    }

    /// Parse infix operators (+, -, *) with precedence climbing.
    /// Supports both hardcoded operators and user-defined infix declarations.
    fn parse_infix(&mut self, min_prec: i32) -> Result<ParsedExpr, String> {
        let mut left = self.parse_app_or_atom()?;
        loop {
            self.skip_whitespace_and_comments();

            // Determine operator and precedence
            // First check user-defined infix operators (they override hardcoded ones)
            let user_op = {
                let mut matched_op: Option<(String, i32, bool, String)> = None;
                for (sym, (prec, func, left_assoc)) in &self.infix_ops {
                    if self.input.get(self.pos..self.pos + sym.len()) == Some(sym.chars().collect::<Vec<_>>().as_slice()) {
                        let next_char = self.input.get(self.pos + sym.len());
                        // Make sure it's not a prefix of a longer identifier/operator
                        if let Some(nc) = next_char {
                            if nc.is_alphanumeric() || *nc == '_' || *nc == '\'' {
                                continue;
                            }
                            // Don't match prefixes of -> or =>
                            if *nc == '>' {
                                continue;
                            }
                        }
                        if matched_op.is_none() || sym.len() > matched_op.as_ref().unwrap().0.len() {
                            matched_op = Some((sym.clone(), *prec, *left_assoc, func.clone()));
                        }
                    }
                }
                matched_op
            };

            let (op, prec, left_assoc, func_name) = if let Some(u) = user_op {
                u
            } else if self.peek() == Some('+') {
                ("+".to_string(), 6, true, "add".to_string())
            } else if self.peek() == Some('-') {
                // Distinguish from arrow ->
                if self.input.get(self.pos + 1) == Some(&'>') {
                    break;
                }
                ("-".to_string(), 6, true, "sub".to_string())
            } else if self.peek() == Some('*') {
                ("*".to_string(), 7, true, "mul".to_string())
            } else {
                break;
            };

            if prec < min_prec {
                break;
            }

            self.advance_by(op.len()); // consume operator

            // Left-associative: right side needs higher precedence
            // Right-associative: right side needs same or higher precedence
            let next_min_prec = if left_assoc { prec + 1 } else { prec };
            let right = self.parse_infix(next_min_prec)?;

            left = ParsedExpr::App(
                Box::new(ParsedExpr::App(
                    Box::new(ParsedExpr::Const(func_name)),
                    Box::new(left),
                )),
                Box::new(right),
            );
        }
        Ok(left)
    }

    fn parse_app_or_atom(&mut self) -> Result<ParsedExpr, String> {
        let mut atoms = vec![self.parse_atom()?];

        loop {
            self.skip_whitespace_and_comments();
            let c = self.peek();
            if c.is_none() || c == Some(')') || c == Some('.') || c == Some(',')
                || c == Some(':') || c == Some('=') || c == Some('|')
                || (c == Some('-') && self.input.get(self.pos + 1) == Some(&'>'))
                || c == Some('}') || c == Some('{')
                || c == Some('+') || c == Some('-') || c == Some('*')
                || c == Some('_') {
                break;
            }
            // Keywords that end the application chain
            if self.starts_with_keyword("in") || self.starts_with_keyword("with") || self.starts_with_keyword("where")
                || self.starts_with_keyword("def") || self.starts_with_keyword("theorem")
                || self.starts_with_keyword("inductive") || self.starts_with_keyword("structure") || self.starts_with_keyword("axiom")
                || self.starts_with_keyword("postulate") || self.starts_with_keyword("module")
                || self.starts_with_keyword("solve")
                || self.starts_with_keyword("notation")
                || self.starts_with_keyword("calc")
                || self.starts_with_keyword("infixl") || self.starts_with_keyword("infix")
                || self.starts_with_keyword("if") || self.starts_with_keyword("then") || self.starts_with_keyword("else")
                || self.starts_with_keyword("section") || self.starts_with_keyword("end")
                || self.starts_with_keyword("variable") || self.starts_with_keyword("mutual")
                || self.starts_with_keyword("import") {
                break;
            }
            atoms.push(self.parse_atom()?);
        }

        if atoms.len() == 1 {
            Ok(atoms.into_iter().next().unwrap())
        } else {
            let mut result = atoms[0].clone();
            for atom in atoms.into_iter().skip(1) {
                result = ParsedExpr::App(Box::new(result), Box::new(atom));
            }
            Ok(result)
        }
    }

    fn parse_atom(&mut self) -> Result<ParsedExpr, String> {
        self.skip_whitespace();
        let c = self.peek();

        match c {
            None => Err("Unexpected end of input".to_string()),
            Some('(') => {
                self.advance();
                let expr = self.parse_expr()?;
                self.consume(')')?;
                Ok(expr)
            }
            Some('\\') => self.parse_lambda(),
            Some('0'..='9') => self.parse_nat_lit(),
            Some(_) => {
                if self.peek() == Some('?') {
                    self.advance(); // consume '?'
                    let name = self.parse_ident_raw()?;
                    Ok(ParsedExpr::MVar(name))
                } else if self.starts_with_keyword("fun") {
                    self.parse_fun()
                } else if self.starts_with_keyword("let") {
                    self.parse_let()
                } else if self.starts_with_keyword("have") {
                    self.parse_have()
                } else if self.starts_with_keyword("match") {
                    self.parse_match()
                } else if self.starts_with_keyword("fix") {
                    self.parse_fix()
                } else if self.starts_with_keyword("if") {
                    self.parse_if()
                } else if self.starts_with_keyword("forall") {
                    self.parse_forall()
                } else if self.starts_with_keyword("exists") {
                    self.parse_exists()
                } else if self.starts_with_keyword("calc") {
                    self.parse_calc()
                } else if self.starts_with_keyword("Type") {
                    self.advance_by(4);
                    Ok(ParsedExpr::Sort(1))
                } else if self.starts_with_keyword("Prop") {
                    self.advance_by(4);
                    Ok(ParsedExpr::Sort(0))
                } else {
                    // Check for nullary notation: identifier matches a notation symbol
                    if let Some(notation) = self.match_notation() {
                        return Ok(notation);
                    }
                    self.parse_ident_or_bvar()
                }
            }
        }
    }

    fn parse_lambda(&mut self) -> Result<ParsedExpr, String> {
        self.advance(); // consume '\'
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let ty = if self.peek() == Some(':') {
            self.advance();
            self.parse_pi_or_arrow()?
        } else {
            ParsedExpr::Const("?".to_string())
        };

        self.skip_whitespace();
        self.consume('.')?;
        let body = self.parse_expr()?;

        Ok(ParsedExpr::Lambda(name, Box::new(ty), Box::new(body)))
    }

    fn parse_fun(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(3); // consume "fun"
        self.skip_whitespace();

        // Parse one or more parameter names
        let mut params = vec![self.parse_ident_raw()?];
        self.skip_whitespace();

        // Additional parameters for multi-param lambda: fun x y z => body
        while self.peek() != Some(':') && !self.starts_with_keyword("=>") {
            if let Some(c) = self.peek() {
                if c.is_alphanumeric() || c == '_' || c == '\'' {
                    params.push(self.parse_ident_raw()?);
                    self.skip_whitespace();
                    continue;
                }
            }
            break;
        }

        let ty = if self.peek() == Some(':') {
            self.advance();
            self.parse_pi_or_arrow()?
        } else {
            ParsedExpr::Const("?".to_string())
        };

        self.skip_whitespace();
        if self.starts_with_keyword("=>") {
            self.advance_by(2);
        } else {
            return Err("Expected '=>' after fun parameter".to_string());
        }

        let mut body = self.parse_expr()?;
        let first_param = params[0].clone();

        // Nest lambdas for multiple parameters: fun x y z => body ~ fun x => fun y => fun z => body
        for param in params.into_iter().skip(1).rev() {
            body = ParsedExpr::Lambda(param, Box::new(ParsedExpr::Const("?".to_string())), Box::new(body));
        }

        Ok(ParsedExpr::Lambda(first_param, Box::new(ty), Box::new(body)))
    }

    fn parse_let(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(3); // consume "let"
        self.skip_whitespace();

        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let (ty, val) = if self.peek() == Some(':') && self.input.get(self.pos + 1) != Some(&'=') {
            self.advance();
            let ty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            if !self.starts_with_keyword(":=") {
                return Err("Expected ':=' in let binding".to_string());
            }
            self.advance_by(2);
            let val = self.parse_expr()?;
            (ty, val)
        } else {
            self.skip_whitespace();
            if !self.starts_with_keyword(":=") {
                return Err("Expected ':=' in let binding".to_string());
            }
            self.advance_by(2);
            let val = self.parse_expr()?;
            (ParsedExpr::Const("?".to_string()), val)
        };

        self.skip_whitespace();
        if !self.starts_with_keyword("in") {
            return Err("Expected 'in' after let binding".to_string());
        }
        self.advance_by(2);
        let body = self.parse_expr()?;

        Ok(ParsedExpr::Let(name, Box::new(ty), Box::new(val), Box::new(body)))
    }

    fn parse_have(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(4); // consume "have"
        self.skip_whitespace();

        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let (ty, val) = if self.peek() == Some(':') && self.input.get(self.pos + 1) != Some(&'=') {
            self.advance();
            let ty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            if !self.starts_with_keyword(":=") {
                return Err("Expected ':=' in have binding".to_string());
            }
            self.advance_by(2);
            let val = self.parse_expr()?;
            (ty, val)
        } else {
            self.skip_whitespace();
            if !self.starts_with_keyword(":=") {
                return Err("Expected ':=' in have binding".to_string());
            }
            self.advance_by(2);
            let val = self.parse_expr()?;
            (ParsedExpr::Const("?".to_string()), val)
        };

        self.skip_whitespace();
        if !self.starts_with_keyword("in") {
            return Err("Expected 'in' after have binding".to_string());
        }
        self.advance_by(2);
        let body = self.parse_expr()?;

        Ok(ParsedExpr::Let(name, Box::new(ty), Box::new(val), Box::new(body)))
    }

    fn parse_match(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(5); // consume "match"
        self.skip_whitespace();

        let scrutinee = self.parse_expr()?;
        self.skip_whitespace();

        if self.peek() != Some(':') {
            return Err("Expected ':' after match scrutinee (match e : T with ...)".to_string());
        }
        self.advance();
        let motive = self.parse_expr()?;
        self.skip_whitespace();

        if !self.starts_with_keyword("with") {
            return Err("Expected 'with' after match motive".to_string());
        }
        self.advance_by(4);
        self.skip_whitespace();

        // Parse branches: | pat => expr | pat => expr
        let mut branches = Vec::new();
        let mut first_pipe_line: Option<usize> = None;
        let mut first_pipe_col: Option<usize> = None;
        let mut last_pipe_line: Option<usize> = None;
        loop {
            self.skip_whitespace();
            if self.peek() != Some('|') {
                break;
            }
            let pipe_line = self.line_start(self.pos);
            let pipe_col = self.pos - pipe_line;
            match (first_pipe_line, first_pipe_col) {
                (Some(line), Some(col)) => {
                    // Same line as first pipe: always accept
                    // Same line as previous pipe: always accept (chained on one line)
                    // Different line: must have same column as first pipe
                    if pipe_line != line && Some(pipe_line) != last_pipe_line && pipe_col != col {
                        break;
                    }
                }
                _ => {
                    first_pipe_line = Some(pipe_line);
                    first_pipe_col = Some(pipe_col);
                }
            }
            last_pipe_line = Some(pipe_line);
            self.advance(); // consume '|'
            self.skip_whitespace();

            // Parse pattern: ctor or ctor var
            let pat = self.parse_pattern()?;
            self.skip_whitespace();

            if self.peek() != Some('=') || self.input.get(self.pos + 1) != Some(&'>') {
                return Err("Expected '=>' after pattern".to_string());
            }
            self.advance_by(2);
            let body = self.parse_expr()?;
            branches.push((pat, body));
            self.skip_whitespace();
        }

        if branches.is_empty() {
            return Err("Match must have at least one branch".to_string());
        }

        Ok(ParsedExpr::Match(Box::new(scrutinee), Box::new(motive), branches))
    }

    /// Parse a well-founded fixpoint: fix f (x : T) measure m => e
    fn parse_fix(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(3); // consume "fix"
        self.skip_whitespace();

        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        if self.peek() != Some('(') {
            return Err("Expected '(' after fix function name".to_string());
        }
        self.advance(); // consume '('
        let param = self.parse_ident_raw()?;
        self.skip_whitespace();

        if self.peek() != Some(':') {
            return Err("Expected ':' in fix parameter".to_string());
        }
        self.advance(); // consume ':'
        let param_ty = self.parse_pi_or_arrow()?;
        self.skip_whitespace();

        if self.peek() != Some(')') {
            return Err("Expected ')' after fix parameter".to_string());
        }
        self.advance(); // consume ')'
        self.skip_whitespace();

        if !self.starts_with_keyword("measure") {
            return Err("Expected 'measure' after fix parameter".to_string());
        }
        self.advance_by(7); // consume "measure"
        self.skip_whitespace();

        let measure = self.parse_expr()?;
        self.skip_whitespace();

        if !self.starts_with_keyword("=>") {
            return Err("Expected '=>' after fix measure".to_string());
        }
        self.advance_by(2); // consume "=>"
        self.skip_whitespace();

        let body = self.parse_expr()?;

        Ok(ParsedExpr::Fix {
            name,
            param,
            param_ty: Box::new(param_ty),
            measure: Box::new(measure),
            body: Box::new(body),
        })
    }

    /// Parse if/then/else: if c : T then t else e
    /// Desugars to: match c : T with | true => t | false => e
    fn parse_if(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(2); // consume "if"
        self.skip_whitespace();

        let cond = self.parse_expr()?;
        self.skip_whitespace();

        if self.peek() != Some(':') {
            return Err("Expected ':' after if condition (if c : T then t else e)".to_string());
        }
        self.advance();
        let motive = self.parse_expr()?;
        self.skip_whitespace();

        if !self.starts_with_keyword("then") {
            return Err("Expected 'then' after if motive".to_string());
        }
        self.advance_by(4);
        self.skip_whitespace();
        let then_branch = self.parse_expr()?;
        self.skip_whitespace();

        if !self.starts_with_keyword("else") {
            return Err("Expected 'else' after then branch".to_string());
        }
        self.advance_by(4);
        self.skip_whitespace();
        let else_branch = self.parse_expr()?;

        Ok(ParsedExpr::Match(
            Box::new(cond),
            Box::new(motive),
            vec![
                (ParsedExpr::Const("true".to_string()), then_branch),
                (ParsedExpr::Const("false".to_string()), else_branch),
            ],
        ))
    }

    /// Parse calc block: calc (ty); a = b := h; b = c := h2; ...
    /// Each line after the first can use `_` for the left-hand side (inferred from previous rhs).
    /// Desugars to nested eq_subst calls.
    fn parse_calc(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(4); // consume "calc"
        self.skip_whitespace();

        // Type annotation must be parenthesized to avoid greedy parsing
        if self.peek() != Some('(') {
            return Err("Expected '(' after calc for type annotation".to_string());
        }
        self.advance();
        let ty = self.parse_expr()?;
        self.consume(')')?;

        self.skip_whitespace();

        // Parse steps: each step is "lhs = rhs := proof" or "_ = rhs := proof"
        let mut steps = Vec::new();
        let mut first_lhs: Option<ParsedExpr> = None;

        loop {
            self.skip_whitespace_and_comments();
            // End of calc block: next token is a keyword or closing delimiter
            if self.peek().is_none()
                || self.starts_with_keyword("def")
                || self.starts_with_keyword("theorem")
                || self.starts_with_keyword("inductive")
                || self.starts_with_keyword("where")
                || self.starts_with_keyword("end")
                || self.starts_with_keyword("in")
                || self.starts_with_keyword("with")
                || self.peek() == Some(')')
                || self.peek() == Some('}')
            {
                break;
            }

            // Parse lhs (or _ for inferred)
            let lhs = if self.peek() == Some('_') {
                self.advance();
                if first_lhs.is_none() {
                    return Err("Cannot use '_' in the first calc step".to_string());
                }
                // Use previous rhs as lhs
                steps.last().map(|(_, rhs, _): &(ParsedExpr, ParsedExpr, ParsedExpr)| rhs.clone()).unwrap()
            } else {
                let l = self.parse_expr()?;
                if first_lhs.is_none() {
                    first_lhs = Some(l.clone());
                }
                l
            };

            self.skip_whitespace();
            if self.peek() != Some('=') {
                return Err(format!("Expected '=' in calc step, got {:?}", self.peek()));
            }
            self.advance(); // consume '='

            self.skip_whitespace();
            let rhs = self.parse_expr()?;

            self.skip_whitespace();
            if self.peek() != Some(':') || self.input.get(self.pos + 1) != Some(&'=') {
                return Err("Expected ':=' after calc step rhs".to_string());
            }
            self.advance_by(2); // consume ':='
            self.skip_whitespace();
            let proof = self.parse_expr()?;

            steps.push((lhs, rhs, proof));

            // Optional semicolon or newline separates steps
            self.skip_whitespace();
            if self.peek() == Some(';') {
                self.advance();
            }
        }

        if steps.is_empty() {
            return Err("calc block must have at least one step".to_string());
        }

        Ok(ParsedExpr::Calc(Box::new(ty), steps))
    }

    /// Parse forall: forall (x : A), B  or  forall (x : A) -> B
    fn parse_forall(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(7); // consume "forall"
        self.skip_whitespace();

        if self.peek() != Some('(') && self.peek() != Some('{') {
            return Err("Expected '(' or '{' after forall".to_string());
        }

        let mut binders = Vec::new();
        while self.peek() == Some('(') || self.peek() == Some('{') {
            let implicit = self.peek() == Some('{');
            self.advance();
            let mut names = vec![self.parse_ident_raw()?];
            self.skip_whitespace();
            while self.peek() != Some(':') {
                names.push(self.parse_ident_raw()?);
                self.skip_whitespace();
            }
            self.advance(); // consume ':'
            let ty = self.parse_pi_or_arrow()?;
            let close = if implicit { '}' } else { ')' };
            if self.peek() != Some(close) {
                return Err(format!("Expected '{}'", close));
            }
            self.advance();
            for name in names {
                binders.push((name, ty.clone()));
            }
            self.skip_whitespace();
        }

        // Optional comma or arrow
        if self.peek() == Some(',') {
            self.advance();
        } else if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'>') {
            self.advance();
            self.advance();
        }

        let body = self.parse_pi_or_arrow()?;

        // Nest Pi binders: forall (a b : A), B ~ forall (a : A), forall (b : A), B
        let mut result = body;
        for (name, ty) in binders.into_iter().rev() {
            result = ParsedExpr::Pi(name, Box::new(ty), Box::new(result));
        }
        Ok(result)
    }

    /// Parse exists: exists (x : A), B  desugars to Exists A (\x : A . B)
    fn parse_exists(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(6); // consume "exists"
        self.skip_whitespace();

        if self.peek() != Some('(') && self.peek() != Some('{') {
            return Err("Expected '(' or '{' after exists".to_string());
        }
        let implicit = self.peek() == Some('{');
        self.advance();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();
        if self.peek() != Some(':') {
            return Err("Expected ':' in exists binder".to_string());
        }
        self.advance();
        let ty = self.parse_pi_or_arrow()?;
        let close = if implicit { '}' } else { ')' };
        if self.peek() != Some(close) {
            return Err(format!("Expected '{}'", close));
        }
        self.advance();

        self.skip_whitespace();
        if self.peek() == Some(',') {
            self.advance();
        }

        let body = self.parse_pi_or_arrow()?;
        // Desugar to Exists ty (\name : ty . body)
        let lambda = ParsedExpr::Lambda(name.clone(), Box::new(ty.clone()), Box::new(body));
        Ok(ParsedExpr::App(
            Box::new(ParsedExpr::App(
                Box::new(ParsedExpr::Const("Exists".to_string())),
                Box::new(ty),
            )),
            Box::new(lambda),
        ))
    }

    /// Parse a pattern: constructor optionally applied to variable names.
    fn parse_pattern(&mut self) -> Result<ParsedExpr, String> {
        let ctor = self.parse_ident_raw()?;
        let mut result = ParsedExpr::Const(ctor);

        // Parse variables after constructor: ctor v1 v2 ...
        loop {
            self.skip_whitespace();
            if let Some(c) = self.peek() {
                if c.is_alphabetic() || c == '_' {
                    let var = self.parse_ident_raw()?;
                    result = ParsedExpr::App(Box::new(result), Box::new(ParsedExpr::Const(var)));
                    continue;
                }
            }
            break;
        }

        Ok(result)
    }

    fn parse_nat_lit(&mut self) -> Result<ParsedExpr, String> {
        let mut num = 0u64;
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                num = num * 10 + (c as u64 - '0' as u64);
                self.advance();
            } else {
                break;
            }
        }
        // Defer numeric literal expansion to to_expr so the environment
        // can resolve the actual constructor names (registry-driven).
        Ok(ParsedExpr::NatLit(num))
    }

    fn parse_ident_or_bvar(&mut self) -> Result<ParsedExpr, String> {
        let name = self.parse_ident_raw()?;
        if name.starts_with("x") {
            if let Ok(n) = name[1..].parse::<u64>() {
                return Ok(ParsedExpr::BVar(n));
            }
        }
        Ok(ParsedExpr::Const(name))
    }

    fn parse_ident_raw(&mut self) -> Result<String, String> {
        self.skip_whitespace();
        let mut name = String::new();

        // Special case for := and =>
        if self.peek() == Some(':') && self.input.get(self.pos + 1) == Some(&'=') {
            return Err("Unexpected ':='".to_string());
        }

        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' || c == '.' || c == '\'' {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }

        if name.is_empty() {
            Err(format!("Expected identifier, got {:?}", self.peek()))
        } else {
            Ok(name)
        }
    }

    /// Check if the current position matches a nullary notation symbol.
    /// If so, advance past it and return the expansion expression.
    fn match_notation(&mut self) -> Option<ParsedExpr> {
        self.skip_whitespace();
        // Collect notation entries to avoid borrow issues
        let notations: Vec<(String, ParsedExpr)> = self.notations.iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        for (symbol, expansion) in notations {
            let symbol_chars: Vec<char> = symbol.chars().collect();
            let symbol_len = symbol_chars.len();
            if self.input.get(self.pos..self.pos + symbol_len) == Some(symbol_chars.as_slice()) {
                // Make sure it's not a prefix of a longer identifier
                let next_char = self.input.get(self.pos + symbol_len);
                if let Some(nc) = next_char {
                    if nc.is_alphanumeric() || *nc == '_' || *nc == '\'' {
                        continue;
                    }
                }
                self.advance_by(symbol_len);
                return Some(expansion);
            }
        }
        None
    }

    fn starts_with_keyword(&self, kw: &str) -> bool {
        // Skip leading whitespace without cloning the parser state.
        let mut pos = self.pos;
        while pos < self.input.len() && self.input[pos].is_whitespace() {
            pos += 1;
        }
        let kw_chars: Vec<char> = kw.chars().collect();
        if pos + kw_chars.len() > self.input.len() {
            return false;
        }
        for (i, &kc) in kw_chars.iter().enumerate() {
            if self.input[pos + i] != kc {
                return false;
            }
        }
        // Make sure it's not a prefix of a longer identifier
        if let Some(&c) = self.input.get(pos + kw_chars.len()) {
            if c.is_alphanumeric() || c == '_' || c == '\'' {
                return false;
            }
        }
        true
    }

    fn advance_by(&mut self, n: usize) {
        self.pos += n;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> ParsedExpr {
        let mut p = Parser::new(s);
        p.parse_expr().unwrap()
    }

    #[test]
    fn test_parse_const() {
        let e = parse("Nat");
        assert!(matches!(e, ParsedExpr::Const(name) if name == "Nat"));
    }

    #[test]
    fn test_parse_app() {
        let e = parse("succ zero");
        match e {
            ParsedExpr::App(f, a) => {
                assert!(matches!(f.as_ref(), ParsedExpr::Const(name) if name == "succ"));
                assert!(matches!(a.as_ref(), ParsedExpr::Const(name) if name == "zero"));
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_parse_lambda() {
        let e = parse("\\x : Nat . x");
        match e {
            ParsedExpr::Lambda(name, ty, body) => {
                assert_eq!(name, "x");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "x"));
            }
            _ => panic!("Expected Lambda"),
        }
    }

    #[test]
    fn test_parse_arrow() {
        let e = parse("Nat -> Nat");
        match e {
            ParsedExpr::Pi(name, ty, body) => {
                assert_eq!(name, "_");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
            }
            _ => panic!("Expected Pi"),
        }
    }

    #[test]
    fn test_parse_dependent_pi() {
        let e = parse("(x : Nat) -> Nat");
        match e {
            ParsedExpr::Pi(name, ty, body) => {
                assert_eq!(name, "x");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
            }
            _ => panic!("Expected Pi"),
        }
    }

    #[test]
    fn test_parse_let() {
        let e = parse("let x := zero in x");
        match e {
            ParsedExpr::Let(name, _, val, body) => {
                assert_eq!(name, "x");
                assert!(matches!(val.as_ref(), ParsedExpr::Const(name) if name == "zero"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "x"));
            }
            _ => panic!("Expected Let"),
        }
    }

    #[test]
    fn test_parse_nat_lit() {
        let e = parse("3");
        // Numeric literals are now kept as NatLit(n) and expanded in to_expr
        assert!(matches!(e, ParsedExpr::NatLit(3)));
    }

    #[test]
    fn test_parse_sort() {
        let e = parse("Type");
        assert!(matches!(e, ParsedExpr::Sort(1)));
        let e = parse("Prop");
        assert!(matches!(e, ParsedExpr::Sort(0)));
    }

    #[test]
    fn test_parse_match_nat() {
        let e = parse("match succ zero : Nat with | zero => zero | succ n => n");
        assert!(matches!(e, ParsedExpr::Match(_, _, branches) if branches.len() == 2));
    }

    #[test]
    fn test_parse_simple_def() {
        let src = "def not (b : Bool) : Bool := true\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        assert!(matches!(&decls[0], ParsedDecl::Def { name, .. } if name == "not"));
    }

    #[test]
    fn test_parse_match_expr() {
        let src = "match b : Bool with\n| true => false\n| false => true";
        let mut p = Parser::new(src);
        let expr = p.parse_expr().unwrap();
        assert!(matches!(expr, ParsedExpr::Match(..)));
    }

    #[test]
    fn test_parse_def_with_match() {
        let src = "def not (b : Bool) : Bool :=\n  match b : Bool with\n  | true => false\n  | false => true\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        assert!(matches!(&decls[0], ParsedDecl::Def { name, .. } if name == "not"));
    }

    #[test]
    fn test_parse_inductive_only() {
        let src = "inductive Bool where\n| true : Bool\n| false : Bool\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        assert!(matches!(&decls[0], ParsedDecl::Inductive { .. }));
    }

    #[test]
    fn test_parse_inductive_then_simple_def() {
        let src = "inductive Bool where\n| true : Bool\n| false : Bool\n\ndef not (b : Bool) : Bool := true\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 2);
        assert!(matches!(&decls[0], ParsedDecl::Inductive { .. }));
        assert!(matches!(&decls[1], ParsedDecl::Def { .. }));
    }

    #[test]
    fn test_parse_alias_def() {
        let src = "def add := nat_add\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        assert!(matches!(&decls[0], ParsedDecl::Def { name, .. } if name == "add"));
    }

    #[test]
    fn test_parse_nat_sub_and_alias() {
        let src = "def nat_sub (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat -> Nat)\n    (fun n => zero)\n    (\\m' : Nat . \\ih : Nat -> Nat . fun n : Nat =>\n      rec.Nat (fun _ => Nat)\n        (succ m')\n        (fun n' : Nat => fun _ : Nat => ih n')\n        n)\n    m\n    n\n\ndef add := nat_add\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 2);
    }

    #[test]
    fn test_parse_full_nat_lean_inline() {
        let src = "def nat_add (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat) n (\\m' : Nat . \\ih : Nat . succ ih) m\n\ndef nat_sub (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat -> Nat)\n    (fun n => zero)\n    (\\m' : Nat . \\ih : Nat -> Nat . fun n : Nat =>\n      rec.Nat (fun _ => Nat)\n        (succ m')\n        (fun n' : Nat => fun _ : Nat => ih n')\n        n)\n    m\n    n\n\ndef nat_mul (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat) zero (\\m' : Nat . \\ih : Nat . nat_add ih n) m\n\n-- Aliases for infix operators\ndef add := nat_add\ndef sub := nat_sub\ndef mul := nat_mul\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 6);
    }

    #[test]
    fn test_parse_defs_with_comment_and_aliases() {
        let src = "def nat_mul (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat) zero (\\m' : Nat . \\ih : Nat . nat_add ih n) m\n\n-- Aliases for infix operators\ndef add := nat_add\ndef sub := nat_sub\ndef mul := nat_mul\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 4);
    }

    #[test]
    fn test_parse_three_defs_no_aliases() {
        let src = "def nat_add (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat) n (\\m' : Nat . \\ih : Nat . succ ih) m\n\ndef nat_sub (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat -> Nat)\n    (fun n => zero)\n    (\\m' : Nat . \\ih : Nat -> Nat . fun n : Nat =>\n      rec.Nat (fun _ => Nat)\n        (succ m')\n        (fun n' : Nat => fun _ : Nat => ih n')\n        n)\n    m\n    n\n\ndef nat_mul (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat) zero (\\m' : Nat . \\ih : Nat . nat_add ih n) m\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 3);
    }

    #[test]
    fn test_parse_nat_lean_file() {
        let path = std::path::Path::new("lib/Nat.cic");
        let src = std::fs::read_to_string(path).unwrap();
        let mut p = Parser::new(&src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 7);
    }

    #[test]
    fn test_parse_nat_sub_only() {
        let src = "def nat_sub (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat -> Nat)\n    (fun n => zero)\n    (\\m' : Nat . \\ih : Nat -> Nat . fun n : Nat =>\n      rec.Nat (fun _ => Nat)\n        (succ m')\n        (fun n' : Nat => fun _ : Nat => ih n')\n        n)\n    m\n    n\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn test_parse_fun_with_arrow_type() {
        // fun _ => Nat -> Nat should parse correctly
        let e = parse("fun _ => Nat -> Nat");
        match e {
            ParsedExpr::Lambda(name, _ty, body) => {
                assert_eq!(name, "_");
                // body should be Nat -> Nat = Pi(_, Nat, Nat)
                match body.as_ref() {
                    ParsedExpr::Pi(_, _, _) => {}
                    _ => panic!("Expected Pi in body, got {:?}", body),
                }
            }
            _ => panic!("Expected Lambda, got {:?}", e),
        }
    }

    #[test]
    fn test_parse_file_declarations() {
        let src = "inductive Bool where\n| true : Bool\n| false : Bool\n\ndef not (b : Bool) : Bool :=\n  match b : Bool with\n  | true => false\n  | false => true\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 2);
        assert!(matches!(&decls[0], ParsedDecl::Inductive { .. }));
        assert!(matches!(&decls[1], ParsedDecl::Def { .. }));
    }

    #[test]
    fn test_parse_infix_add() {
        let e = parse("2 + 3");
        // Should desugar to add 2 3 = App(App(Const("add"), NatLit(2)), NatLit(3))
        match e {
            ParsedExpr::App(f, rhs) => {
                match f.as_ref() {
                    ParsedExpr::App(op, lhs) => {
                        assert!(matches!(op.as_ref(), ParsedExpr::Const(name) if name == "add"));
                        assert!(matches!(lhs.as_ref(), ParsedExpr::NatLit(2)));
                        assert!(matches!(rhs.as_ref(), ParsedExpr::NatLit(3)));
                    }
                    _ => panic!("Expected App(App(add, 2), 3)"),
                }
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_parse_infix_precedence() {
        let e = parse("2 + 3 * 4");
        // Should be add 2 (mul 3 4)
        match e {
            ParsedExpr::App(f, rhs) => {
                match f.as_ref() {
                    ParsedExpr::App(op, lhs) => {
                        assert!(matches!(op.as_ref(), ParsedExpr::Const(name) if name == "add"));
                        assert!(matches!(lhs.as_ref(), ParsedExpr::NatLit(2)));
                        // rhs should be mul 3 4
                        match rhs.as_ref() {
                            ParsedExpr::App(f2, rhs2) => {
                                match f2.as_ref() {
                                    ParsedExpr::App(op2, lhs2) => {
                                        assert!(matches!(op2.as_ref(), ParsedExpr::Const(name) if name == "mul"));
                                        assert!(matches!(lhs2.as_ref(), ParsedExpr::NatLit(3)));
                                        assert!(matches!(rhs2.as_ref(), ParsedExpr::NatLit(4)));
                                    }
                                    _ => panic!("Expected mul"),
                                }
                            }
                            _ => panic!("Expected App for mul"),
                        }
                    }
                    _ => panic!("Expected App(App(add, 2), ...)"),
                }
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_parse_forall() {
        let e = parse("forall (n : Nat), Nat");
        match e {
            ParsedExpr::Pi(name, ty, body) => {
                assert_eq!(name, "n");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
            }
            _ => panic!("Expected Pi, got {:?}", e),
        }
    }

    #[test]
    fn test_parse_forall_arrow() {
        let e = parse("forall (n : Nat) -> Nat");
        match e {
            ParsedExpr::Pi(name, ty, body) => {
                assert_eq!(name, "n");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
            }
            _ => panic!("Expected Pi, got {:?}", e),
        }
    }

    #[test]
    fn test_parse_variable_decl() {
        let src = "variable (n : Nat)\n\ndef test1 := succ n\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 2);
        assert!(matches!(&decls[0], ParsedDecl::Variable { .. }));
        assert!(matches!(&decls[1], ParsedDecl::Def { .. }));
    }

    #[test]
    fn test_parse_variable_after_inductive() {
        let src = "inductive Nat where\n| zero : Nat\n| succ : Nat -> Nat\n\nvariable (n : Nat)\n\ndef test1 := succ n\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 3);
        assert!(matches!(&decls[0], ParsedDecl::Inductive { .. }));
        assert!(matches!(&decls[1], ParsedDecl::Variable { .. }));
        assert!(matches!(&decls[2], ParsedDecl::Def { .. }));
    }

    #[test]
    fn test_parse_notation_decl() {
        let src = "notation \"NatAlias\" => Nat\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        match &decls[0] {
            ParsedDecl::Notation { symbol, expansion } => {
                assert_eq!(symbol, "NatAlias");
                assert!(matches!(expansion, ParsedExpr::Const(name) if name == "Nat"));
            }
            _ => panic!("Expected Notation decl, got {:?}", decls[0]),
        }
    }

    #[test]
    fn test_parse_notation_usage() {
        let src = "inductive Nat where\n| zero : Nat\n\nnotation \"NatAlias\" => Nat\n\ndef test1 : NatAlias := zero\n";
        let mut p = Parser::new(src);
        match p.parse_file() {
            Ok(decls) => {
                assert_eq!(decls.len(), 3);
                assert!(matches!(&decls[0], ParsedDecl::Inductive { .. }));
                assert!(matches!(&decls[1], ParsedDecl::Notation { .. }));
                assert!(matches!(&decls[2], ParsedDecl::Def { .. }));
            }
            Err(e) => {
                let rem: String = p.input[p.pos..].iter().collect();
                panic!("Parse error: {} at pos={} rem={:?}", e, p.pos, rem);
            }
        }
    }

    #[test]
    fn test_parse_calc_single_step() {
        let e = parse("calc (Nat)\n  a = b := h");
        match e {
            ParsedExpr::Calc(ty, steps) => {
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert_eq!(steps.len(), 1);
                assert!(matches!(&steps[0].0, ParsedExpr::Const(name) if name == "a"));
                assert!(matches!(&steps[0].1, ParsedExpr::Const(name) if name == "b"));
                assert!(matches!(&steps[0].2, ParsedExpr::Const(name) if name == "h"));
            }
            _ => panic!("Expected Calc, got {:?}", e),
        }
    }

    #[test]
    fn test_parse_calc_multi_step() {
        let e = parse("calc (Nat)\n  a = b := h1\n  _ = c := h2\n  _ = d := h3");
        match e {
            ParsedExpr::Calc(ty, steps) => {
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert_eq!(steps.len(), 3);
                // First step
                assert!(matches!(&steps[0].0, ParsedExpr::Const(name) if name == "a"));
                assert!(matches!(&steps[0].1, ParsedExpr::Const(name) if name == "b"));
                assert!(matches!(&steps[0].2, ParsedExpr::Const(name) if name == "h1"));
                // Second step (_ inferred as b)
                assert!(matches!(&steps[1].0, ParsedExpr::Const(name) if name == "b"));
                assert!(matches!(&steps[1].1, ParsedExpr::Const(name) if name == "c"));
                assert!(matches!(&steps[1].2, ParsedExpr::Const(name) if name == "h2"));
                // Third step (_ inferred as c)
                assert!(matches!(&steps[2].0, ParsedExpr::Const(name) if name == "c"));
                assert!(matches!(&steps[2].1, ParsedExpr::Const(name) if name == "d"));
                assert!(matches!(&steps[2].2, ParsedExpr::Const(name) if name == "h3"));
            }
            _ => panic!("Expected Calc, got {:?}", e),
        }
    }

    #[test]
    fn test_resolve_mk_with_quot_and_frac() {
        use crate::repl::Repl;
        let mut repl = Repl::new();
        repl.set_quiet(true);
        repl.check_files(&["lib/Nat.cic", "lib/Int.cic", "lib/Frac.cic"]).unwrap();
        let (env, _tc, bindings, _infix, _notations) = repl.into_state();

        // Check that mk is NOT in env_bindings as bare name
        assert!(bindings.get("mk").is_none(), "bare 'mk' should not be in env_bindings");

        // Quot.mk is a primitive (QuotInfo), not a ConstructorInfo,
        // so resolve_ctor_name only sees Frac.mk and resolves unambiguously.
        assert_eq!(env.resolve_ctor_name("mk"), Some(Name::new("Frac").extend("mk")));
    }

    #[test]
    fn test_parse_tactic_block_multiline_exact() {
        let src = "theorem t : Nat := by\n  exact\n    let x : Nat := zero in\n    x\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        match &decls[0] {
            ParsedDecl::Theorem { value, .. } => {
                match value {
                    ParsedExpr::TacticBlock(tactics) => {
                        assert_eq!(tactics.len(), 1, "expected single multiline exact tactic, got {:?}", tactics);
                        assert!(tactics[0].starts_with("exact"));
                        assert!(tactics[0].contains("let x"));
                    }
                    _ => panic!("Expected TacticBlock"),
                }
            }
            _ => panic!("Expected theorem"),
        }
    }

    #[test]
    fn test_parse_tactic_block_have_no_in() {
        let src = "theorem t : Nat := by\n  have h : Nat := zero\n  exact h\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        match &decls[0] {
            ParsedDecl::Theorem { value, .. } => {
                match value {
                    ParsedExpr::TacticBlock(tactics) => {
                        assert_eq!(tactics.len(), 2, "expected two tactics, got {:?}", tactics);
                        assert!(tactics[0].starts_with("have"));
                        assert!(tactics[1].starts_with("exact"));
                    }
                    _ => panic!("Expected TacticBlock"),
                }
            }
            _ => panic!("Expected theorem"),
        }
    }

    #[test]
    fn test_parse_fix_measure() {
        let src = "fix f (n : Nat) measure (fun n : Nat => n) => n";
        let mut p = Parser::new(src);
        let e = p.parse_expr().unwrap();
        assert!(matches!(e, ParsedExpr::Fix { name, param, .. } if name == "f" && param == "n"));
    }

    #[test]
    fn test_fix_measure_factorial() {
        use crate::repl::Repl;
        let mut repl = Repl::new();
        repl.set_quiet(true);
        repl.check_files(&["lib/Nat.cic", "lib/Eq.cic", "lib/Order.cic", "lib/test_fix.cic"]).unwrap();
    }

    #[test]
    fn test_match_structural_recursion() {
        use crate::repl::Repl;
        let mut repl = Repl::new();
        repl.set_quiet(true);
        repl.check_files(&["lib/Nat.cic", "lib/Eq.cic", "lib/Decimal.cic", "lib/test_match_structural.cic"]).unwrap();
    }
}
