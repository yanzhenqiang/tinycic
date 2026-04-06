# TinyCIC vs Lean 4 对比分析

## 1. Term/Expr 数据结构对比

### Lean 4 的 Expr
```cpp
enum class expr_kind { BVar, FVar, MVar, Sort, Const, App, Lambda, Pi, Let, Lit, MData, Proj };
```

- **BVar**: Bound variable (de Bruijn 索引)
- **FVar**: Free variable (局部变量，用 Name 标识)
- **MVar**: Meta variable (用于 elaboration)
- **Sort**: 宇宙层级
- **Const**: 全局常量
- **App**: 函数应用
- **Lambda**: λ 抽象
- **Pi**: 依赖函数类型 (∀)
- **Let**: let 绑定
- **Lit**: 字面量 (Nat/String)
- **MData**: 元数据
- **Proj**: 投影

### TinyCIC 的 Term
```rust
pub enum Term {
    Var(DeBruijn),      // 对应 BVar
    Sort(Level),        // 对应 Sort
    Const(Name),        // 对应 Const
    Pi { ... },         // 对应 Pi
    Lambda { ... },     // 对应 Lambda
    App { ... },        // 对应 App
    Let { ... },        // 对应 Let
    Inductive { ... },  // Lean 4 中没有，用 Const 表示
    Constructor { ... },// Lean 4 中没有，用 Const 表示
    Elim { ... },       // Lean 4 中没有，用 Const 表示
}
```

**差异**：
- TinyCIC 缺少 FVar、MVar、Lit、MData、Proj
- TinyCIC 显式区分 Inductive/Constructor/Elim，Lean 4 都用 Const

## 2. 替换 (Substitution) 对比

### Lean 4 的核心函数
```cpp
// instantiate.cpp
expr instantiate(expr const & e, unsigned n, expr const * s);
expr instantiate_rev(expr const & e, unsigned n, expr const * s);
```

关键实现细节：
1. 使用 `replace` 通用函数，配合 lambda 回调
2. 检查 `get_loose_bvar_range` 来提前返回（优化）
3. 使用 `lift_loose_bvars` 在绑定上下文中提升变量
4. 处理 `offset` 来跟踪嵌套绑定深度

### TinyCIC 的实现
```rust
// subst.rs - 需要改进
impl Term {
    pub fn subst(&self, var_idx: u32, value: &Rc<Term>) -> Rc<Term>
    pub fn lift(&self, cutoff: u32, amount: u32) -> Rc<Term>
}
```

**需要改进**：
- 添加 `has_loose_bvars` 检查来优化
- 确保 lift 在 subst 进入绑定上下文时正确应用
- 处理多个变量同时替换的情况

## 3. WHNF (Weak Head Normal Form) 对比

### Lean 4 的实现 (type_checker.cpp:641)
```cpp
expr type_checker::whnf(expr const & e) {
    // 直接返回的情况
    switch (e.kind()) {
    case expr_kind::BVar: case expr_kind::Sort: case expr_kind::MVar: case expr_kind::Pi:
    case expr_kind::Lit:
        return e;
    // ...
    }
    
    // 检查缓存
    auto it = m_st->m_whnf.find(e);
    if (it != m_st->m_whnf.end())
        return it->second;
    
    // 主循环：whnf_core + 各种归约
    expr t = e;
    while (true) {
        expr t1 = whnf_core(t);
        if (auto v = reduce_native(env(), t1)) { ... }
        else if (auto v = reduce_nat(t1)) { ... }
        else if (auto next_t = unfold_definition(t1)) { ... }
        else { ... }
    }
}
```

### Lean 4 的 whnf_core (type_checker.cpp:401)
处理：
1. MData: 递归到内部表达式
2. FVar: 查找 let 绑定的值并展开
3. App: Beta 归约 + 递归器归约
4. Let: Zeta 归约 (instantiate let_value)
5. Proj: 投影归约

### TinyCIC 的实现
```rust
pub fn whnf(&self, term: &Rc<Term>) -> Whnf {
    match term.as_ref() {
        Term::App { func, arg } => {
            // Beta 归约
            if let Term::Lambda { body, .. } = func_whnf {
                let reduced = body.subst_zero(arg);
                self.whnf_with_steps(&reduced, steps + 1)
            }
        }
        Term::Let { value, body, .. } => {
            // Zeta 归约
            let reduced = body.subst_zero(value);
            self.whnf_with_steps(&reduced, steps + 1)
        }
        Term::Elim { ... } => {
            // 递归器归约 (简化实现)
        }
        // 其他情况已经是 WHNF
    }
}
```

**需要改进**：
- 添加缓存机制
- 添加 nat 字面量归约
- 完善递归器归约逻辑
- 处理 definition 展开

## 4. 类型检查 (Type Inference) 对比

### Lean 4 的核心函数 (type_checker.cpp:270)
```cpp
expr type_checker::infer_type_core(expr const & e, bool infer_only) {
    switch (e.kind()) {
    case expr_kind::BVar:   lean_unreachable(); ...
    case expr_kind::FVar:   r = infer_fvar(e); break;
    case expr_kind::MVar:   lean_unreachable(); ...
    case expr_kind::Sort:   r = mk_sort(mk_succ(sort_level(e))); break;
    case expr_kind::Const:  r = infer_constant(e, infer_only); break;
    case expr_kind::App:    r = infer_app(e, infer_only); break;
    case expr_kind::Lambda: r = infer_lambda(e, infer_only); break;
    case expr_kind::Pi:     r = infer_pi(e, infer_only); break;
    case expr_kind::Let:    r = infer_let(e, infer_only); break;
    case expr_kind::Proj:   r = infer_proj(e, infer_only); break;
    // ...
    }
}
```

### Lean 4 的 infer_app (type_checker.cpp:163)
```cpp
expr type_checker::infer_app(expr const & e, bool infer_only) {
    expr f_type = ensure_pi_core(infer_type_core(app_fn(e), infer_only), e);
    expr a_type = infer_type_core(app_arg(e), infer_only);
    expr d_type = binding_domain(f_type);
    if (!is_def_eq(a_type, d_type))
        throw ...; // 类型不匹配
    return instantiate(binding_body(f_type), app_arg(e));
}
```

### TinyCIC 的实现
```rust
fn infer_app(&self, ctx: &Context, func: &Rc<Term>, arg: &Rc<Term>) 
    -> TcResult<Rc<Term>> {
    let func_ty = self.infer(ctx, func)?;
    match self.whnf(&func_ty).as_ref() {
        Term::Pi { domain, codomain, .. } => {
            self.check(ctx, arg, &domain)?;
            Ok(codomain.subst_zero(arg))
        }
        _ => Err(TypeError::ExpectedFunction { found: func_ty }),
    }
}
```

**基本一致**，但需要添加 caching。

## 5. Definitional Equality (is_def_eq) 对比

### Lean 4 的实现 (type_checker.cpp:1100+)
非常复杂的实现，包含：

1. **quick_is_def_eq**: 快速路径
   - 检查等价管理器缓存
   - 处理 Lambda/Pi/Sort/MData/Lit

2. **is_def_eq_core**: 主函数
   - 归约到 WHNF (cheap_proj=true)
   - proof irrelevance 检查
   - lazy_delta_reduction
   - 常量比较
   - FVar 比较
   - 投影比较
   - 应用比较
   - eta 展开
   - eta 结构展开
   - 字符串字面量展开
   - 单位类型简化

3. **lazy_delta_reduction**: 延迟 delta 归约
   - 比较 reducibility hints
   - 尝试参数比较优化
   - 逐步展开定义

### TinyCIC 的实现
```rust
pub fn convertible(&self, t1: &Rc<Term>, t2: &Rc<Term>) -> bool {
    let nf1 = nf(t1);
    let nf2 = nf(t2);
    self.alpha_eq(&nf1, &nf2)
}
```

**严重不足**：
- 只使用完全归约 + alpha 等价
- 缺少 lazy delta reduction
- 缺少 eta 展开/结构展开
- 缺少 proof irrelevance
- 没有缓存机制

## 6. 正性检查 (Positivity Check) 对比

### Lean 4 的实现 (inductive.cpp:393)
```cpp
void check_positivity(expr t, name const & cnstr_name, int arg_idx) {
    t = whnf(t);
    if (!has_ind_occ(t)) {
        // nonrecursive argument - ok
    } else if (is_pi(t)) {
        if (has_ind_occ(binding_domain(t)))
            throw ...; // 非正出现错误
        expr local = mk_local_decl_for(t);
        check_positivity(instantiate(binding_body(t), local), ...);
    } else if (is_valid_ind_app(t)) {
        // recursive argument - ok
    } else {
        throw ...; // 无效出现
    }
}
```

### TinyCIC 的实现
```rust
fn check_term(&self, term: &Rc<Term>, pos: Position) -> TcResult<()> {
    match term.as_ref() {
        Term::Const(name) => {
            if name == &self.inductive_name && pos == Position::Negative {
                Err(TypeError::NonPositiveOccurrence)
            } else { Ok(()) }
        }
        Term::Pi { domain, codomain, .. } => {
            self.check_term(domain, Position::Negative)?;
            self.check_term(codomain, pos)
        }
        // ...
    }
}
```

**差异**：
- Lean 4 先归约到 WHNF
- Lean 4 使用 `has_ind_occ` 辅助函数检查归纳类型出现
- Lean 4 使用 `is_valid_ind_app` 检查有效的归纳应用
- TinyCIC 需要添加 WHNF 归约和更严格的检查

## 7. 归纳类型声明处理对比

### Lean 4 的数据结构 (declaration.h)
```cpp
class inductive_type {
    name const & get_name() const;
    expr const & get_type() const;
    constructors const & get_cnstrs() const;
};

class inductive_val {
    unsigned get_nparams() const;
    unsigned get_nindices() const;
    names const & get_cnstrs() const;
    bool is_rec() const;
    bool is_unsafe() const;
    // ...
};

class constructor_val {
    name const & get_induct() const;
    unsigned get_nparams() const;
    unsigned get_nfields() const;
    // ...
};

class recursor_val {
    name const & get_major_induct() const;
    unsigned get_nparams() const;
    unsigned get_nmotives() const;
    unsigned get_nminors() const;
    unsigned get_major_idx() const;
    bool is_k() const;
    list_ref<recursor_rule> get_rules() const;
    // ...
};
```

### TinyCIC 的数据结构
```rust
pub struct InductiveDecl {
    pub name: Name,
    pub params: Vec<(Name, Rc<Term>)>,
    pub num_indices: usize,
    pub ty: Rc<Term>,
    pub constructors: Vec<ConstructorDecl>,
    pub is_recursive: bool,
}

pub struct InductiveInfo {
    pub num_params: usize,
    pub num_indices: usize,
    pub ty: Rc<Term>,
    pub constructors: Vec<(Name, Rc<Term>)>,
    pub recursor: Option<Rc<Term>>,
}
```

**基本一致**，但 Lean 4 的消去式信息更详细（motives, minors, major_idx 等）。

## 改进计划

### 高优先级
1. 修复 subst/lift 实现，确保在绑定上下文中正确处理变量提升
2. 改进 WHNF 实现，添加缓存和更完整的归约规则
3. 改进 is_def_eq 实现，添加 lazy delta reduction

### 中优先级
4. 完善正性检查，添加 WHNF 归约和更严格的检查
5. 添加 nat 字面量支持
6. 改进消去式生成

### 低优先级
7. 添加 FVar 支持（用于更精确的局部变量管理）
8. 添加 MData 支持（用于元数据/位置信息）
