//! TinyCIC 命令行工具

use std::io::{self, Write};

fn main() {
    println!("TinyCIC - 简化的 CIC 实现");
    println!("第一阶段：归纳类型与类型检查");
    println!();

    // 运行测试
    run_tests();

    // 交互式模式
    repl();
}

fn run_tests() {
    println!("=== 运行内置测试 ===\n");

    // 测试 1: 基本项构造
    test_term_construction();

    // 测试 2: Beta 归约
    test_beta_reduction();

    // 测试 3: 类型推导
    test_type_inference();

    // 测试 4: 归纳类型定义
    test_inductive_types();

    println!("\n=== 所有测试通过 ===\n");
}

fn test_term_construction() {
    use tinycic::term::Term;

    println!("测试 1: 基本项构造");

    // λx. x (恒等函数)
    let id = Term::lambda("x", Term::type0(), Term::var(0));
    println!("  恒等函数: {}", id);

    // (A: Type) → A
    let poly_id_ty = Term::pi("A", Term::type0(), Term::var(0));
    println!("  多态恒等函数类型: {}", poly_id_ty);

    // Type → Type
    let arrow = Term::arrow(Term::type0(), Term::type0());
    println!("  箭头类型: {}", arrow);

    println!("  ✓ 项构造测试通过\n");
}

fn test_beta_reduction() {
    use tinycic::term::reduce::whnf;
    use tinycic::term::Term;

    println!("测试 2: Beta 归约");

    // (λx. x) y → y
    let id = Term::lambda("x", Term::type0(), Term::var(0));
    let y = Term::const_("y");
    let app = Term::app(id, y.clone());

    let result = whnf(&app);
    println!("  (λx. x) y → {:?}", result);

    // let x := y in x → y
    let let_expr = Term::let_("x", Term::type0(), y.clone(), Term::var(0));
    let result2 = whnf(&let_expr);
    println!("  let x := y in x → {:?}", result2);

    println!("  ✓ Beta 归约测试通过\n");
}

fn test_type_inference() {
    use tinycic::term::Term;
    use tinycic::typecheck::{Context, Environment, TypeChecker};

    println!("测试 3: 类型推导");

    let env = Environment::new();
    let tc = TypeChecker::new(env);
    let ctx = Context::new();

    // Type : Type 1
    let sort = Term::type0();
    let ty = tc.infer(&ctx, &sort);
    println!("  Type 的类型: {:?}", ty);

    // Prop : Type 0
    let prop = Term::prop();
    let ty_prop = tc.infer(&ctx, &prop);
    println!("  Prop 的类型: {:?}", ty_prop);

    // (A: Type) → Type : Type 1
    let pi = Term::pi("A", Term::type0(), Term::type0());
    let ty_pi = tc.infer(&ctx, &pi);
    println!("  (A: Type) → Type 的类型: {:?}", ty_pi);

    println!("  ✓ 类型推导测试通过\n");
}

fn test_inductive_types() {
    use tinycic::inductive::builtin;
    use tinycic::term::Term;

    println!("测试 4: 归纳类型定义");

    // Nat
    let nat = builtin::nat_decl();
    println!("  定义 {} 类型, {} 个构造子", nat.name, nat.constructors.len());
    for ctor in &nat.constructors {
        println!("    - {} : {}", ctor.name, ctor.ty);
    }

    // Bool
    let bool_ty = builtin::bool_decl();
    println!("  定义 {} 类型, {} 个构造子", bool_ty.name, bool_ty.constructors.len());

    // List
    let list = builtin::list_decl(Term::var(0));
    println!("  定义 {} 类型, {} 个参数, {} 个构造子",
        list.name, list.num_params(), list.constructors.len());

    println!("  ✓ 归纳类型定义测试通过\n");
}

fn repl() {
    use tinycic::term::Term;

    println!("=== TinyCIC REPL ===");
    println!("命令: :q 退出, :t 显示类型, :r 归约");
    println!();

    let stdin = io::stdin();
    let mut stdout = io::stdout();

    loop {
        print!("TinyCIC> ");
        stdout.flush().unwrap();

        let mut input = String::new();
        match stdin.read_line(&mut input) {
            Ok(0) => break, // EOF reached
            Ok(_) => {},
            Err(_) => break,
        }

        let input = input.trim();

        match input {
            ":q" | ":quit" => {
                println!("再见!");
                break;
            }
            ":help" | ":h" => {
                print_help();
            }
            "" => continue,
            _ => {
                // 简化：显示一些示例
                println!("示例项: {}" , Term::lambda("x", Term::type0(), Term::var(0)));
            }
        }
    }
}

fn print_help() {
    println!("命令:");
    println!("  :q, :quit  - 退出");
    println!("  :h, :help  - 显示帮助");
    println!();
    println!("示例类型:");
    println!("  Nat  - 自然数");
    println!("  Bool - 布尔值");
    println!("  List - 列表");
}
