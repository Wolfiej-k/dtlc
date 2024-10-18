use dtlc::Expr;
use std::rc::Rc;

fn main() {
    // Polymorphic identity function.
    let poly_id = Rc::new(Expr::Lambda {
        var: "A".to_string(),
        ty: Rc::new(Expr::Star),
        body: Rc::new(Expr::Lambda {
            var: "x".to_string(),
            ty: Rc::new(Expr::Var("A".to_string())),
            body: Rc::new(Expr::Var("x".to_string())),
        }),
    });

    println!("id : {}", poly_id.type_check().expect(""));
    println!("id = {}\n", poly_id);

    // Commutativity of addition.
    let iter_nat = Rc::new(Expr::Lambda {
        var: "A".to_string(),
        ty: Rc::new(Expr::Star),
        body: Rc::new(Expr::Lambda {
            var: "z".to_string(),
            ty: Rc::new(Expr::Var("A".to_string())),
            body: Rc::new(Expr::Lambda {
                var: "s".to_string(),
                ty: Rc::new(Expr::Pi {
                    var: "x".to_string(),
                    ty: Rc::new(Expr::Var("A".to_string())),
                    body: Rc::new(Expr::Var("A".to_string())),
                }),
                body: Rc::new(Expr::Lambda {
                    var: "n".to_string(),
                    ty: Rc::new(Expr::Nat),
                    body: Rc::new(Expr::ElimNat(
                        Rc::new(Expr::Lambda {
                            var: "x".to_string(),
                            ty: Rc::new(Expr::Nat),
                            body: Rc::new(Expr::Var("A".to_string())),
                        }),
                        Rc::new(Expr::Var("z".to_string())),
                        Rc::new(Expr::Lambda {
                            var: "x".to_string(),
                            ty: Rc::new(Expr::Nat),
                            body: Rc::new(Expr::Var("s".to_string())),
                        }),
                        Rc::new(Expr::Var("n".to_string())),
                    )),
                }),
            }),
        }),
    });

    println!("iter_nat : {}", iter_nat.type_check().expect(""));
    println!("iter_nat = {}\n", iter_nat);

    let same = Rc::new(Expr::Lambda {
        var: "A".to_string(),
        ty: Rc::new(Expr::Star),
        body: Rc::new(Expr::Lambda {
            var: "a".to_string(),
            ty: Rc::new(Expr::Var("A".to_string())),
            body: Rc::new(Expr::Lambda {
                var: "b".to_string(),
                ty: Rc::new(Expr::Var("A".to_string())),
                body: Rc::new(Expr::Pi {
                    var: "P".to_string(),
                    ty: Rc::new(Expr::Pi {
                        var: "x".to_string(),
                        ty: Rc::new(Expr::Var("A".to_string())),
                        body: Rc::new(Expr::Star),
                    }),
                    body: Rc::new(Expr::Pi {
                        var: "x".to_string(),
                        ty: Rc::new(Expr::App(
                            Rc::new(Expr::Var("P".to_string())),
                            Rc::new(Expr::Var("a".to_string())),
                        )),
                        body: Rc::new(Expr::App(
                            Rc::new(Expr::Var("P".to_string())),
                            Rc::new(Expr::Var("b".to_string())),
                        )),
                    }),
                }),
            }),
        }),
    });

    println!("same : {}", same.type_check().expect(""));
    println!("same = {}\n", same);

    let refl = Rc::new(Expr::Lambda {
        var: "A".to_string(),
        ty: Rc::new(Expr::Star),
        body: Rc::new(Expr::Lambda {
            var: "x".to_string(),
            ty: Rc::new(Expr::Var("A".to_string())),
            body: Rc::new(Expr::Lambda {
                var: "P".to_string(),
                ty: Rc::new(Expr::Pi {
                    var: "a".to_string(),
                    ty: Rc::new(Expr::Var("A".to_string())),
                    body: Rc::new(Expr::Star),
                }),
                body: Rc::new(Expr::Lambda {
                    var: "z".to_string(),
                    ty: Rc::new(Expr::App(
                        Rc::new(Expr::Var("P".to_string())),
                        Rc::new(Expr::Var("x".to_string())),
                    )),
                    body: Rc::new(Expr::Var("z".to_string())),
                }),
            }),
        }),
    });

    println!("refl : {}", refl.type_check().expect(""));
    println!("refl = {}\n", refl);

    let sym = Rc::new(Expr::Lambda {
        var: "A".to_string(),
        ty: Rc::new(Expr::Star),
        body: Rc::new(Expr::Lambda {
            var: "x".to_string(),
            ty: Rc::new(Expr::Var("A".to_string())),
            body: Rc::new(Expr::Lambda {
                var: "y".to_string(),
                ty: Rc::new(Expr::Var("A".to_string())),
                body: Rc::new(Expr::Lambda {
                    var: "same_xy".to_string(),
                    ty: Rc::new(Expr::App(
                        Rc::new(Expr::App(
                            Rc::new(Expr::App(
                                Rc::clone(&same),
                                Rc::new(Expr::Var("A".to_string())),
                            )),
                            Rc::new(Expr::Var("x".to_string())),
                        )),
                        Rc::new(Expr::Var("y".to_string())),
                    )),
                    body: Rc::new(Expr::Lambda {
                        var: "P".to_string(),
                        ty: Rc::new(Expr::Pi {
                            var: "_".to_string(),
                            ty: Rc::new(Expr::Var("A".to_string())),
                            body: Rc::new(Expr::Star),
                        }),
                        body: Rc::new(Expr::App(
                            Rc::new(Expr::App(
                                Rc::new(Expr::Var("same_xy".to_string())),
                                Rc::new(Expr::Lambda {
                                    var: "z_1".to_string(),
                                    ty: Rc::new(Expr::Var("A".to_string())),
                                    body: Rc::new(Expr::Pi {
                                        var: "x_1".to_string(),
                                        ty: Rc::new(Expr::App(
                                            Rc::new(Expr::Var("P".to_string())),
                                            Rc::new(Expr::Var("z_1".to_string())),
                                        )),
                                        body: Rc::new(Expr::App(
                                            Rc::new(Expr::Var("P".to_string())),
                                            Rc::new(Expr::Var("x".to_string())),
                                        )),
                                    }),
                                }),
                            )),
                            Rc::new(Expr::Lambda {
                                var: "p".to_string(),
                                ty: Rc::new(Expr::App(
                                    Rc::new(Expr::Var("P".to_string())),
                                    Rc::new(Expr::Var("x".to_string())),
                                )),
                                body: Rc::new(Expr::Var("p".to_string())),
                            }),
                        )),
                    }),
                }),
            }),
        }),
    });

    println!("sym : {}", sym.type_check().expect(""));
    println!("sym = {}\n", sym);

    let trans = Rc::new(Expr::Lambda {
        var: "A".to_string(),
        ty: Rc::new(Expr::Star),
        body: Rc::new(Expr::Lambda {
            var: "x".to_string(),
            ty: Rc::new(Expr::Var("A".to_string())),
            body: Rc::new(Expr::Lambda {
                var: "y".to_string(),
                ty: Rc::new(Expr::Var("A".to_string())),
                body: Rc::new(Expr::Lambda {
                    var: "z".to_string(),
                    ty: Rc::new(Expr::Var("A".to_string())),
                    body: Rc::new(Expr::Lambda {
                        var: "pxy".to_string(),
                        ty: Rc::new(Expr::App(
                            Rc::new(Expr::App(
                                Rc::new(Expr::App(
                                    Rc::clone(&same),
                                    Rc::new(Expr::Var("A".to_string())),
                                )),
                                Rc::new(Expr::Var("x".to_string())),
                            )),
                            Rc::new(Expr::Var("y".to_string())),
                        )),
                        body: Rc::new(Expr::Lambda {
                            var: "pyz".to_string(),
                            ty: Rc::new(Expr::App(
                                Rc::new(Expr::App(
                                    Rc::new(Expr::App(
                                        Rc::clone(&same),
                                        Rc::new(Expr::Var("A".to_string())),
                                    )),
                                    Rc::new(Expr::Var("y".to_string())),
                                )),
                                Rc::new(Expr::Var("z".to_string())),
                            )),
                            body: Rc::new(Expr::Lambda {
                                var: "P".to_string(),
                                ty: Rc::new(Expr::Pi {
                                    var: "z1".to_string(),
                                    ty: Rc::new(Expr::Var("A".to_string())),
                                    body: Rc::new(Expr::Star),
                                }),
                                body: Rc::new(Expr::Lambda {
                                    var: "px".to_string(),
                                    ty: Rc::new(Expr::App(
                                        Rc::new(Expr::Var("P".to_string())),
                                        Rc::new(Expr::Var("x".to_string())),
                                    )),
                                    body: Rc::new(Expr::App(
                                        Rc::new(Expr::App(
                                            Rc::new(Expr::Var("pyz".to_string())),
                                            Rc::new(Expr::Var("P".to_string())),
                                        )),
                                        Rc::new(Expr::App(
                                            Rc::new(Expr::App(
                                                Rc::new(Expr::Var("pxy".to_string())),
                                                Rc::new(Expr::Var("P".to_string())),
                                            )),
                                            Rc::new(Expr::Var("px".to_string())),
                                        )),
                                    )),
                                }),
                            }),
                        }),
                    }),
                }),
            }),
        }),
    });

    println!("trans : {}", trans.type_check().expect(""));
    println!("trans = {}\n", trans);

    let suc = Rc::new(Expr::Lambda {
        var: "x".to_string(),
        ty: Rc::new(Expr::Nat),
        body: Rc::new(Expr::Succ(Rc::new(Expr::Var("x".to_string())))),
    });

    let plus = Rc::new(Expr::Lambda {
        var: "x".to_string(),
        ty: Rc::new(Expr::Nat),
        body: Rc::new(Expr::Lambda {
            var: "y".to_string(),
            ty: Rc::new(Expr::Nat),
            body: Rc::new(Expr::App(
                Rc::new(Expr::App(
                    Rc::new(Expr::App(
                        Rc::new(Expr::App(Rc::clone(&iter_nat), Rc::new(Expr::Nat))),
                        Rc::new(Expr::Var("y".to_string())),
                    )),
                    Rc::clone(&suc),
                )),
                Rc::new(Expr::Var("x".to_string())),
            )),
        }),
    });

    println!("plus : {}", plus.type_check().expect(""));
    println!("plus = {}\n", plus);

    let same_under_suc = Rc::new(Expr::Lambda {
        var: "x".to_string(),
        ty: Rc::new(Expr::Nat),
        body: Rc::new(Expr::Lambda {
            var: "y".to_string(),
            ty: Rc::new(Expr::Nat),
            body: Rc::new(Expr::Lambda {
                var: "z".to_string(),
                ty: Rc::new(Expr::App(
                    Rc::new(Expr::App(
                        Rc::new(Expr::App(Rc::clone(&same), Rc::new(Expr::Nat))),
                        Rc::new(Expr::Var("x".to_string())),
                    )),
                    Rc::new(Expr::Var("y".to_string())),
                )),
                body: Rc::new(Expr::Lambda {
                    var: "P".to_string(),
                    ty: Rc::new(Expr::Pi {
                        var: "_".to_string(),
                        ty: Rc::new(Expr::Nat),
                        body: Rc::new(Expr::Star),
                    }),
                    body: Rc::new(Expr::App(
                        Rc::new(Expr::Var("z".to_string())),
                        Rc::new(Expr::Lambda {
                            var: "z_1".to_string(),
                            ty: Rc::new(Expr::Nat),
                            body: Rc::new(Expr::App(
                                Rc::new(Expr::Var("P".to_string())),
                                Rc::new(Expr::Succ(Rc::new(Expr::Var("z_1".to_string())))),
                            )),
                        }),
                    )),
                }),
            }),
        }),
    });

    println!(
        "same_under_suc : {}",
        same_under_suc.type_check().expect("")
    );
    println!("same_under_suc = {}\n", same_under_suc);

    // Remaining cases:
    // plus_right_zero : (x : N) → Same N x (x + 0)
    // plus_right_zero x = natElim (λ (x : N) → Same N x (x + 0))
    //                             (λ P x → x)
    //                             (λ n x₁ P → x₁ (λ z → P (suc z)))
    //                             x

    // plus_right_suc : (x y : N) → Same N (suc (x + y)) (x + suc y)
    // plus_right_suc x y = natElim (λ (x : N) → Same N  (suc (x + y)) (x + suc y))
    //                             (λ P z → z)
    //                             (λ n z P → z (λ z₁ → P (suc z₁)))
    //                             x

    // plus_comm : (x y : N) → Same N (x + y) (y + x)
    // plus_comm x y = natElim (λ (x : N) → Same N (x + y) (y + x))
    //                         (plus_right_zero y)
    //                         (λ (n : N) (p : Same N (n + y) (y + n)) →
    //                         trans N (suc (n + y))
    //                                 (suc (y + n))
    //                                 (y + suc n)
    //                                 (same_under_suc (n + y) (y + n) p)
    //                                 (plus_right_suc y n))
    //                         x
}
