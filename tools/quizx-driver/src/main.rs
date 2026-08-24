use quizx::circuit::*;
use quizx::decompose::{BssWithCatsDriver, Decomposer};
use quizx::graph::*;
use quizx::vec_graph::Graph;
use std::env;
use std::time::Instant;

fn main() {
    let args: Vec<_> = env::args().collect();
    let file = &args[1];
    let k: usize = args[2].parse().unwrap();
    let c = Circuit::from_file(file).unwrap();
    let n = c.num_qubits();
    assert_eq!(n, 3 * k);
    let mut g: Graph = c.to_graph();
    let ins: Vec<BasisElem> = (0..n)
        .map(|i| if i < 2 * k { BasisElem::X0 } else { BasisElem::Z0 })
        .collect();
    g.plug_inputs(&ins);
    let outs: Vec<BasisElem> = (0..n)
        .map(|i| {
            if i < 2 * k {
                BasisElem::X0
            } else if i == 2 * k {
                BasisElem::Z1
            } else {
                BasisElem::Z0
            }
        })
        .collect();
    g.plug_outputs(&outs);
    quizx::simplify::full_simp(&mut g);
    println!("tcount after full_simp: {}", g.tcount());
    let mut d = Decomposer::new(&g);
    d.with_full_simp();
    let t = Instant::now();
    let d = d.decompose_parallel(&BssWithCatsDriver { random_t: false });
    println!(
        "scalar: {} terms: {} time: {:.2?}",
        d.scalar(),
        d.nterms,
        t.elapsed()
    );
}
