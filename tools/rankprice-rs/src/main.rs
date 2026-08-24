// Rust engine for the rank-price residual enumeration.
// Reads a job file (core-rotated phase terms), enumerates u in 0..2^rho,
// per u builds the Z4 quadratic form on the rest variables and evaluates the
// exact Gauss sum; accumulates the exact Z[omega_8] numerator.
use rayon::prelude::*;
use serde::Deserialize;
use std::env;
use std::fs;
use std::time::Instant;

#[derive(Deserialize)]
struct Job {
    k: u32,
    rho: u32,
    nrest: u32,
    hpow: u32,
    base_const: u8,
    terms: Vec<(u64, u64, u8, u8)>, // (core_mask, rest_mask, const_bit, coeff mod 8)
}

#[derive(Clone, Copy, Default)]
struct Zi {
    a: i64,
    b: i64,
}
impl Zi {
    fn mul(self, o: Zi) -> Zi {
        Zi { a: self.a * o.a - self.b * o.b, b: self.a * o.b + self.b * o.a }
    }
}
const I_POW: [Zi; 4] = [
    Zi { a: 1, b: 0 },
    Zi { a: 0, b: 1 },
    Zi { a: -1, b: 0 },
    Zi { a: 0, b: -1 },
];

#[inline]
fn pair_idx(i: usize, j: usize) -> u64 {
    // i < j
    1u64 << (j * (j - 1) / 2 + i)
}

/// Exact sum over t in F2^m of i^{ sum r_i t_i + 2 sum_{i<j} B_ij t_i t_j } (mod 4),
/// B given as a triangular bitmask. Exact port of the Python gauss_z4.
fn gauss_z4(mut r: [u8; 12], mut bmask: u64, m: usize) -> Zi {
    let mut alive: u32 = ((1u64 << m) - 1) as u32;
    let mut fac = Zi { a: 1, b: 0 };
    let mut c: u8 = 0;
    while alive != 0 {
        let x = (31 - alive.leading_zeros()) as usize;
        alive &= !(1 << x);
        let a = r[x] & 3;
        // partners of x among alive
        let mut part: u32 = 0;
        let mut al = alive;
        while al != 0 {
            let j = al.trailing_zeros() as usize;
            al &= al - 1;
            let (lo, hi) = if j < x { (j, x) } else { (x, j) };
            if bmask & pair_idx(lo, hi) != 0 {
                part |= 1 << j;
                bmask &= !pair_idx(lo, hi);
            }
        }
        if a & 1 == 1 {
            fac = fac.mul(if a == 1 { Zi { a: 1, b: 1 } } else { Zi { a: 1, b: -1 } });
            let s: u8 = if a == 1 { 3 } else { 1 }; // -1 mod 4 = 3, +1
            let mut pl = part;
            while pl != 0 {
                let j = pl.trailing_zeros() as usize;
                pl &= pl - 1;
                r[j] = (r[j] + s) & 3;
            }
            // toggle pairs within part
            let mut pi = part;
            while pi != 0 {
                let j = pi.trailing_zeros() as usize;
                pi &= pi - 1;
                let mut pj = pi;
                while pj != 0 {
                    let j2 = pj.trailing_zeros() as usize;
                    pj &= pj - 1;
                    let (lo, hi) = if j < j2 { (j, j2) } else { (j2, j) };
                    bmask ^= pair_idx(lo, hi);
                }
            }
        } else {
            let want: u8 = if a == 0 { 0 } else { 1 };
            if part == 0 {
                if want == 1 {
                    return Zi { a: 0, b: 0 };
                }
                fac = Zi { a: fac.a * 2, b: fac.b * 2 };
                continue;
            }
            fac = Zi { a: fac.a * 2, b: fac.b * 2 };
            let p = part.trailing_zeros() as usize;
            let rest_part = part & !(1 << p);
            alive &= !(1 << p);
            let rp = r[p] & 3;
            if rp != 0 {
                c = (c + rp * want) & 3;
                let coef = (rp * (1u8.wrapping_sub(2 * want) as u8)) & 3;
                // note: (1 - 2*want) mod 4: want=0 -> 1, want=1 -> 3
                let coef = if want == 0 { rp & 3 } else { (4 - (rp & 3)) & 3 };
                let _ = coef;
                let cf = if want == 0 { rp & 3 } else { (4 - (rp & 3)) & 3 };
                let mut rl = rest_part;
                while rl != 0 {
                    let j = rl.trailing_zeros() as usize;
                    rl &= rl - 1;
                    r[j] = (r[j] + cf) & 3;
                }
                if cf & 1 == 1 {
                    let mut pi = rest_part;
                    while pi != 0 {
                        let j = pi.trailing_zeros() as usize;
                        pi &= pi - 1;
                        let mut pj = pi;
                        while pj != 0 {
                            let j2 = pj.trailing_zeros() as usize;
                            pj &= pj - 1;
                            let (lo, hi) = if j < j2 { (j, j2) } else { (j2, j) };
                            bmask ^= pair_idx(lo, hi);
                        }
                    }
                }
            }
            // cross terms 2*B[p][j]*t_p*t_j
            let mut al2 = alive;
            while al2 != 0 {
                let j = al2.trailing_zeros() as usize;
                al2 &= al2 - 1;
                let (lo, hi) = if j < p { (j, p) } else { (p, j) };
                if bmask & pair_idx(lo, hi) != 0 {
                    bmask &= !pair_idx(lo, hi);
                    if want == 1 {
                        r[j] = (r[j] + 2) & 3;
                    }
                    let mut rl = rest_part;
                    while rl != 0 {
                        let j2 = rl.trailing_zeros() as usize;
                        rl &= rl - 1;
                        if j2 == j {
                            r[j] = (r[j] + 2) & 3;
                        } else {
                            let (lo, hi) = if j < j2 { (j, j2) } else { (j2, j) };
                            bmask ^= pair_idx(lo, hi);
                        }
                    }
                }
            }
        }
    }
    fac.mul(I_POW[(c & 3) as usize])
}

fn main() {
    let args: Vec<_> = env::args().collect();
    let job: Job = serde_json::from_str(&fs::read_to_string(&args[1]).unwrap()).unwrap();
    let rho = job.rho;
    let m = job.nrest as usize;
    assert!(m <= 12);
    // sanity: odd coefficients only on pure-core terms
    for &(_, rest, _, coeff) in &job.terms {
        if rest != 0 {
            assert!(coeff % 2 == 0, "odd coefficient with rest part");
        }
    }
    let terms = job.terms.clone();
    let base_const = job.base_const;
    let t0 = Instant::now();
    let total: [i64; 4] = (0u64..(1u64 << rho))
        .into_par_iter()
        .fold(
            || [0i64; 4],
            |mut acc, u| {
                let mut cst: u32 = base_const as u32;
                let mut r = [0u8; 12];
                let mut bmask: u64 = 0;
                for &(core, rest, cbit, coeff) in &terms {
                    let nc = ((core & u).count_ones() & 1) as u8 ^ cbit;
                    if rest == 0 {
                        cst += (coeff as u32) * (nc as u32);
                    } else {
                        let eff: u8 = if nc == 1 { (8 - coeff) & 7 } else { coeff };
                        cst += (coeff as u32) * (nc as u32);
                        let q = (eff >> 1) & 3;
                        if q == 0 {
                            continue;
                        }
                        let mut rl = rest;
                        while rl != 0 {
                            let i = rl.trailing_zeros() as usize;
                            rl &= rl - 1;
                            r[i] = (r[i] + q) & 3;
                        }
                        if q & 1 == 1 {
                            let mut pi = rest;
                            while pi != 0 {
                                let i = pi.trailing_zeros() as usize;
                                pi &= pi - 1;
                                let mut pj = pi;
                                while pj != 0 {
                                    let j = pj.trailing_zeros() as usize;
                                    pj &= pj - 1;
                                    let (lo, hi) = if i < j { (i, j) } else { (j, i) };
                                    bmask ^= pair_idx(lo, hi);
                                }
                            }
                        }
                    }
                }
                let g = gauss_z4(r, bmask, m);
                // total += omega^{cst mod 8} * (g.a + g.b * i), i = omega^2
                let cm = (cst & 7) as usize;
                let (s, base) = if cm < 4 { (1i64, cm) } else { (-1i64, cm - 4) };
                // omega^base * (a + b w^2): contributes a at base, b at base+2 (with wrap sign)
                acc[base] += s * g.a;
                let b2 = base + 2;
                if b2 < 4 {
                    acc[b2] += s * g.b;
                } else {
                    acc[b2 - 4] -= s * g.b;
                }
                acc
            },
        )
        .reduce(|| [0i64; 4], |mut a, b| {
            for i in 0..4 {
                a[i] += b[i];
            }
            a
        });
    let dt = t0.elapsed();
    let w = std::f64::consts::FRAC_1_SQRT_2;
    let re = total[0] as f64 + w * (total[1] as f64 - total[3] as f64);
    let im = total[2] as f64 + w * (total[1] as f64 + total[3] as f64);
    let norm = 2f64.powf(job.hpow as f64 / 2.0);
    println!(
        "k={} rho={} numerator=({},{},{},{}) amp={:.12}+{:.12}i time={:.2?}",
        job.k, rho, total[0], total[1], total[2], total[3], re / norm, im / norm, dt
    );
}
