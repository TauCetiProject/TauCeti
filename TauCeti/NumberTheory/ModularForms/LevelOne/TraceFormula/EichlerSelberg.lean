/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.EichlerShimura
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Formula

/-!
# The Eichler–Selberg trace formula at level one

For even `k ≥ 4` and `n ≥ 1`, the trace of the Hecke operator `Tₙ` on the cusp forms of weight `k`
on `SL(2, ℤ)` is

`tr(Tₙ | S_k(SL(2, ℤ))) = -½ ∑_{t² ≤ 4n} P_k(t, n) H(4n - t²) - ½ ∑_{dd' = n} min(d, d')^(k-1)`,

where `H` is the Hurwitz class number, with `H(0) = -1/12`, and the weight `P_k(t, n)` is the
value at `t` of the second-kind Dickson polynomial of degree `k - 2` and parameter `n`, the
coefficient of `x^(k-2)` in `(1 - t x + n x²)⁻¹`.

This is Popa and Zagier's proof. Their explicit element `popaZagierElement` of the group ring of
the integral matrices of determinant `n` acts on the degree-`w` binary forms `V_w`, `w = k - 2`,
and its trace there is the class-number expression
`σ_{k-1}(n) - ∑ min(d, d')^(k-1) - ∑ P_k(t, n) H(4n - t²)`
(see `trace_periodAction_popaZagierElement_eq_sigma_sub_min_sub_hurwitzClassNumber` in
`TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Formula`). By Popa and Zagier's trace
reduction from `V_w` to the period polynomials `W_w` and the Eichler–Shimura isomorphism
`W_w ≃ₗ M_k × S_k`, where `popaZagierElement` acts as `Tₙ × Tₙ`, the same ambient trace is
`2 tr(Tₙ | S_k) + σ_{k-1}(n)`
(`TauCeti.TraceFormulaMatrixModule.trace_heckeTCuspLevelOne_eq_trace_popaZagierElement`).
Comparing the two gives the formula.

## Main results

* `TauCeti.trace_heckeTCuspLevelOne_eq_neg_hurwitzClassNumber_sub_min`: the Eichler–Selberg trace
  formula for `Tₙ` on `S_k(SL(2, ℤ))`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, Theorem 1.
* D. Zagier, *The Eichler–Selberg trace formula on SL₂(ℤ)*, appendix to S. Lang,
  *Introduction to Modular Forms*, for the normalization `H(0) = -1/12`.
-/

public section

open Polynomial TauCeti.TraceFormulaMatrixModule
open scoped MatrixGroups

namespace TauCeti

variable {k : ℤ} {w : ℕ}

/-- **The Eichler–Selberg trace formula at level one.** For even `k = w + 2 ≥ 4` and `n ≥ 1`, the
trace of `Tₙ` on the cusp forms of weight `k` on `SL(2, ℤ)` is

`tr(Tₙ | S_k) = -½ ∑_{t² ≤ 4n} H(4n - t²) P_k(t, n) - ½ ∑_{dd' = n} min(d, d')^(k-1)`,

with Hurwitz class numbers normalized by `H(0) = -1/12` and `P_k(t, n) = (dickson 2 n w).eval t`.
The sum over `t` runs over the integers with `t² ≤ 4n`, written as a filter of `[-4n, 4n]`. -/
theorem trace_heckeTCuspLevelOne_eq_neg_hurwitzClassNumber_sub_min (hk : k = w + 2)
    (hw : Even w) (hw₀ : w ≠ 0) (n : ℕ) [NeZero n] :
    LinearMap.trace ℂ _ (heckeTCuspLevelOne k n) =
      -(∑ t ∈ (Finset.Icc (-4 * (n : ℤ)) (4 * n)).filter (fun t ↦ t ^ 2 ≤ 4 * (n : ℤ)),
          (hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat : ℂ) *
            (dickson 2 (n : ℂ) w).eval (t : ℂ)) / 2 -
        (∑ p ∈ n.divisorsAntidiagonal, ((min p.1 p.2 : ℕ) : ℂ) ^ (w + 1)) / 2 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [trace_heckeTCuspLevelOne_eq_trace_popaZagierElement hk hw hw₀ n,
    trace_periodAction_popaZagierElement_eq_sigma_sub_min_sub_hurwitzClassNumber
      (K := ℂ) n hn w hw]
  ring

end TauCeti
