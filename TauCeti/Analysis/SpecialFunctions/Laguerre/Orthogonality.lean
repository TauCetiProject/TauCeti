/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Laguerre.Measure
public import TauCeti.RingTheory.Polynomial.Laguerre.Basic
import Mathlib.Algebra.Group.ForwardDiff
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The orthogonality relation of the Laguerre polynomials

For real `α > -1` the generalized Laguerre polynomials `Lₙ^{(α)} = Polynomial.laguerre α n` are
orthogonal for the weight `x ^ α * exp (-x)` on `(0, ∞)`, that is, against the Laguerre measure
`Polynomial.laguerreMeasure α` (DLMF 18.2.1 with Table 18.3.1):

`∫ Lₘ^{(α)}(x) Lₙ^{(α)}(x) x ^ α e^{-x} dx = δₘₙ Γ(n + α + 1) / n!`.

This is the relation that makes the normalized Laguerre polynomials an orthonormal family of
`L²(laguerreMeasure α)`; with the exact degree `Polynomial.degree_laguerre` and the finite
exponential moments `Polynomial.integrable_exp_mul_abs_laguerreMeasure` it is what the polynomial
completeness theorem needs to make them a Hilbert basis.

The proof computes the integral of `Lₙ^{(α)}` against every polynomial of degree at most `n`.
Expanding `Lₙ^{(α)}` in monomials and integrating each against the measure, whose moments are
`Γ(k + α + 1)`, gives for every `j`

`∫ x ^ j Lₙ^{(α)}(x) x ^ α e^{-x} dx = Γ(n + α + 1) / n! * ∑ₖ (-1)ᵏ (n choose k) (α + 1 + k)ⱼ`,

because `(α + k + 1)_{n-k} Γ(α + k + 1) = Γ(n + α + 1)` and `Γ(j + k + α + 1) = (α + k + 1)ⱼ Γ(α +
k + 1)`. The alternating binomial sum is `(-1)ⁿ` times the `n`-th forward difference at `α + 1` of
the rising factorial `t ↦ (t)ⱼ`, a polynomial of degree `j` with leading coefficient `1`, so it
vanishes for `j < n` and equals `(-1)ⁿ n!` for `j = n`. Hence `Lₙ^{(α)}` is orthogonal to every
polynomial of lower degree, and the integral of `Lₙ^{(α)}` against a polynomial `q` of degree at
most `n` is `(-1)ⁿ Γ(n + α + 1)` times the coefficient of `Xⁿ` in `q`. At `q = Lₙ^{(α)}`, whose
coefficient of `Xⁿ` is `(-1)ⁿ / n!`, this is the norm `Γ(n + α + 1) / n!`.

## Main statements

* `Polynomial.integral_eval_mul_laguerre_laguerreMeasure`: for `q` of degree at most `n`,
  `∫ q Lₙ^{(α)} = (-1)ⁿ Γ(n + α + 1) q.coeff n`.
* `Polynomial.integral_eval_mul_laguerre_laguerreMeasure_of_degree_lt`: `Lₙ^{(α)}` is orthogonal
  to every polynomial of degree less than `n`.
* `Polynomial.integral_laguerre_mul_laguerre_laguerreMeasure`: the orthogonality relation
  `∫ Lₘ^{(α)} Lₙ^{(α)} = if m = n then Γ(n + α + 1) / n! else 0`.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov>, 18.2.1 and
  Table 18.3.1 (the weight and the norms `hₙ`), 18.5.12 (the explicit sum).
* G. Szegő, *Orthogonal Polynomials*, Ch. V, §5.1.
-/

public section

open MeasureTheory Real

namespace Polynomial

variable {α : ℝ}

/-- One term of the monomial expansion of `∫ x ^ j Lₙ^{(α)}(x) dμ`: the coefficient of `Xᵏ` in
`Lₙ^{(α)}` times the moment `Γ(j + k + α + 1)` is a multiple of `Γ(n + α + 1) / n!`, written in
the shape of the summands of `fwdDiff_iter_eq_sum_shift`. -/
private theorem coeff_laguerre_mul_Gamma (hα : -1 < α) (j : ℕ) {n k : ℕ} (hk : k ≤ n) :
    (laguerre α n).coeff k * Gamma ((j + k : ℕ) + α + 1) =
      (-1) ^ n * (Gamma (n + α + 1) / n.factorial) *
        (((-1 : ℤ) ^ (n - k) * n.choose k) • (ascPochhammer ℝ j).eval (α + 1 + k • (1 : ℝ))) := by
  set s : ℝ := α + k + 1
  have hs : 0 < s := by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
  -- `Γ(s + m) = (s)ₘ Γ(s)` for the positive base `s = α + k + 1`
  have hΓ (m : ℕ) : Gamma (s + m) = (ascPochhammer ℝ m).eval s * Gamma s := by
    rw [← Gamma_add_nat_div_Gamma_eq s fun i hi => by
        have : (0 : ℝ) ≤ i := i.cast_nonneg; linarith,
      div_mul_cancel₀ _ (Gamma_pos_of_pos hs).ne']
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h₁ : ((j + k : ℕ) : ℝ) + α + 1 = s + j := by push_cast; ring
  have h₂ : ((k + d : ℕ) : ℝ) + α + 1 = s + d := by push_cast; ring
  have h₃ : α + 1 + k • (1 : ℝ) = s := by rw [nsmul_one]; ring
  have hfact : ((k + d).choose k : ℝ) * k.factorial * d.factorial = (k + d).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k d)
    rw [Nat.add_sub_cancel_left] at this
    exact_mod_cast this
  rw [coeff_laguerre_of_le α hk, h₁, h₂, h₃, hΓ, hΓ, Nat.add_sub_cancel_left, ← eval_eq_smeval,
    Rat.smul_def, zsmul_eq_mul, ← hfact]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : (d.factorial : ℝ) ≠ 0 := by positivity
  have : ((k + d).choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right k d)).ne'
  rw [pow_add]
  rcases neg_one_pow_eq_or ℝ d with h | h <;> rw [h] <;> field_simp <;> ring

/-- The integral of `x ^ j Lₙ^{(α)}(x)` against the Laguerre measure is `(-1)ⁿ Γ(n + α + 1) / n!`
times the `n`-th forward difference at `α + 1` of the rising factorial `t ↦ (t)ⱼ`. -/
private theorem integral_pow_mul_laguerre_laguerreMeasure (hα : -1 < α) (j n : ℕ) :
    ∫ x, x ^ j * (laguerre α n).eval x ∂laguerreMeasure α =
      (-1) ^ n * (Gamma (n + α + 1) / n.factorial) *
        (fwdDiff (1 : ℝ))^[n] (ascPochhammer ℝ j).eval (α + 1) := by
  have hint (i : ℕ) : -1 < (i : ℝ) + α := by have : (0 : ℝ) ≤ i := i.cast_nonneg; linarith
  have hL (x : ℝ) : x ^ j * (laguerre α n).eval x =
      ∑ k ∈ Finset.range (n + 1), (laguerre α n).coeff k * x ^ (j + k) := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_laguerre_le α n)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hL]
  rw [integral_finsetSum _ fun k _ => (integrable_pow_laguerreMeasure (hint _)).const_mul _,
    fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_const_mul, integral_pow_laguerreMeasure (hint _),
    coeff_laguerre_mul_Gamma hα j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]

/-- The integral of `x ^ j Lₙ^{(α)}(x)` against the Laguerre measure for `j ≤ n`: it vanishes for
`j < n` and is `(-1)ⁿ Γ(n + α + 1)` for `j = n`. -/
private theorem integral_pow_mul_laguerre_laguerreMeasure_of_le (hα : -1 < α) {j n : ℕ}
    (hj : j ≤ n) :
    ∫ x, x ^ j * (laguerre α n).eval x ∂laguerreMeasure α =
      if j = n then (-1) ^ n * Gamma (n + α + 1) else 0 := by
  rw [integral_pow_mul_laguerre_laguerreMeasure hα]
  split_ifs with h
  · subst h
    have h := congrFun (ascPochhammer ℝ j).fwdDiff_iter_degree_eq_factorial (α + 1)
    rw [ascPochhammer_natDegree, (monic_ascPochhammer ℝ j).leadingCoeff] at h
    have : (j.factorial : ℝ) ≠ 0 := by positivity
    rw [h, one_smul, Pi.natCast_apply]
    field_simp
  · rw [(ascPochhammer ℝ j).fwdDiff_iter_eq_zero_of_degree_lt
      (by rw [ascPochhammer_natDegree]; omega)]
    simp

/-- **Integrals of polynomials against a Laguerre polynomial.** For real `α > -1` and a real
polynomial `q` of degree at most `n`, the integral of `q Lₙ^{(α)}` against the Laguerre measure is
`(-1)ⁿ Γ(n + α + 1)` times the coefficient of `Xⁿ` in `q`. -/
theorem integral_eval_mul_laguerre_laguerreMeasure (hα : -1 < α) {q : ℝ[X]} {n : ℕ}
    (hq : q.natDegree ≤ n) :
    ∫ x, q.eval x * (laguerre α n).eval x ∂laguerreMeasure α =
      (-1) ^ n * Gamma (n + α + 1) * q.coeff n := by
  have hq' (x : ℝ) : q.eval x * (laguerre α n).eval x =
      ∑ i ∈ Finset.range (n + 1), q.coeff i * (x ^ i * (laguerre α n).eval x) := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hq']
  rw [integral_finsetSum _ fun i _ =>
      ((integrable_eval_laguerreMeasure hα (X ^ i * laguerre α n)).const_mul (q.coeff i)).congr
        (ae_of_all _ fun x => by dsimp only; rw [eval_mul, eval_pow, eval_X])]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single_of_mem n (Finset.self_mem_range_succ n) fun i hi hin => ?_,
    integral_pow_mul_laguerre_laguerreMeasure_of_le hα le_rfl, ite_eq_left rfl, mul_comm]
  rw [integral_pow_mul_laguerre_laguerreMeasure_of_le hα
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)), ite_eq_right hin, mul_zero]

/-- For real `α > -1`, the Laguerre polynomial `Lₙ^{(α)}` is orthogonal, against the Laguerre
measure, to every real polynomial of degree less than `n`. -/
theorem integral_eval_mul_laguerre_laguerreMeasure_of_degree_lt (hα : -1 < α) {q : ℝ[X]} {n : ℕ}
    (hq : q.degree < n) :
    ∫ x, q.eval x * (laguerre α n).eval x ∂laguerreMeasure α = 0 := by
  rw [integral_eval_mul_laguerre_laguerreMeasure hα (natDegree_le_of_degree_le hq.le),
    coeff_eq_zero_of_degree_lt hq, mul_zero]

/-- **The orthogonality relation of the Laguerre polynomials** (DLMF 18.2.1 with Table 18.3.1).
For real `α > -1`,
`∫ Lₘ^{(α)}(x) Lₙ^{(α)}(x) x ^ α e^{-x} dx = if m = n then Γ(n + α + 1) / n! else 0`
over `(0, ∞)`. -/
theorem integral_laguerre_mul_laguerre_laguerreMeasure (hα : -1 < α) (m n : ℕ) :
    ∫ x, (laguerre α m).eval x * (laguerre α n).eval x ∂laguerreMeasure α =
      if m = n then Gamma (n + α + 1) / n.factorial else 0 := by
  rcases lt_trichotomy m n with hmn | rfl | hmn
  · rw [ite_eq_right hmn.ne, integral_eval_mul_laguerre_laguerreMeasure_of_degree_lt hα
      ((degree_laguerre_le α m).trans_lt (by exact_mod_cast hmn))]
  · rw [ite_eq_left rfl, integral_eval_mul_laguerre_laguerreMeasure hα (natDegree_laguerre_le α m),
      coeff_laguerre_self]
    have : (m.factorial : ℝ) ≠ 0 := by positivity
    rw [map_div₀, map_pow, map_neg, map_one, map_natCast]
    field_simp
    rw [← pow_mul, pow_mul', neg_one_sq, one_pow, one_mul]
  · simp_rw [mul_comm ((laguerre α m).eval _)]
    rw [ite_eq_right hmn.ne', integral_eval_mul_laguerre_laguerreMeasure_of_degree_lt hα
      ((degree_laguerre_le α n).trans_lt (by exact_mod_cast hmn))]

end Polynomial
