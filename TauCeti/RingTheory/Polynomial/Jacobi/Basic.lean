/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Binomial

import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Algebra.NatCast

/-!
# The Jacobi polynomials

This file defines the Jacobi polynomials `Pₙ^{(α,β)}` over a commutative `ℚ`-algebra `R`, with
the parameters `α β : R`, by the explicit sum (DLMF 18.5.8)

  `Pₙ^{(α,β)} = 2⁻ⁿ ∑ k ≤ n, (n+β choose n-k) (n+α choose k) (X - 1)^{n-k} (X + 1)^k`,

where the generalized binomial coefficients are written with rising factorials,
`(n+β choose n-k) = (β + k + 1)_{n-k} / (n-k)!` and `(n+α choose k) = (α + n - k + 1)_k / k!`.
The rational factors act through `Algebra ℚ R`, so no division in `R` is needed, and `ℝ` and `ℂ`
are instances rather than special cases. The parameter `β` travels with `X - 1` and `α` with
`X + 1`; this pairing is the classical one, under which `Pₙ^{(α,β)}(1) = (α + 1)_n / n!`.

The Jacobi polynomials are the orthogonal polynomials for the weight `(1 - x)^α (1 + x)^β` on
`(-1, 1)`; up to normalization, Legendre (`α = β = 0`), Chebyshev (`α = β = -1/2`) and
Gegenbauer polynomials are specializations. This file develops the algebraic facts that the
orthogonality theory consumes.

## Main definitions and results

* `Polynomial.jacobi α β n`: the Jacobi polynomial `Pₙ^{(α,β)}`.
* `Polynomial.coeff_jacobi_self`: the coefficient of `X^n` is `(n + α + β + 1)_n / (2ⁿ n!)`,
  by the Chu–Vandermonde identity `Ring.descPochhammer_smeval_add`.
* `Polynomial.degree_jacobi`: `Pₙ^{(α,β)}` has degree `n` as soon as `(n + α + β + 1)_n ≠ 0`, and
  `Polynomial.degree_jacobi_real`: over `ℝ` this holds for all `n` when `-2 < α + β`, which
  covers the orthogonality range `-1 < α`, `-1 < β`.
* `Polynomial.jacobi_comp_neg_X`: the reflection symmetry `Pₙ^{(α,β)}(-X) = (-1)ⁿ Pₙ^{(β,α)}(X)`.
* `Polynomial.eval_one_jacobi`, `Polynomial.eval_neg_one_jacobi`: the values at `±1`.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov/18>: 18.5.8,
  Tables 18.3.1 and 18.6.1.
* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, Chapter IV.
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The Jacobi polynomial `Pₙ^{(α,β)}` over a commutative `ℚ`-algebra (DLMF 18.5.8):
`2⁻ⁿ ∑ k ≤ n, ((β + k + 1)_{n-k} (α + n - k + 1)_k / ((n-k)! k!)) (X - 1)^{n-k} (X + 1)^k`.
The factor `(β + k + 1)_{n-k} / (n-k)!` is `(n+β).choose (n-k)` and `(α + n - k + 1)_k / k!` is
`(n+α).choose k`, so `β` travels with `X - 1` and `α` with `X + 1`. -/
noncomputable def jacobi (α β : R) (n : ℕ) : R[X] :=
  ((1 : ℚ) / 2 ^ n) • ∑ k ∈ Finset.range (n + 1),
    (((1 : ℚ) / ((n - k).factorial * k.factorial)) •
      ((ascPochhammer R (n - k)).smeval (β + k + 1) *
        (ascPochhammer R k).smeval (α + (n - k : ℕ) + 1))) • ((X - 1) ^ (n - k) * (X + 1) ^ k)

/-- The defining explicit sum of the Jacobi polynomial `Pₙ^{(α,β)}`. -/
theorem jacobi_def (α β : R) (n : ℕ) :
    jacobi α β n = ((1 : ℚ) / 2 ^ n) • ∑ k ∈ Finset.range (n + 1),
      (((1 : ℚ) / ((n - k).factorial * k.factorial)) •
        ((ascPochhammer R (n - k)).smeval (β + k + 1) *
          (ascPochhammer R k).smeval (α + (n - k : ℕ) + 1))) •
        ((X - 1) ^ (n - k) * (X + 1) ^ k) := by
  rw [jacobi]

omit [Algebra ℚ R] in
private lemma coeff_X_sub_one_pow_mul_X_add_one_pow (m k : ℕ) :
    ((X - 1 : R[X]) ^ m * (X + 1) ^ k).coeff (m + k) = 1 := by
  have hd₁ : ((X - 1 : R[X]) ^ m).natDegree ≤ m := by compute_degree
  have hd₂ : ((X + 1 : R[X]) ^ k).natDegree ≤ k := by compute_degree
  have h₁ := coeff_pow_of_natDegree_le (p := (X - 1 : R[X])) (m := m) (n := 1) (by compute_degree)
  have h₂ := coeff_pow_of_natDegree_le (p := (X + 1 : R[X])) (m := k) (n := 1) (by compute_degree)
  rw [mul_one] at h₁ h₂
  rw [coeff_mul_add_eq_of_natDegree_le hd₁ hd₂, h₁, h₂]
  simp [coeff_one]

omit [Algebra ℚ R] in
private lemma ascPochhammer_smeval_eq_descPochhammer (r s : R) (m : ℕ) (h : s = r - m + 1) :
    (ascPochhammer R m).smeval s = (descPochhammer ℤ m).smeval r := by
  rw [descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_cast, h]

/-- The Jacobi polynomial `Pₙ^{(α,β)}` has natural degree at most `n`. -/
theorem natDegree_jacobi_le (α β : R) (n : ℕ) : (jacobi α β n).natDegree ≤ n := by
  rw [jacobi_def]
  refine (natDegree_smul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun k hk => ?_)
  refine (natDegree_smul_le _ _).trans ?_
  have : ((X - 1 : R[X]) ^ (n - k) * (X + 1) ^ k).natDegree ≤ n - k + k := by compute_degree
  rwa [Nat.sub_add_cancel (by simpa [Nat.lt_succ_iff] using hk)] at this

/-- The coefficient of `X^n` in `Pₙ^{(α,β)}` is `(n + α + β + 1)_n / (2ⁿ n!)`, that is
`(2n+α+β).choose n / 2ⁿ`. -/
theorem coeff_jacobi_self (α β : R) (n : ℕ) :
    (jacobi α β n).coeff n =
      ((1 : ℚ) / (2 ^ n * n.factorial)) • (ascPochhammer R n).smeval (n + α + β + 1) := by
  rw [ascPochhammer_smeval_eq_descPochhammer ((α + n) + (β + n)) _ _ (by ring),
    Ring.descPochhammer_smeval_add _ (Commute.all _ _), Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    smul_sum, jacobi_def, AddMonoidAlgebra.coeff_smul_apply, finsetSum_coeff, smul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
  have hc := coeff_X_sub_one_pow_mul_X_add_one_pow (R := R) (n - k) k
  rw [Nat.sub_add_cancel hkn] at hc
  rw [AddMonoidAlgebra.coeff_smul_apply, hc, smul_eq_mul, mul_one,
    ascPochhammer_smeval_eq_descPochhammer (β + n) _ _ (by push_cast [Nat.cast_sub hkn]; ring),
    ascPochhammer_smeval_eq_descPochhammer (α + n) _ _ (by push_cast [Nat.cast_sub hkn]; ring),
    mul_comm (descPochhammer ℤ (n - k) |>.smeval _), smul_smul]
  dsimp only
  rw [← map_natCast (algebraMap ℚ R) (n.choose k), ← Algebra.smul_def, smul_smul]
  congr 1
  have hc0 : (n.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [← Nat.choose_mul_factorial_mul_factorial hkn]
  push_cast
  field_simp

/-- The Jacobi polynomial `Pₙ^{(α,β)}` has degree at most `n`. -/
theorem degree_jacobi_le (α β : R) (n : ℕ) : (jacobi α β n).degree ≤ n :=
  degree_le_of_natDegree_le (natDegree_jacobi_le α β n)

private lemma coeff_jacobi_self_ne_zero {α β : R} {n : ℕ}
    (h : (ascPochhammer R n).smeval (n + α + β + 1) ≠ 0) : (jacobi α β n).coeff n ≠ 0 := by
  rw [coeff_jacobi_self]
  exact smul_ne_zero (by positivity) h

/-- The Jacobi polynomial `Pₙ^{(α,β)}` has degree `n` as soon as its candidate leading coefficient
`(n + α + β + 1)_n / (2ⁿ n!)` is nonzero. Over a domain, with `z = n + α + β + 1`, the rising
factorial `(z)_n` vanishes exactly when `n ≥ 1` and `z ∈ {0, -1, …, -(n-1)}`; for instance
`jacobi (-1) (-1) 1 = 0`. -/
theorem degree_jacobi (α β : R) (n : ℕ)
    (h : (ascPochhammer R n).smeval (n + α + β + 1) ≠ 0) : (jacobi α β n).degree = n :=
  degree_eq_of_le_of_coeff_ne_zero (degree_jacobi_le α β n) (coeff_jacobi_self_ne_zero h)

/-- The Jacobi polynomial `Pₙ^{(α,β)}` has natural degree `n` as soon as `(n + α + β + 1)_n ≠ 0`. -/
theorem natDegree_jacobi (α β : R) (n : ℕ)
    (h : (ascPochhammer R n).smeval (n + α + β + 1) ≠ 0) : (jacobi α β n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_jacobi_le α β n) (coeff_jacobi_self_ne_zero h)

/-- The leading coefficient of `Pₙ^{(α,β)}` is `(n + α + β + 1)_n / (2ⁿ n!)` whenever this value is
nonzero (DLMF Table 18.3.1). -/
theorem leadingCoeff_jacobi (α β : R) (n : ℕ)
    (h : (ascPochhammer R n).smeval (n + α + β + 1) ≠ 0) :
    (jacobi α β n).leadingCoeff =
      ((1 : ℚ) / (2 ^ n * n.factorial)) • (ascPochhammer R n).smeval (n + α + β + 1) := by
  rw [leadingCoeff, natDegree_jacobi α β n h, coeff_jacobi_self]

/-- Over `ℝ`, the Jacobi polynomial `Pₙ^{(α,β)}` has degree `n` for every `n` as soon as
`-2 < α + β`, in particular on the orthogonality range `-1 < α`, `-1 < β`. -/
theorem degree_jacobi_real {α β : ℝ} (h : -2 < α + β) (n : ℕ) :
    (jacobi α β n).degree = n := by
  refine degree_jacobi α β n ?_
  rw [← eval_eq_smeval]
  rcases n with _ | n
  · simp
  · exact (ascPochhammer_pos _ _ (by push_cast; linarith)).ne'

/-- The Jacobi polynomial of degree `0` is `1`. -/
@[simp]
theorem jacobi_zero (α β : R) : jacobi α β 0 = 1 := by
  simp [jacobi_def]

/-- The Jacobi polynomial of degree `1`: `P₁^{(α,β)} = (α + 1) + (α + β + 2) (X - 1) / 2`. -/
theorem jacobi_one (α β : R) :
    jacobi α β 1 = C (α + 1) + ((1 : ℚ) / 2) • (C (α + β + 2) * (X - 1)) := by
  have h : C (algebraMap ℚ R 2⁻¹) * 2 = (1 : R[X]) := by
    rw [← C_ofNat, ← C_mul, TauCeti.algebraMap_inv_mul_ofNat two_ne_zero, C_1]
  simp only [jacobi_def, pow_one, one_div, Nat.reduceAdd, mul_inv_rev, ascPochhammer_smeval_cast,
    smul_assoc, sum_range_succ, range_one, sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    tsub_zero, Nat.factorial_one, mul_one, ascPochhammer_one, Nat.cast_zero, add_zero, smeval_X,
    ascPochhammer_zero, smeval_one, pow_zero, one_smul, tsub_self, one_mul, smul_add, map_add,
    map_one]
  simp only [Algebra.smul_def, algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, C_add,
    C_1, C_ofNat]
  linear_combination (C α + 1) * h

/-- The value of `Pₙ^{(α,β)}` at `1` is `(α + 1)_n / n!`, that is `(n+α).choose n`
(DLMF Table 18.6.1). -/
@[simp]
theorem eval_one_jacobi (α β : R) (n : ℕ) :
    (jacobi α β n).eval 1 = ((1 : ℚ) / n.factorial) • (ascPochhammer R n).smeval (α + 1) := by
  rw [jacobi_def, eval_smul, eval_finsetSum, sum_range_succ, sum_eq_zero fun k hk => ?_]
  · have h2 : ((1 : R) + 1) ^ n = algebraMap ℚ R (2 ^ n) := by
      rw [one_add_one_eq_two, map_pow, map_ofNat]
    simp only [eval_smul, eval_pow, eval_add, eval_X, eval_one,
      Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, ascPochhammer_zero,
      smeval_one, one_smul, Nat.cast_zero, add_zero, zero_add, smul_eq_mul, h2]
    rw [mul_comm _ (algebraMap ℚ R _), ← Algebra.smul_def, smul_smul]
    simp
  · have hk : n - k ≠ 0 := Nat.sub_ne_zero_of_lt (mem_range.1 hk)
    simp [eval_smul, zero_pow hk]

/-- The reflection symmetry of the Jacobi polynomials: `Pₙ^{(α,β)}(-X) = (-1)ⁿ Pₙ^{(β,α)}(X)`
(DLMF Table 18.6.1). It is the analogue of
`Polynomial.neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq`. -/
theorem jacobi_comp_neg_X (α β : R) (n : ℕ) :
    (jacobi α β n).comp (-X) = (-1 : R) ^ n • jacobi β α n := by
  rw [jacobi_def, jacobi_def, smul_comp, sum_comp]
  conv_rhs => rw [smul_comm ((-1 : R) ^ n) ((1 : ℚ) / 2 ^ n), smul_sum, ← sum_range_reflect]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
  rw [Nat.add_sub_cancel, Nat.sub_sub_self hkn, smul_comp, smul_comm ((-1 : R) ^ n),
    mul_comm (k.factorial : ℚ), mul_comm (ascPochhammer R k |>.smeval _)]
  congr 1
  have h3 : (-1 : R[X]) ^ n = (-1) ^ (n - k) * (-1) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  rw [smul_eq_C_mul, C_pow, C_neg, C_1, h3, mul_comp, pow_comp, pow_comp, sub_comp, add_comp,
    X_comp, one_comp]
  have h1 : (-X - 1 : R[X]) ^ (n - k) = (-1) ^ (n - k) * (X + 1) ^ (n - k) := by
    rw [← mul_pow]; ring
  have h2 : (-X + 1 : R[X]) ^ k = (-1) ^ k * (X - 1) ^ k := by
    rw [← mul_pow]; ring
  rw [h1, h2]
  ring

/-- The value of `Pₙ^{(α,β)}` at `-1` is `(-1)ⁿ (β + 1)_n / n!` (DLMF Table 18.6.1). -/
@[simp]
theorem eval_neg_one_jacobi (α β : R) (n : ℕ) :
    (jacobi α β n).eval (-1) =
      (-1) ^ n * ((1 : ℚ) / n.factorial) • (ascPochhammer R n).smeval (β + 1) := by
  simpa [eval_comp, eval_smul] using congrArg (eval 1) (jacobi_comp_neg_X α β n)

end Polynomial
