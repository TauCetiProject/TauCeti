/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.MarkovTrace
public import TauCeti.Algebra.TemperleyLieb.Star
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.LinearCombination

/-!
# Positivity of the Markov trace for loop values at least two

For a real loop value `δ`, the analytic adjoint and a Markov trace `tr` give the Hermitian forms
`(x, y) ↦ tr n (x⋆ * y)` on the Temperley–Lieb algebras. This file proves that these forms are
positive semidefinite on every number of strands when `δ ≥ 2`. This is the half of the sufficiency
direction of Jones's positivity theorem covering the continuous part `[2, ∞)` of the admissible
loop parameters; the discrete series `2 cos (π / m)` is not treated here.

The proof uses the spin model of `TauCeti.TemperleyLieb.markovTrace`. Write `δ = r + r⁻¹` with
`r > 0` and take `q = -r`, so that `δ = -(q + q⁻¹)`. In the spin model the cup vector is the cap
covector scaled by `-q = r`, so each generator acts by the real symmetric matrix `r · capᵀ cap`,
and the spin representation is a star representation into matrices with the conjugate transpose.
The weights of the spin configurations are products of `r` and `r⁻¹`, hence positive. So the
trace of `x⋆ * x` is the weighted sum `∑ₛ wₛ ∑ₜ |A t s|²` over the entries of the matrix `A` of `x`,
which is nonnegative. By uniqueness of the Markov trace the same holds for every Markov trace.

The general statements are over a commutative star-ordered ring `R` that is an ordered ring,
such as `ℝ` or `ℂ` with its partial order `ComplexOrder`, for a unit `q` with `0 ≤ -q`.

## Main results

* `TauCeti.TemperleyLieb.conjTranspose_spinGenerator`: for self-adjoint `q`, the generator
  matrices of the spin model are self-adjoint.
* `TauCeti.TemperleyLieb.spinRep_star`: for self-adjoint `q`, the spin representation carries
  the analytic adjoint to the conjugate transpose.
* `TauCeti.TemperleyLieb.markovTrace_star_mul_self_nonneg`: for `0 ≤ -q`, the spin-model trace of
  `x⋆ * x` is nonnegative.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg`: the same for every Markov trace
  at the loop value `-(q + q⁻¹)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_two_le`: over `ℂ`, for real
  `δ ≥ 2` the Hermitian forms of a Markov trace are positive semidefinite on every number of
  strands.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Theorem 4.3.17.
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
-/

public section

open Matrix

namespace TauCeti.TemperleyLieb

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} {n : ℕ}

section Star

/-- For self-adjoint `q`, the cap covector of the spin model has self-adjoint entries. -/
@[simp] theorem star_spinCap (hq : IsSelfAdjoint (q : R)) (x y : Bool) :
    star (spinCap q x y) = spinCap q x y := by
  cases x <;> cases y <;> simp [(Ring.inverse_unit q ▸ hq.ringInverse).star_eq]

/-- For self-adjoint `q`, the generator matrices of the spin model are self-adjoint: each is
`-q` times the matrix `capᵀ cap` on the two strands it caps. -/
@[simp] theorem conjTranspose_spinGenerator (hq : IsSelfAdjoint (q : R)) (j k : Fin n) :
    (spinGenerator q j k)ᴴ = spinGenerator q j k := by
  ext s t
  rw [conjTranspose_apply, spinGenerator_apply, spinGenerator_apply]
  simp only [eq_comm (a := s _)]
  split_ifs
  · rw [star_mul, star_spinCap hq, spinCup_eq_neg_mul_spinCap, star_mul, star_spinCap hq,
      star_neg, hq.star_eq, spinCup_eq_neg_mul_spinCap]
    ring
  · exact star_zero R

/-- For self-adjoint `q`, the spin representation carries the analytic adjoint of the
Temperley–Lieb algebra to the conjugate transpose of matrices. -/
@[simp] theorem spinRep_star {δ : R} [Fact (IsSelfAdjoint δ)] (hq : IsSelfAdjoint (q : R))
    (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) (x : TemperleyLieb R δ n) :
    spinRep q hδ (star x) = (spinRep q hδ x)ᴴ := by
  refine (map_star_iff.mpr fun i ↦ ?_) x
  rw [spinRep_e, IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_spinGenerator hq]

end Star

section Order

variable [PartialOrder R] [StarOrderedRing R] [IsOrderedRing R]

/-- For `0 ≤ -q`, the weight of every spin configuration is nonnegative: it is a product of the
single-spin weights `-q` and `-q⁻¹`, both nonnegative. -/
theorem spinWeight_nonneg (hq : 0 ≤ -(q : R)) (s : Fin n → Bool) : 0 ≤ spinWeight q s := by
  have hsa : IsSelfAdjoint (q : R) := by simpa using hq.isSelfAdjoint.neg
  have hinv : 0 ≤ -((q⁻¹ : Rˣ) : R) := by
    have h := (Ring.inverse_unit q ▸ hsa.ringInverse).conjugate_nonneg hq
    rwa [mul_neg, Units.inv_mul, neg_mul, one_mul] at h
  rw [spinWeight_def]
  refine Finset.prod_nonneg fun l _ ↦ ?_
  cases s l
  · simpa using hinv
  · simpa using hq

/-- **Positivity of the spin-model trace.** For a unit `q` with `0 ≤ -q`, the Markov trace
`TauCeti.TemperleyLieb.markovTrace` at the loop value `δ = -(q + q⁻¹)` is nonnegative on every
element of the form `x⋆ * x`. -/
theorem markovTrace_star_mul_self_nonneg {δ : R} [Fact (IsSelfAdjoint δ)] (hq : 0 ≤ -(q : R))
    (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) (x : TemperleyLieb R δ n) :
    0 ≤ markovTrace q hδ (star x * x) := by
  have hsa : IsSelfAdjoint (q : R) := by simpa using hq.isSelfAdjoint.neg
  -- The trace of `D * Aᴴ * A` is the trace of `A * D * Aᴴ`, with `D` a nonnegative diagonal.
  rw [markovTrace_apply, map_mul, spinRep_star hsa, ← mul_assoc, trace_mul_comm, ← mul_assoc]
  exact ((posSemidef_diagonal_iff.2 (spinWeight_nonneg hq)).mul_mul_conjTranspose_same
    _).trace_nonneg

/-- **Positivity of a Markov trace.** For a unit `q` with `0 ≤ -q`, every Markov trace at the
loop value `δ = -(q + q⁻¹)` is nonnegative on every element of the form `x⋆ * x`. -/
theorem IsMarkovTrace.map_star_mul_self_nonneg {δ : R} [Fact (IsSelfAdjoint δ)]
    {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr) (hq : 0 ≤ -(q : R))
    (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) (x : TemperleyLieb R δ n) :
    0 ≤ tr n (star x * x) := by
  rw [htr.eq_markovTrace q hδ]
  exact markovTrace_star_mul_self_nonneg hq hδ x

end Order

open scoped ComplexOrder

/-- **Positivity for loop values at least two.** For a real loop value `δ ≥ 2`, the Hermitian
forms `(x, y) ↦ tr n (x⋆ * y)` of a Markov trace on the complex Temperley–Lieb algebras are
positive semidefinite on every number of strands. -/
theorem IsMarkovTrace.map_star_mul_self_nonneg_of_two_le {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 2 ≤ δ) (x : TemperleyLieb ℂ (δ : ℂ) n) : 0 ≤ tr n (star x * x) := by
  -- Write `δ = r + r⁻¹` with `r = (δ + √(δ ^ 2 - 4)) / 2 > 0`, and take `q = -r`.
  set r : ℝ := (δ + √(δ ^ 2 - 4)) / 2 with hr_def
  have hr : 0 < r := by positivity
  have hrinv : r⁻¹ = δ - r := by
    refine inv_eq_of_mul_eq_one_right ?_
    have hsq := Real.sq_sqrt (show 0 ≤ δ ^ 2 - 4 by nlinarith)
    rw [hr_def]
    linear_combination -hsq / 4
  let q : ℂˣ := Units.mk0 (-(r : ℂ)) (by simpa using hr.ne')
  refine htr.map_star_mul_self_nonneg (q := q) (by simpa [q] using hr.le) ?_ x
  simp only [q, Units.val_inv_eq_inv_val, Units.val_mk0, inv_neg, neg_add, neg_neg,
    ← Complex.ofReal_inv, hrinv, Complex.ofReal_sub]
  ring

end TauCeti.TemperleyLieb
