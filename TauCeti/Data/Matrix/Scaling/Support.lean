/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Scaling.Basic

/-!
# Diagonal scalings of a nonnegative kernel with zero entries

Let `K : Matrix ι κ ℝ` be a nonnegative kernel, possibly with zero entries, and let `a : ι → ℝ`
and `b : κ → ℝ` be prescribed row and column sums. A diagonal scaling `u i * K i j * v j` of `K`
by strictly positive factors vanishes exactly where `K` does. This file proves the converse
criterion: such a scaling with row sums `a` and column sums `b` exists exactly when some
nonnegative matrix with these row and column sums has the zero pattern of `K`
(`Matrix.exists_sinkhorn_scaling_iff`). For a strictly positive kernel and strictly positive
marginals of equal total mass the product matrix `a i * b j / ∑ k, a k` is such a matrix, which is
the case of the Sinkhorn–Knopp theorem `Matrix.exists_sinkhorn_scaling`. The zero pattern of `K`
can rule a scaling out: for `K = !![1, 1; 0, 1]` and `a = b = 1` the only nonnegative matrix with
these row and column sums vanishing where `K` does is the identity, which vanishes at the entry
`(0, 1)` where `K` does not, so `K` has no such scaling.

The scaled matrix is found as a minimiser of the relative entropy `Matrix.relEntropy · K` among
the nonnegative matrices with the prescribed row and column sums that vanish wherever `K` does.
These form a compact convex set, nonempty as soon as the transport polytope meets the support of
`K` (`Matrix.exists_relEntropy_minOn_support`). If some feasible matrix has the zero pattern of
`K`, then the minimiser is a diagonal scaling of `K` by strictly positive factors
(`Matrix.exists_isDiagonalScaling_of_relEntropy_minOn_support` in
`TauCeti.Data.Matrix.Scaling.Basic`): the minimiser has the largest support among the competitors,
and the first-order condition on that support splits `log P - log K` into a function of the row plus
a function of the column.

## Main results

* `Matrix.exists_relEntropy_minOn_support`: the relative entropy against `K` attains a minimum on
  the nonnegative matrices with given row and column sums vanishing where `K` does, as soon as
  there is one such matrix.
* `Matrix.exists_sinkhorn_scaling_iff`: **the scaling criterion** for a nonnegative kernel.

## References

* M. V. Menon, *Matrix links, an extremization problem, and the reduction of a non-negative
  matrix to one with prescribed row and column sums*, Canad. J. Math. 20 (1968), 225--232.
* R. A. Brualdi, *Convex sets of non-negative matrices*, Canad. J. Math. 20 (1968), 144--157.
* M. Idel, *A review of matrix scaling and Sinkhorn's normal form for matrices and positive
  maps*, arXiv:1609.06349 (2016), Section 3.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probab. 3 (1975), 146--158, for the support of a relative-entropy minimiser.
-/

public section

open scoped BigOperators

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Minimisers supported where the kernel is -/

/-- The relative entropy against `K` attains a minimum on the nonnegative matrices with row sums
`a` and column sums `b` that vanish wherever `K` does, as soon as there is one such matrix. -/
theorem exists_relEntropy_minOn_support (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (hfeas : ∃ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) ∧ HasMarginals Q a b ∧
      ∀ i j, K i j = 0 → Q i j = 0) :
    ∃ P : Matrix ι κ ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b ∧
      (∀ i j, K i j = 0 → P i j = 0) ∧
      ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
        (∀ i j, K i j = 0 → Q i j = 0) → relEntropy P K ≤ relEntropy Q K := by
  have hclosed : IsClosed {P : Matrix ι κ ℝ | ∀ i j, K i j = 0 → P i j = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop) continuous_const
  obtain ⟨Q, hQ0, hQa, hQK⟩ := hfeas
  obtain ⟨P, ⟨⟨hP0, hPa⟩, hPK⟩, hmin⟩ :=
    ((isCompact_setOf_nonneg_hasMarginals a b).inter_right hclosed).exists_isMinOn
      ⟨Q, ⟨hQ0, hQa⟩, hQK⟩ (continuous_relEntropy K).continuousOn
  exact ⟨P, hP0, hPa, hPK, fun Q hQ0 hQa hQK => isMinOn_iff.mp hmin Q ⟨⟨hQ0, hQa⟩, hQK⟩⟩

/-! ### The scaling criterion -/

/-- **The scaling criterion** for a nonnegative kernel: a nonnegative matrix `K` admits strictly
positive row factors `u` and column factors `v` such that the diagonal scaling `u i * K i j * v j`
has row sums `a` and column sums `b` exactly when some nonnegative matrix with row sums `a` and
column sums `b` vanishes exactly where `K` does.

There is no hypothesis on `a` and `b`: their nonnegativity and equal total mass follow from either
side. -/
theorem exists_sinkhorn_scaling_iff {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 ≤ K i j) {a : ι → ℝ}
    {b : κ → ℝ} :
    (∃ (u : ι → ℝ) (v : κ → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      (∀ i, ∑ j, u i * K i j * v j = a i) ∧ ∀ j, ∑ i, u i * K i j * v j = b j) ↔
      ∃ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) ∧ (∀ i j, Q i j = 0 ↔ K i j = 0) ∧
        HasMarginals Q a b := by
  constructor
  · rintro ⟨u, v, hu, hv, ha, hb⟩
    refine ⟨fun i j => u i * K i j * v j,
      fun i j => mul_nonneg (mul_nonneg (hu i).le (hK i j)) (hv j).le, fun i j => ?_,
      (hasMarginals_def _ _ _).2 ⟨ha, hb⟩⟩
    simp [(hu i).ne', (hv j).ne']
  · rintro ⟨Q, hQ, hQK, hQa⟩
    obtain ⟨P, hP, hPa, hPK, hmin⟩ :=
      exists_relEntropy_minOn_support K a b ⟨Q, hQ, hQa, fun i j h => (hQK i j).2 h⟩
    obtain ⟨u, v, hu, hv, hPuv⟩ :=
      exists_isDiagonalScaling_of_relEntropy_minOn_support hK hP hPa hPK hmin hQ hQa hQK
    rw [hasMarginals_def] at hPa
    rw [isDiagonalScaling_def] at hPuv
    refine ⟨u, v, hu, hv, fun i => ?_, fun j => ?_⟩
    · rw [← hPa.1 i]
      exact Finset.sum_congr rfl fun j _ => (hPuv i j).symm
    · rw [← hPa.2 j]
      exact Finset.sum_congr rfl fun i _ => (hPuv i j).symm

end Matrix
