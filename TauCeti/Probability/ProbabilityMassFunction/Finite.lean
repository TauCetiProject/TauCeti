/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.ProbabilityMassFunction.Marginal

/-!
# Finite sums for probability mass functions

This file records summation identities for probability mass functions: the total mass on a finite
type, a bound on weighted partial sums over any type, and the finite-sum specializations of the
marginal formulas of `TauCeti.Probability.ProbabilityMassFunction.Marginal`.

## Main results

* `PMF.sum_toReal_eq_one`: the real values of a PMF on a finite type sum to one.
* `PMF.sum_toReal_mul_le`: a weighted sum over a finset of a function bounded above by `M ≥ 0`
  on that finset is at most `M`.
* `PMF.map_fst_apply_fintype`, `PMF.map_snd_apply_fintype`: the two marginals of a product PMF are
  its row and column sums whenever the factor being summed over is finite.
* `PMF.map_fst_eq_iff_fintype`, `PMF.map_snd_eq_iff_fintype`: characterizations of prescribed
  marginals by those finite sums.
-/

public section

noncomputable section

open scoped BigOperators ENNReal

universe u v

namespace PMF

variable {ι : Type u} {κ : Type v}

/-- The real values of a probability mass function on a finite type sum to one. -/
@[simp]
theorem sum_toReal_eq_one [Fintype ι] (μ : PMF ι) : ∑ i, (μ i).toReal = 1 := by
  have h : ∑ i, μ i = 1 := (tsum_fintype fun i ↦ μ i).symm.trans μ.tsum_coe
  rw [← ENNReal.toReal_sum fun i _ ↦ μ.apply_ne_top i, h, ENNReal.toReal_one]

/-- A `p`-weighted sum over a finset `s` of a function bounded above by `M ≥ 0` on `s` is at
most `M`. -/
theorem sum_toReal_mul_le (p : PMF ι) (s : Finset ι) {ψ : ι → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hψ : ∀ y ∈ s, ψ y ≤ M) : ∑ y ∈ s, (p y).toReal * ψ y ≤ M := by
  have hs : ∑ y ∈ s, (p y).toReal ≤ 1 := by
    rw [← ENNReal.toReal_sum fun y _ ↦ p.apply_ne_top y, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top (p.tsum_coe ▸ sum_le_tsum s)
  calc
    ∑ y ∈ s, (p y).toReal * ψ y ≤ ∑ y ∈ s, (p y).toReal * M :=
      Finset.sum_le_sum fun y hy ↦ mul_le_mul_of_nonneg_left (hψ y hy) ENNReal.toReal_nonneg
    _ = (∑ y ∈ s, (p y).toReal) * M := by rw [Finset.sum_mul]
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right hs hM0
    _ = M := one_mul M

variable (π : PMF (ι × κ))

/-- The first marginal of a product PMF with finite second factor is obtained by summing each row
of its matrix of point masses. -/
theorem map_fst_apply_fintype [Fintype κ] (i : ι) : π.map Prod.fst i = ∑ j, π (i, j) := by
  rw [map_fst_apply, tsum_fintype]

/-- A product PMF with finite second factor has first marginal `μ` exactly when its row sums are
`μ`. -/
theorem map_fst_eq_iff_fintype [Fintype κ] (μ : PMF ι) :
    π.map Prod.fst = μ ↔ ∀ i, ∑ j, π (i, j) = μ i := by
  rw [map_fst_eq_iff]
  simp only [tsum_fintype]

/-- The second marginal of a product PMF with finite first factor is obtained by summing each
column of its matrix of point masses. -/
theorem map_snd_apply_fintype [Fintype ι] (j : κ) : π.map Prod.snd j = ∑ i, π (i, j) := by
  rw [map_snd_apply, tsum_fintype]

/-- A product PMF with finite first factor has second marginal `ν` exactly when its column sums are
`ν`. -/
theorem map_snd_eq_iff_fintype [Fintype ι] (ν : PMF κ) :
    π.map Prod.snd = ν ↔ ∀ j, ∑ i, π (i, j) = ν j := by
  rw [map_snd_eq_iff]
  simp only [tsum_fintype]

end PMF
