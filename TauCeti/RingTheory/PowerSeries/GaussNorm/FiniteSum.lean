/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Common bounds for weighted coefficients of finite sums

The ultrametric inequality preserves a common bound for the weighted coefficients of a finite
family of series. This gives both boundedness and Gauss-norm bounds when assembling series.
-/

public section

namespace TauCeti

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R] {c : ℝ}

/-- A common bound for the weighted coefficients of degree `n` of finitely many series also
bounds that of their sum in an ultrametric ring, including the empty sum. -/
theorem norm_coeff_sum_mul_pow_le {ι : Type*} (s : Finset ι)
    (F : ι → PowerSeries R) (n : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ i ∈ s, ‖(F i).coeff n‖ * c ^ n ≤ A) :
    ‖(∑ i ∈ s, F i).coeff n‖ * c ^ n ≤ A := by
  rw [map_sum]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hA
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs
    fun i ↦ (F i).coeff n
  by_cases hcn : 0 ≤ c ^ n
  · exact (mul_le_mul_of_nonneg_right hle hcn).trans (hF i hi)
  · exact (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (le_of_not_ge hcn)).trans hA

end TauCeti
