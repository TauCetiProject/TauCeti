/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# Quadratic corrections to the rescaling of formal exponentials

Subtracting `a² g` from `g(aX)` normalizes a rescaled formal exponential. At integer
scales the correction divides out the corresponding power of the original exponential.
In a family of scales with zero sum of squares, the corrections collectively cancel.
-/

public section

open scoped PowerSeries

namespace PowerSeries

/-- If the squares of the scales sum to zero, the product of the rescaled formal exponentials
is unchanged by subtracting the quadratic rescaling correction from each exponent. -/
theorem prod_rescale_subst_exp_eq_of_sum_sq_eq_zero {R ι : Type*} [CommRing R] [Algebra ℚ R]
    {g : R⟦X⟧} (hg : constantCoeff g = 0) (s : Finset ι) (a : ι → R)
    (ha : ∑ i ∈ s, a i ^ 2 = 0) :
    ∏ i ∈ s, rescale (a i) ((exp R).subst g) =
      ∏ i ∈ s, (exp R).subst (rescale (a i) g - a i ^ 2 • g) := by
  have h₁ (i : ι) : constantCoeff (rescale (a i) ((exp R).subst g)) = 1 := by
    simp [constantCoeff_rescale, hg]
  have h₂ (i : ι) : constantCoeff (rescale (a i) g - a i ^ 2 • g) = 0 := by
    simp [constantCoeff_rescale, hg]
  apply (logOf_inj (by simp [h₁]) (by simp [h₂])).mp
  simp only [logOf_prod (fun i _ ↦ h₁ i), logOf_prod (fun i _ ↦ constantCoeff_subst_exp (h₂ i)),
    logOf_rescale _ (constantCoeff_subst_exp hg), logOf_subst_exp hg, logOf_subst_exp (h₂ _),
    Finset.sum_sub_distrib, ← Finset.sum_smul, ha, zero_smul, sub_zero]

/-- The quadratic correction at a natural scale `n` removes the `n²`-th power of
the original exponential. -/
theorem subst_exp_rescale_sub_sq_smul_mul_pow {R : Type*} [CommRing R] [Algebra ℚ R]
    {g : R⟦X⟧} (hg : constantCoeff g = 0) (n : ℕ) :
    (exp R).subst (rescale (n : R) g - (n : R) ^ 2 • g) * ((exp R).subst g) ^ n ^ 2 =
      rescale (n : R) ((exp R).subst g) := by
  have h₁ : constantCoeff ((exp R).subst g) = 1 := constantCoeff_subst_exp hg
  have h₂ : constantCoeff (rescale (n : R) g - (n : R) ^ 2 • g) = 0 := by
    simp [constantCoeff_rescale, hg]
  have hlog : logOf (((exp R).subst g) ^ n ^ 2) = (n : R) ^ 2 • g := by
    have h : logOf (((exp R).subst g) ^ n ^ 2) = (n ^ 2 : ℕ) • g := by
      simpa only [Finset.prod_const, Finset.sum_const, Finset.card_range, logOf_subst_exp hg] using
        (logOf_prod (s := Finset.range (n ^ 2)) (f := fun _ ↦ (exp R).subst g) (fun _ _ ↦ h₁))
    exact h.trans (by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul R])
  apply (logOf_inj (by simp [h₂, h₁]) (by simp [constantCoeff_rescale, h₁])).mp
  rw [logOf_mul (constantCoeff_subst_exp h₂) (by simp [h₁]), logOf_subst_exp h₂, hlog,
    sub_add_cancel, logOf_rescale _ h₁, logOf_subst_exp hg]

end PowerSeries
