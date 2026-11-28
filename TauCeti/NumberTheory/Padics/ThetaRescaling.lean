/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.FourSquares
import TauCeti.RingTheory.PowerSeries.Exp.QuadraticRescale
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Rescale
import TauCeti.RingTheory.PowerSeries.SubringCoeff

/-!
# Cancelling quadratic rescaling factors of theta series

For a theta series written as `exp(g)`, the normalized factor at scale `a` has logarithm
`g(aX) - a² g(X)`. If the normalized factors at natural-number scales are integral in a formal
coordinate, density gives the same result at every p-adic integer scale. A tuple of scales with
zero sum of squares then cancels the normalization. This produces integral products with an
integral inverse, without requiring the individual theta series to have integral coefficients.

The cancellation and density argument is the formal-series step of
`New.CMLattice.prod_rescale_theta_mem` and `New.CMLattice.exists_scaledThetaProd_mem_mul_eq_one`
in `grh/src/New/Derivatives/Sharpness/LeastValuation.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open scoped PowerSeries PowerSeries.WithPiTopology

namespace PowerSeries

/-- Integrality of the quadratic-rescaling factor at every natural scale extends to every
p-adic integer scale. Integrality in the coordinate `y` is expressed by pulling back along
`y.substAlgEquiv.symm` and testing the coefficients in the closed subring `O`. -/
theorem coeff_subst_exp_rescale_sub_sq_smul_mem {p : ℕ} [Fact p.Prime] {R : Type*}
    [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    {O : Subring R} (hO : IsClosed (O : Set R)) (y : TauCeti.FormalCoordinate R)
    (η : ℤ_[p] →+* R) (hη : Continuous η) {g : R⟦X⟧} (hg : constantCoeff g = 0)
    (hnat : ∀ n k : ℕ, coeff k (y.substAlgEquiv.symm
      ((exp R).subst (rescale (n : R) g - (n : R) ^ 2 • g))) ∈ O) (a : ℤ_[p]) (k : ℕ) :
    coeff k (y.substAlgEquiv.symm
      ((exp R).subst (rescale (η a) g - (η a) ^ 2 • g))) ∈ O := by
  let D (a : ℤ_[p]) := rescale (η a) g - (η a) ^ 2 • g
  have hD₀ (a : ℤ_[p]) : constantCoeff (D a) = 0 := by
    simp [D, constantCoeff_rescale, hg]
  have hD : Continuous D := by
    refine continuous_iff_continuousAt.mpr fun a ↦
      (WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr fun n ↦ ?_
    simp only [D, map_sub, coeff_rescale, coeff_smul, smul_eq_mul]
    exact (((hη.pow n).mul continuous_const).sub
      ((hη.pow 2).mul continuous_const)).continuousAt
  have hG : Continuous (fun a ↦ y.substAlgEquiv.symm ((exp R).subst (D a))) := by
    rw [TauCeti.FormalCoordinate.substAlgEquiv_symm]
    simp only [TauCeti.FormalCoordinate.substAlgEquiv_apply]
    exact (continuous_const.powerSeries_subst hD hD₀).powerSeries_subst continuous_const
      (fun _ ↦ (y⁻¹).constantCoeff_toPowerSeries)
  refine PadicInt.denseRange_natCast.induction_on
    (p := fun a ↦ coeff k (y.substAlgEquiv.symm ((exp R).subst (D a))) ∈ O) a
    (hO.preimage ((WithPiTopology.continuous_coeff R k).comp hG)) ?_
  intro n
  simpa only [D, map_natCast] using hnat n k

/-- A zero sum of squared p-adic scales gives a product that is a unit in the integral
power series in `y`, provided the natural-scale corrections are integral in `y`.
The witness has constant coefficient one, so its inverse is taken over `O` itself. -/
theorem exists_map_prod_rescale_subst_exp_of_sum_sq_eq_zero {p : ℕ} [Fact p.Prime] {R ι : Type*}
    [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    {O : Subring R} (hO : IsClosed (O : Set R)) (y : TauCeti.FormalCoordinate R)
    (η : ℤ_[p] →+* R) (hη : Continuous η) {g : R⟦X⟧} (hg : constantCoeff g = 0)
    (hnat : ∀ n k : ℕ, coeff k (y.substAlgEquiv.symm
      ((exp R).subst (rescale (n : R) g - (n : R) ^ 2 • g))) ∈ O)
    (s : Finset ι) (a : ι → ℤ_[p]) (ha : ∑ i ∈ s, η (a i) ^ 2 = 0) :
    ∃ u : O⟦X⟧, constantCoeff u = 1 ∧
      y.substAlgEquiv (map O.subtype u) = ∏ i ∈ s, rescale (η (a i)) ((exp R).subst g) := by
  classical
  let f (i : ι) := (exp R).subst (rescale (η (a i)) g - (η (a i)) ^ 2 • g)
  have hmem (i : ι) : y.substAlgEquiv.symm (f i) ∈ (map O.subtype).range := by
    refine (mem_map_range O.subtype).mpr fun k ↦ ?_
    exact ⟨⟨_, coeff_subst_exp_rescale_sub_sq_smul_mem hO y η hη hg hnat (a i) k⟩, rfl⟩
  obtain ⟨u, hu⟩ := (map O.subtype).range.prod_mem fun i _ ↦ hmem i
  rw [← map_prod] at hu
  have he : y.substAlgEquiv (map O.subtype u) = ∏ i ∈ s, f i :=
    (congrArg y.substAlgEquiv hu).trans (AlgEquiv.apply_symm_apply _ _)
  refine ⟨u, O.subtype_injective ?_, he.trans ?_⟩
  · have hc := congrArg constantCoeff he
    simpa [TauCeti.FormalCoordinate.constantCoeff_substAlgEquiv, constantCoeff_map, f,
      constantCoeff_rescale, hg] using hc
  · exact (prod_rescale_subst_exp_eq_of_sum_sq_eq_zero hg s (η ∘ a) ha).symm

/-- Suppose the rescale of `θ` by each positive integer `n` is `θ ^ (n ^ 2)` times a
series integral in the formal coordinate `y`, as in the multiplication-by-`n` law
for theta sections. Six p-adic scales starting with `1` give a product of rescaled
copies of `θ` that is a unit in the integral power series in `y`. -/
theorem exists_six_rescale_prod_eq_integral_unit {p : ℕ} [Fact p.Prime] {R : Type*}
    [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    {O : Subring R} (hO : IsClosed (O : Set R)) (y : TauCeti.FormalCoordinate R)
    (η : ℤ_[p] →+* R) (hη : Continuous η) {θ : R⟦X⟧} (hθ : constantCoeff θ = 1)
    (hnat : ∀ n : ℕ, 0 < n → ∃ H : O⟦X⟧,
      y.substAlgEquiv (map O.subtype H) * θ ^ n ^ 2 = rescale (n : R) θ) :
    ∃ a : Fin 6 → ℤ_[p], a 0 = 1 ∧ ∃ u : O⟦X⟧, constantCoeff u = 1 ∧
      y.substAlgEquiv (map O.subtype u) = ∏ i, rescale (η (a i)) θ := by
  let g := logOf θ
  have hg : constantCoeff g = 0 := constantCoeff_logOf hθ
  have hExp : (exp R).subst g = θ := subst_exp_logOf hθ
  have hθu : IsUnit θ := isUnit_iff_constantCoeff.mpr (hθ ▸ isUnit_one)
  have hcorr (n k : ℕ) : coeff k (y.substAlgEquiv.symm
      ((exp R).subst (rescale (n : R) g - (n : R) ^ 2 • g))) ∈ O := by
    obtain ⟨H, hH⟩ : ∃ H : O⟦X⟧,
        y.substAlgEquiv (map O.subtype H) * θ ^ n ^ 2 = rescale (n : R) θ := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact ⟨1, by simp [rescale_zero, hθ]⟩
      · exact hnat n hn
    have h := subst_exp_rescale_sub_sq_smul_mul_pow hg n
    rw [hExp, ← hH] at h
    rw [(hθu.pow (n ^ 2)).mul_right_cancel h, AlgEquiv.symm_apply_apply, coeff_map]
    exact (coeff k H).property
  obtain ⟨v, w, x, z, h⟩ := PadicInt.sum_four_squares (-1 : ℤ_[p])
  let a : Fin 6 → ℤ_[p] := ![1, v, w, x, z, 0]
  have ha : ∑ i, a i ^ 2 = 0 := by
    simp [a, Fin.sum_univ_succ]
    linear_combination h
  have ha' : ∑ i, η (a i) ^ 2 = 0 := by
    simpa only [map_sum, map_pow, map_zero] using congrArg η ha
  refine ⟨a, rfl, ?_⟩
  simpa only [hExp] using
    exists_map_prod_rescale_subst_exp_of_sum_sq_eq_zero hO y η hη hg hcorr Finset.univ a ha'

end PowerSeries
