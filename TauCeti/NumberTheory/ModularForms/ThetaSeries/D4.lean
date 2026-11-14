/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.RootLattice
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.GeneralLevel
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.RealModel
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Basic
import TauCeti.NumberTheory.Divisors
import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The theta series of D₄

The real model of `IntegralLattice.checkerboardLattice 4` has rank `4`, level `2`, and square
signed discriminant `4 = 2²`, so its quadratic theta character is trivial and its theta series
descends via `ZLattice.thetaFormGamma0` to a weight-two modular form
`thetaFormRealModelCheckerboardLatticeFour` on `Γ₀(2)`. This modular form equals
`-EisensteinSeries.correctedE2 2`, whose underlying function is `2 E₂(2τ) - E₂(τ)`.

The identification uses the Sturm bound on `Γ₀(2)`: weight two and index three mean that
only the constant coefficient is needed. In particular no enumeration of roots enters the
identity. Its Fourier coefficients give the representation numbers of the rational lattice.

## Main definitions

* `TauCeti.IntegralLattice.thetaFormRealModelCheckerboardLatticeFour`: the theta series of `D₄` as
  a weight-two modular form on `Γ₀(2)`.

## Main statements

* `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardLattice_four_slash_of_mem_Gamma0`:
  `Θ_{D₄}` is invariant in weight `2` under every matrix of `Γ₀(2)`.
* `TauCeti.IntegralLattice.thetaFormRealModelCheckerboardLatticeFour_eq`,
  `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardLattice_four`:
  `Θ_{D₄} = -EisensteinSeries.correctedE2 2` as modular forms on `Γ₀(2)` and as functions on `ℍ`.
* `TauCeti.IntegralLattice.representationNumber_checkerboardLattice_four_two_mul`: for `m ≠ 0`,
  `r_{D₄}(2m) = 24 ∑_{d ∣ m, d odd} d`.

## References

* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
-/

public section

open Module ModularForm UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ArithmeticFunction.sigma ModularForm

namespace TauCeti.IntegralLattice

/-- The theta series of the real `D₄` lattice is invariant in weight `2` under every matrix of
`Γ₀(2)`. -/
theorem thetaSeries_realModel_checkerboardLattice_four_slash_of_mem_Gamma0 {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 2) :
    ZLattice.thetaSeries ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4))
        ∣[(2 : ℤ)] A =
      ZLattice.thetaSeries ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) :=
  ((isEven_realModel_iff _ _).mpr
      (isEven_checkerboardLattice 4)).thetaSeries_slash_of_mem_Gamma0_of_isSquare
    (by simp [finrank_carrier])
    ⟨2, by rw [signedDiscr_realModel_checkerboardLattice_four]; norm_num⟩
    (by rwa [level_realModel_checkerboardLattice_four])

/-- The theta series of the real model of `D₄` as a weight-two modular form on `Γ₀(2)`. -/
noncomputable def thetaFormRealModelCheckerboardLatticeFour :
    ModularForm ((Gamma0 2).map (mapGL ℝ)) 2 :=
  (ZLattice.thetaFormGamma0
    ((isEven_realModel_iff _ (isPosDef_checkerboardLattice 4)).mpr (isEven_checkerboardLattice 4))
    (k := 2) (by simp [finrank_carrier])
    (((isEven_realModel_iff _ (isPosDef_checkerboardLattice 4)).mpr
      (isEven_checkerboardLattice 4)).thetaCharacter_eq_one_of_isSquare _
        ⟨2, by rw [signedDiscr_realModel_checkerboardLattice_four]; norm_num⟩)).mcast rfl
    (by rw [level_realModel_checkerboardLattice_four])

/-- The underlying function of `thetaFormRealModelCheckerboardLatticeFour` is `Θ_{D₄}`. -/
@[simp]
theorem coe_thetaFormRealModelCheckerboardLatticeFour :
    ⇑thetaFormRealModelCheckerboardLatticeFour =
      ZLattice.thetaSeries
        ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) := by
  dsimp only [thetaFormRealModelCheckerboardLatticeFour, ModularForm.coe_mcast]
  exact ZLattice.coe_thetaFormGamma0 _ _ _

/-- The `D₄` theta form on `Γ₀(2)` is nonzero. -/
@[simp]
theorem thetaFormRealModelCheckerboardLatticeFour_ne_zero :
    thetaFormRealModelCheckerboardLatticeFour ≠ 0 := fun h ↦
  ZLattice.thetaSeries_ne_zero_of_re_eq_zero _ UpperHalfPlane.I_re (by
    rw [← coe_thetaFormRealModelCheckerboardLatticeFour, h, FunLike.coe_zero]
    rfl)

/-- The `D₄` theta form on `Γ₀(2)` is not a cusp form. -/
@[simp]
theorem not_isCuspForm_thetaFormRealModelCheckerboardLatticeFour :
    ¬ ModularForm.IsCuspForm thetaFormRealModelCheckerboardLatticeFour :=
  ZLattice.not_isCuspForm_of_coe_eq_thetaSeries _ coe_thetaFormRealModelCheckerboardLatticeFour

/-- As modular forms on `Γ₀(2)`, the theta form of `D₄` equals
`-EisensteinSeries.correctedE2 2`. -/
theorem thetaFormRealModelCheckerboardLatticeFour_eq :
    thetaFormRealModelCheckerboardLatticeFour = -EisensteinSeries.correctedE2 2 := by
  have hi : Nat.card (𝒮ℒ ⧸ ((Gamma0 2).map (mapGL ℝ)).subgroupOf 𝒮ℒ) = 3 := by
    rw [Subgroup.card_quotient_mapGL_eq_index, Gamma0_prime_index 2 Nat.prime_two]
  apply ModularForm.eq_of_sturm_bound
  intro i hi'
  rw [hi] at hi'
  have hi0 : i = 0 := by norm_num at hi'; omega
  subst i
  rw [CongruenceSubgroup.strictWidthInfty_Gamma0, coe_thetaFormRealModelCheckerboardLatticeFour,
    ((isEven_realModel_iff _ _).mpr (isEven_checkerboardLattice 4)).qExpansion_thetaSeries_coeff,
    FunLike.coe_neg, ModularForm.qExpansion_neg one_pos
      (TauCeti.one_mem_strictPeriods_Gamma0_map 2),
    map_neg, EisensteinSeries.qExpansion_coeff_correctedE2]
  norm_num

/-- The theta series of the real D₄ lattice is `2 E₂(2τ) - E₂(τ)`. -/
@[simp]
theorem thetaSeries_realModel_checkerboardLattice_four :
    ZLattice.thetaSeries ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) =
      ⇑(-EisensteinSeries.correctedE2 2) := by
  rw [← coe_thetaFormRealModelCheckerboardLatticeFour, thetaFormRealModelCheckerboardLatticeFour_eq]

/-- For `m ≠ 0`, the number of vectors of norm `2m` in D₄ is `24` times the sum of the
odd divisors of `m`. -/
theorem representationNumber_checkerboardLattice_four_two_mul {m : ℕ} (hm : m ≠ 0) :
    (checkerboardLattice 4).representationNumber (2 * m) =
      24 * ∑ d ∈ m.divisors with Odd d, d := by
  classical
  have hc := (isEven_checkerboardLattice 4).qExpansion_thetaSeries_realModel_coeff
    (isPosDef_checkerboardLattice 4) m
  rw [thetaSeries_realModel_checkerboardLattice_four, FunLike.coe_neg,
    ModularForm.qExpansion_neg one_pos (TauCeti.one_mem_strictPeriods_Gamma0_map 2),
    map_neg, EisensteinSeries.qExpansion_coeff_correctedE2, ite_eq_right hm] at hc
  have heven : (∑ d ∈ m.divisors with 2 ∣ d, d) =
      if 2 ∣ m then 2 * σ 1 (m / 2) else 0 := by
    split_ifs with h
    · rw [Nat.sum_divisors_filter_dvd h, ArithmeticFunction.sigma_one_apply, Finset.mul_sum]
    · apply Finset.sum_eq_zero
      intro d hd
      exact (h ((Finset.mem_filter.mp hd).2.trans
        (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1))).elim
  have hsplit : σ 1 m = (∑ d ∈ m.divisors with Odd d, d) +
      if 2 ∣ m then 2 * σ 1 (m / 2) else 0 := by
    rw [← heven, ArithmeticFunction.sigma_one_apply, add_comm]
    simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using
      (Finset.sum_filter_add_sum_filter_not m.divisors (fun d ↦ 2 ∣ d) (fun d ↦ d)).symm
  have hs : (σ 1 m : ℂ) = (∑ d ∈ m.divisors with Odd d, d : ℕ) +
      if 2 ∣ m then 2 * (σ 1 (m / 2) : ℂ) else 0 := by exact_mod_cast hsplit
  apply Nat.cast_injective (R := ℂ)
  push_cast at hs ⊢
  linear_combination -hc + 24 * hs

/-- D₄ has `24` vectors of norm `2` (its minimal vectors). -/
theorem representationNumber_checkerboardLattice_four_two :
    (checkerboardLattice 4).representationNumber 2 = 24 := by
  have h := representationNumber_checkerboardLattice_four_two_mul (m := 1) one_ne_zero
  norm_num [Finset.sum_filter] at h ⊢
  exact h

end TauCeti.IntegralLattice
