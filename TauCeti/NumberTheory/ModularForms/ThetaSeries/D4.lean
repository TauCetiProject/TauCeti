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

/-!
# The theta series of D₄

The real model of `TauCeti.IntegralLattice.checkerboardLattice 4` is an even full lattice of
rank `4`, level `2` and signed discriminant `4 = 2²`. Because its signed discriminant is a square,
its quadratic theta character is trivial, so `ZLattice.thetaFormGamma0` bundles its theta series
directly as a weight-two modular form on `Γ₀(2)`
(`TauCeti.IntegralLattice.checkerboardLatticeFourThetaFormGamma0`).

Since `[SL₂(ℤ) : Γ₀(2)] = 3`, the Sturm bound identifies this modular form with
`-EisensteinSeries.correctedE2 2` — pointwise `2 E₂(2τ) - E₂(τ)` — from their common constant
coefficient `1`, without enumerating roots
(`TauCeti.IntegralLattice.checkerboardLatticeFourThetaFormGamma0_eq`). Reading off
Fourier coefficients yields the odd-divisor representation numbers
`r_{D₄}(2m) = 24 ∑_{d ∣ m, d odd} d` for `m ≥ 1` (in particular `r_{D₄}(2) = 24`) and the
classical `q`-series expansion `Θ_{D₄}(τ) = 1 + 24 ∑_{m ≥ 1} (∑_{d ∣ m, d odd} d) q^m`.

## Main definitions

* `TauCeti.IntegralLattice.checkerboardLatticeFourThetaFormGamma0`: `Θ_{D₄}` as a
  bundled weight-two modular form on `Γ₀(2)`.

## Main statements

* `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardLattice_four_slash_of_mem_Gamma0`:
  `Γ₀(2)` slash invariance of `Θ_{D₄}` in weight `2`.
* `TauCeti.IntegralLattice.checkerboardLatticeFourThetaFormGamma0_eq`,
  `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardLattice_four`,
  `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardLattice_four_apply`: bundled,
  function-level and pointwise identifications with `-correctedE2 2` (`2 E₂(2τ) - E₂(τ)`).
* `TauCeti.IntegralLattice.representationNumber_checkerboardLattice_four_two_mul`,
  `TauCeti.IntegralLattice.representationNumber_checkerboardLattice_four_two`,
  `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardLattice_four_eq_tsum`: odd-divisor
  representation numbers, kissing number `24` and classical `q`-series expansion of `D₄`.

## References

* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
-/

public noncomputable section

open Module ModularForm UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm ArithmeticFunction.sigma

namespace TauCeti.IntegralLattice

/-- The theta series of the real model of `D₄`, bundled as a weight-two modular form on
`Γ₀(2)`. -/
def checkerboardLatticeFourThetaFormGamma0 :
    ModularForm ((Gamma0 2).map (mapGL ℝ)) 2 :=
  (ZLattice.thetaFormGamma0
    ((isEven_realModel_iff _ (isPosDef_checkerboardLattice 4)).mpr (isEven_checkerboardLattice 4))
    (k := 2) (by simp [RealModelSpace.finrank_eq, finrank_carrier])
    (ZLattice.IsEven.thetaCharacter_eq_one_of_isSquare _ _
      ⟨2, by rw [signedDiscr_realModel_checkerboardLattice_four]; norm_num⟩)).mcast rfl
    (by rw [level_realModel_checkerboardLattice_four])

/-- The underlying function of `checkerboardLatticeFourThetaFormGamma0` is the theta
series of the real model of `D₄`. -/
@[simp]
theorem coe_checkerboardLatticeFourThetaFormGamma0 :
    ⇑checkerboardLatticeFourThetaFormGamma0 =
      ZLattice.thetaSeries
        ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) := by
  dsimp only [checkerboardLatticeFourThetaFormGamma0, ModularForm.coe_mcast]
  exact ZLattice.coe_thetaFormGamma0 _ _ _

/-- The `q`-expansion coefficients of `checkerboardLatticeFourThetaFormGamma0` are the
rational representation numbers of `D₄` at even norms. -/
theorem qExpansion_checkerboardLatticeFourThetaFormGamma0_coeff (m : ℕ) :
    (qExpansion 1 checkerboardLatticeFourThetaFormGamma0).coeff m =
      ((checkerboardLattice 4).representationNumber (2 * m) : ℂ) := by
  rw [coe_checkerboardLatticeFourThetaFormGamma0,
    (isEven_checkerboardLattice 4).qExpansion_thetaSeries_realModel_coeff
      (isPosDef_checkerboardLattice 4)]

/-- The weight-two theta form of `D₄` on `Γ₀(2)` is nonzero. -/
@[simp]
theorem checkerboardLatticeFourThetaFormGamma0_ne_zero :
    checkerboardLatticeFourThetaFormGamma0 ≠ 0 := fun h ↦
  ZLattice.thetaSeries_ne_zero_of_re_eq_zero _ UpperHalfPlane.I_re (by
    rw [← coe_checkerboardLatticeFourThetaFormGamma0, h, FunLike.coe_zero]
    rfl)

/-- The weight-two theta form of `D₄` on `Γ₀(2)` is not a cusp form: its constant term at `∞`
is `1`. -/
@[simp]
theorem not_isCuspForm_checkerboardLatticeFourThetaFormGamma0 :
    ¬ ModularForm.IsCuspForm checkerboardLatticeFourThetaFormGamma0 :=
  ZLattice.not_isCuspForm_of_coe_eq_thetaSeries _
    coe_checkerboardLatticeFourThetaFormGamma0

/-- **Trivial-character `Γ₀(2)` invariance for `D₄`.** Under every matrix `A ∈ Γ₀(2)`, the theta
series of the real model of `D₄` is invariant in weight `2`. -/
theorem thetaSeries_realModel_checkerboardLattice_four_slash_of_mem_Gamma0
    {A : SL(2, ℤ)} (hA : A ∈ Gamma0 2) :
    ZLattice.thetaSeries
        ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) ∣[(2 : ℤ)] A =
      ZLattice.thetaSeries
        ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) := by
  have hL : ZLattice.IsEven
      ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) :=
    (isEven_realModel_iff _ (isPosDef_checkerboardLattice 4)).mpr (isEven_checkerboardLattice 4)
  have hA' : A ∈ Gamma0
      (ZLattice.level ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4))) := by
    rwa [level_realModel_checkerboardLattice_four]
  exact hL.thetaSeries_slash_of_mem_Gamma0_of_isSquare
    (by simp [RealModelSpace.finrank_eq, finrank_carrier])
    ⟨2, by rw [signedDiscr_realModel_checkerboardLattice_four]; norm_num⟩ hA'

/-- As weight-two modular forms on `Γ₀(2)`, the theta form of the real model of `D₄` equals
`-EisensteinSeries.correctedE2 2`. -/
theorem checkerboardLatticeFourThetaFormGamma0_eq :
    checkerboardLatticeFourThetaFormGamma0 = -EisensteinSeries.correctedE2 2 := by
  have hi : Nat.card (𝒮ℒ ⧸ ((Gamma0 2).map (mapGL ℝ)).subgroupOf 𝒮ℒ) = 3 := by
    rw [Subgroup.card_quotient_mapGL_eq_index, Gamma0_prime_index 2 Nat.prime_two]
  apply ModularForm.eq_of_sturm_bound
  intro i hi'
  rw [hi] at hi'
  have hi0 : i = 0 := by norm_num at hi'; omega
  subst i
  have hL : ZLattice.IsEven
      ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) :=
    (isEven_realModel_iff _ (isPosDef_checkerboardLattice 4)).mpr (isEven_checkerboardLattice 4)
  rw [CongruenceSubgroup.strictWidthInfty_Gamma0,
    coe_checkerboardLatticeFourThetaFormGamma0, hL.qExpansion_thetaSeries_coeff,
    FunLike.coe_neg, ModularForm.qExpansion_neg one_pos
      (TauCeti.one_mem_strictPeriods_Gamma0_map 2),
    map_neg, EisensteinSeries.qExpansion_coeff_correctedE2]
  norm_num

/-- The theta series of the real `D₄` lattice is `2 E₂(2τ) - E₂(τ)`. -/
@[simp]
theorem thetaSeries_realModel_checkerboardLattice_four :
    ZLattice.thetaSeries ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) =
      ⇑(-EisensteinSeries.correctedE2 2) := by
  rw [← coe_checkerboardLatticeFourThetaFormGamma0,
    checkerboardLatticeFourThetaFormGamma0_eq]

/-- Pointwise on the upper half-plane, `Θ_{D₄}(τ) = 2 E₂(2τ) - E₂(τ)`. -/
theorem thetaSeries_realModel_checkerboardLattice_four_apply (τ : ℍ) :
    ZLattice.thetaSeries ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) τ =
      2 * _root_.EisensteinSeries.E2 (scaleGL 2 • τ) - _root_.EisensteinSeries.E2 τ := by
  rw [thetaSeries_realModel_checkerboardLattice_four, FunLike.coe_neg, Pi.neg_apply,
    EisensteinSeries.correctedE2_apply]
  push_cast
  ring

/-- For `m ≠ 0`, the number of vectors of norm `2m` in `D₄` is `24` times the sum of the
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

/-- `D₄` has `24` vectors of norm `2` (its minimal vectors). -/
theorem representationNumber_checkerboardLattice_four_two :
    (checkerboardLattice 4).representationNumber 2 = 24 := by
  have h := representationNumber_checkerboardLattice_four_two_mul (m := 1) one_ne_zero
  norm_num [Finset.sum_filter] at h ⊢
  exact h

/-- The classical expansion `Θ_{D₄}(τ) = 1 + 24 ∑_{m ≥ 1} (∑_{d ∣ m, d odd} d) q^m`,
where `q = exp (2 π i τ)`. -/
theorem thetaSeries_realModel_checkerboardLattice_four_eq_tsum (τ : ℍ) :
    ZLattice.thetaSeries ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) τ =
      1 + 24 * ∑' m : ℕ, (∑ d ∈ (m + 1).divisors with Odd d, (d : ℂ)) *
        Function.Periodic.qParam 1 τ ^ (m + 1) := by
  let L := (checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)
  have hL : ZLattice.IsEven L :=
    (isEven_realModel_iff _ (isPosDef_checkerboardLattice 4)).mpr (isEven_checkerboardLattice 4)
  have hs := hL.hasSum_thetaSeries_qParam τ
  have ht := hs.summable.sum_add_tsum_nat_add 1
  rw [hs.tsum_eq] at ht
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, ZLattice.representationNumber_zero,
    Nat.cast_one, pow_zero, smul_eq_mul, mul_one] at ht
  have hcoeff (m : ℕ) : (ZLattice.representationNumber L (2 * ((m + 1 : ℕ) : ℝ)) : ℂ) =
      24 * ∑ d ∈ (m + 1).divisors with Odd d, (d : ℂ) := by
    rw [← hL.qExpansion_thetaSeries_coeff (m + 1),
      (isEven_checkerboardLattice 4).qExpansion_thetaSeries_realModel_coeff
        (isPosDef_checkerboardLattice 4) (m + 1),
      representationNumber_checkerboardLattice_four_two_mul (Nat.succ_ne_zero m)]
    push_cast
    rfl
  simp_rw [hcoeff, mul_assoc] at ht
  rw [tsum_mul_left] at ht
  exact ht.symm

end TauCeti.IntegralLattice
