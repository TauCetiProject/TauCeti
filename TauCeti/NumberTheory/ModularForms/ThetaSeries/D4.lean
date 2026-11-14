/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.RootLattice
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.RealModel
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Basic
import TauCeti.NumberTheory.ModularForms.ThetaSeries.GeneralLevel
import TauCeti.NumberTheory.Divisors
import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The theta series of D₄

The root lattice `D₄ = IntegralLattice.checkerboardLattice 4` has rank `4`, level `2`, and square
signed discriminant `4 = 2²`. Its quadratic theta character is therefore trivial, so
`ZLattice.thetaFormGamma0` bundles the theta series of its real model as a weight-two modular form
`thetaFormRealModelCheckerboardLatticeFour` on `Γ₀(2)`.

By the Sturm bound on `Γ₀(2)` (weight two and index three, so `⌊6 / 12⌋ = 0` and only the constant
coefficient enters), this modular form equals `-EisensteinSeries.correctedE2 2`, namely
`2 E₂(2τ) - E₂(τ)`. In particular no enumeration of roots enters the identity. Its Fourier
coefficients give the representation numbers `r_{D₄}(2m) = 24 ∑_{d ∣ m, d odd} d` of the rational
lattice and the convergent `q`-series expansion of `Θ_{D₄}`.

## Main definitions

* `TauCeti.IntegralLattice.thetaFormRealModelCheckerboardLatticeFour`: the theta series of the
  real model of `D₄`, bundled as a weight-two modular form on `Γ₀(2)`.

## Main statements

* `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardLattice_four_slash_of_mem_Gamma0`:
  `Θ_{D₄} ∣[2] A = Θ_{D₄}` for every `A ∈ Γ₀(2)`.
* `TauCeti.IntegralLattice.thetaFormRealModelCheckerboardLatticeFour_eq_neg_correctedE2`,
  `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardLattice_four`: equality of `Θ_{D₄}`
  with `-EisensteinSeries.correctedE2 2` (`2 E₂(2τ) - E₂(τ)`), as modular forms in `M₂(Γ₀(2))` and
  as functions on `ℍ`.
* `TauCeti.IntegralLattice.representationNumber_checkerboardLattice_four_two_mul`,
  `TauCeti.IntegralLattice.representationNumber_checkerboardLattice_four_two`:
  `r_{D₄}(2m) = 24 ∑_{d ∣ m, d odd} d` for `m ≠ 0`, and `r_{D₄}(2) = 24`.
* `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardLattice_four_eq_tsum`: the convergent
  expansion `Θ_{D₄}(τ) = 1 + 24 ∑_{m ≥ 1} (∑_{d ∣ m, d odd} d) q^m`.

## References

* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
-/

public section

open Module ModularForm UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ArithmeticFunction.sigma

namespace TauCeti.IntegralLattice

/-- **Modularity of `Θ_{D₄}` on `Γ₀(2)`**: the theta series of the real model of `D₄`, bundled as a
weight-two modular form on `Γ₀(2)` via `ZLattice.thetaFormGamma0` from the lattice invariants
`level D₄ = 2` and `signedDiscr D₄ = 4 = 2²`. -/
noncomputable def thetaFormRealModelCheckerboardLatticeFour :
    ModularForm ((Gamma0 2).map (mapGL ℝ)) 2 :=
  (ZLattice.thetaFormGamma0
    ((isEven_realModel_iff _ (isPosDef_checkerboardLattice 4)).mpr (isEven_checkerboardLattice 4))
    (k := 2) (by simp [finrank_carrier])
    (ZLattice.IsEven.thetaCharacter_eq_one_of_isSquare _ _
      ⟨2, by rw [signedDiscr_realModel_checkerboardLattice_four]; norm_num⟩)).mcast rfl
    (by rw [level_realModel_checkerboardLattice_four])

/-- The underlying function of the bundled `D₄` theta form is the lattice theta series. -/
@[simp]
theorem coe_thetaFormRealModelCheckerboardLatticeFour :
    ⇑thetaFormRealModelCheckerboardLatticeFour =
      ZLattice.thetaSeries
        ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) := by
  dsimp only [thetaFormRealModelCheckerboardLatticeFour, ModularForm.coe_mcast]
  exact ZLattice.coe_thetaFormGamma0 _ _ _

/-- The theta series of the real model of `D₄` is invariant in weight two under every matrix
`A ∈ Γ₀(2)`. -/
theorem thetaSeries_realModel_checkerboardLattice_four_slash_of_mem_Gamma0 {A : SL(2, ℤ)}
    (hA : A ∈ Gamma0 2) :
    ZLattice.thetaSeries ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4))
        ∣[(2 : ℤ)] A =
      ZLattice.thetaSeries
        ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) := by
  rw [← coe_thetaFormRealModelCheckerboardLatticeFour, ModularForm.SL_slash,
    TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
  exact thetaFormRealModelCheckerboardLatticeFour.slash_action_eq' _
    (Subgroup.mem_map_of_mem _ hA)

/-- As weight-two modular forms on `Γ₀(2)`, the theta form of the real model of `D₄` equals
`-EisensteinSeries.correctedE2 2`, namely `2 E₂(2τ) - E₂(τ)`. -/
theorem thetaFormRealModelCheckerboardLatticeFour_eq_neg_correctedE2 :
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
  rw [← coe_thetaFormRealModelCheckerboardLatticeFour,
    thetaFormRealModelCheckerboardLatticeFour_eq_neg_correctedE2]

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

/-- The classical expansion `Θ_{D₄}(τ) = 1 + 24 ∑_{m ≥ 1} (∑_{d ∣ m, d odd} d) q^m`,
where `q = exp (2 π i τ)`. -/
theorem thetaSeries_realModel_checkerboardLattice_four_eq_tsum (τ : ℍ) :
    ZLattice.thetaSeries ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) τ =
      1 + 24 * ∑' m : ℕ, (∑ d ∈ (m + 1).divisors with Odd d, (d : ℂ)) *
        Function.Periodic.qParam 1 τ ^ (m + 1) := by
  have hL : ZLattice.IsEven
      ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) :=
    (isEven_realModel_iff _ _).mpr (isEven_checkerboardLattice 4)
  have hs := hL.hasSum_thetaSeries_qParam τ
  have ht := hs.summable.sum_add_tsum_nat_add 1
  rw [hs.tsum_eq] at ht
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, ZLattice.representationNumber_zero,
    Nat.cast_one, pow_zero, smul_eq_mul, mul_one] at ht
  have hterm (m : ℕ) :
      (ZLattice.representationNumber
          ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4))
          (2 * (m + 1 : ℕ)) : ℂ) * Function.Periodic.qParam 1 τ ^ (m + 1) =
        24 * ((∑ d ∈ (m + 1).divisors with Odd d, (d : ℂ)) *
          Function.Periodic.qParam 1 τ ^ (m + 1)) := by
    have hrep := (checkerboardLattice 4).representationNumber_realModel
      (isPosDef_checkerboardLattice 4) (2 * ((m + 1 : ℕ) : ℚ))
    rw [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] at hrep
    rw [hrep, representationNumber_checkerboardLattice_four_two_mul (Nat.succ_ne_zero m)]
    push_cast
    ring
  simp_rw [hterm, tsum_mul_left] at ht
  exact ht.symm

end TauCeti.IntegralLattice
