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
import TauCeti.NumberTheory.ModularForms.TrivialNebentypus
import TauCeti.NumberTheory.Divisors
import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The theta series of D₄

The theta series of the real model of `IntegralLattice.checkerboardLattice 4` is
`2 E₂(2τ) - E₂(τ)`, the negative of `EisensteinSeries.correctedE2 2`.
The identification uses the Sturm bound on `Γ₀(2)`: weight two and index three mean that
only the constant coefficient is needed. In particular no enumeration of roots enters the
identity. Its Fourier coefficients give the representation numbers of the rational lattice.

## References

* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
-/

public section

open Module ModularForm UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ArithmeticFunction.sigma

namespace TauCeti.IntegralLattice

/-- The theta series of the real D₄ lattice is `2 E₂(2τ) - E₂(τ)`. -/
@[simp]
theorem thetaSeries_realModel_checkerboardLattice_four :
    ZLattice.thetaSeries ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) =
      ⇑(-EisensteinSeries.correctedE2 2) := by
  let L := (checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)
  have hL : ZLattice.IsEven L := (isEven_realModel_iff _ _).mpr (isEven_checkerboardLattice 4)
  have hk : finrank ℝ ((checkerboardLattice 4).RealModelSpace
      (isPosDef_checkerboardLattice 4)) = 2 * 2 := by simp [finrank_carrier]
  have hN : ZLattice.level L = 2 := level_realModel_checkerboardLattice_four
  have hχ : hL.thetaCharacter ⟨2, hk⟩ = 1 :=
    hL.thetaCharacter_eq_one_of_isSquare _
      ⟨2, by rw [signedDiscr_realModel_checkerboardLattice_four]; norm_num⟩
  obtain ⟨f, hf⟩ : ∃ f : ModularForm ((Gamma0 2).map (mapGL ℝ)) 2,
      ⇑f = ZLattice.thetaSeries L := by
    suffices h : ∃ f : ModularForm ((Gamma0 (ZLattice.level L)).map (mapGL ℝ)) 2,
        ⇑f = ZLattice.thetaSeries L by
      rw [hN] at h
      exact h
    have : NeZero (ZLattice.level L) := ⟨by omega⟩
    have hg : ZLattice.thetaFormOfLevel hL hk ∈
        TauCeti.modFormCharSpace 2 (1 : (ZMod (ZLattice.level L))ˣ →* ℂˣ) := by
      simpa only [hχ, ← MulChar.mulEquivToUnitHom_apply, map_one, Nat.cast_ofNat] using
        ZLattice.thetaFormOfLevel_mem_modFormCharSpace hL hk
    refine ⟨TauCeti.modFormCharSpaceOneEquiv (ZLattice.level L) 2 ⟨_, hg⟩, ?_⟩
    rw [TauCeti.coe_modFormCharSpaceOneEquiv_apply]
    exact ZLattice.coe_thetaFormOfLevel hL hk
  have hi : Nat.card (𝒮ℒ ⧸ ((Gamma0 2).map (mapGL ℝ)).subgroupOf 𝒮ℒ) = 3 := by
    rw [Subgroup.card_quotient_mapGL_eq_index, Gamma0_prime_index 2 Nat.prime_two]
  have heq : f = -EisensteinSeries.correctedE2 2 := by
    apply ModularForm.eq_of_sturm_bound
    intro i hi'
    rw [hi] at hi'
    have hi0 : i = 0 := by norm_num at hi'; omega
    subst i
    rw [CongruenceSubgroup.strictWidthInfty_Gamma0, hf, hL.qExpansion_thetaSeries_coeff]
    rw [FunLike.coe_neg, ModularForm.qExpansion_neg one_pos
        (TauCeti.one_mem_strictPeriods_Gamma0_map 2),
      map_neg, EisensteinSeries.qExpansion_coeff_correctedE2]
    norm_num
  exact hf.symm.trans (congrArg (DFunLike.coe (F := ModularForm
    ((Gamma0 2).map (mapGL ℝ)) 2)) heq)

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
