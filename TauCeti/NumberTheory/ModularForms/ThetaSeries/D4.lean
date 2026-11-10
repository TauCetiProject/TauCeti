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

/-- The theta series of the real D₄ lattice is `2 E₂(2τ) - E₂(τ)`. The identity follows from
modularity and the constant term, without counting roots. -/
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
  let f : ModularForm ((Gamma0 2).map (mapGL ℝ)) 2 :=
    { toFun := ZLattice.thetaSeries L
      slash_action_eq' := by
        intro A hA
        obtain ⟨A, hA, rfl⟩ := hA
        rw [← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash]
        have hA' : A ∈ Gamma0 (ZLattice.level L) := by rwa [hN]
        have hs := hL.thetaSeries_slash_of_mem_Gamma0 hk hA'
        have hd := MulChar.IsQuadratic.apply_one_one_eq_apply_zero_zero_of_mem_Gamma0
          (hL.thetaCharacter_isQuadratic ⟨2, hk⟩) hA'
        rw [hχ] at hs hd
        rw [hd, MulChar.one_apply (isUnit_intCast_apply_zero_zero_of_mem_Gamma0 hA'),
          one_smul] at hs
        simpa only [Nat.cast_ofNat] using hs
      holo' := ZLattice.mdifferentiable_thetaSeries L
      bdd_at_cusps' := fun hc ↦ hL.isBoundedAt_thetaSeries hk
        (hc.mono (Subgroup.map_le_range _ _)) }
  have hf : ⇑f = ZLattice.thetaSeries L := rfl
  have hi : Nat.card (𝒮ℒ ⧸ ((Gamma0 2).map (mapGL ℝ)).subgroupOf 𝒮ℒ) = 3 := by
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex,
      MonoidHom.range_eq_map (mapGL ℝ), ← Subgroup.relIndex_comap,
      Subgroup.comap_map_eq_self_of_injective mapGL_injective, Subgroup.relIndex_top_right,
      Gamma0_prime_index 2 Nat.prime_two]
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

/-- The D₄ representation numbers are twenty-four times the sum of the odd divisors.
The value is deduced from the Eisenstein identity, not from an enumeration of vectors. -/
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

/-- The kissing number of D₄ is `24`, as a consequence of its theta series. -/
theorem representationNumber_checkerboardLattice_four_two :
    (checkerboardLattice 4).representationNumber 2 = 24 := by
  have h := representationNumber_checkerboardLattice_four_two_mul (m := 1) one_ne_zero
  norm_num [Finset.sum_filter] at h ⊢
  exact h

end TauCeti.IntegralLattice
