/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Exponential
public import TauCeti.Algebra.Lie.F4.ShortRoot.Centralizer
public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Basis
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.SpecialMap

/-!
# Root-action columns on the modular F4 quotient

This file records structural first- and second-divided-power columns after quotienting the
modular Chevalley lattice by its short-root ideal.  These formulas are stated on concrete lifts;
they do not package quotient endomorphisms or exponentials.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule
open scoped TensorProduct

noncomputable section

/-- A long-root lift is the quotient basis vector indexed by its short special-map image. -/
theorem f4ShortRootSubspace_mkQ_rootVector_eq_quotientBasis
    (γ : Fin 48) (hγ : f4Length γ = 2) :
    f4ShortRootSubspace.mkQ (f4ModularRootVector γ) =
      f4ShortRootQuotientBasis
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl
          ⟨f4SpecialIsogenyIndexEquiv γ, by
            simpa only [f4SpecialIsogenyIndexEquiv_apply] using
              (f4Length_specialIsogenyIndex_eq_one_iff γ).2 hγ⟩)) := by
  let i : F4ShortRootIndex :=
    ⟨f4SpecialIsogenyIndexEquiv γ, by
      simpa only [f4SpecialIsogenyIndexEquiv_apply] using
        (f4Length_specialIsogenyIndex_eq_one_iff γ).2 hγ⟩
  rw [f4ShortRootQuotientBasis_symm_inl]
  apply congrArg f4ShortRootSubspace.mkQ
  apply congrArg f4ModularRootVector
  -- The local root label `i` is the special-map image of `γ`.
  change γ = f4SpecialIsogenyIndexEquiv (f4SpecialIsogenyIndexEquiv γ)
  simp only [f4SpecialIsogenyIndexEquiv_apply]
  exact (f4SpecialIsogenyIndex_involutive γ).symm

/-- The positive long simple-root `0` has coroot quotient coordinate `13`. -/
theorem f4ShortRootSubspace_mkQ_modularCoroot_inl_zero_eq_quotientBasis :
    f4ShortRootSubspace.mkQ
        (f4ModularCoroot (f4SignedSimpleRootIndex (.inl 0))) =
      f4ShortRootQuotientBasis 13 := by
  rw [f4SignedSimpleRootIndex_inl, f4ModularCoroot_castAdd]
  exact f4ShortRootQuotientBasis_thirteen.symm

/-- The positive long simple-root `1` has coroot quotient coordinate `12`. -/
theorem f4ShortRootSubspace_mkQ_modularCoroot_inl_one_eq_quotientBasis :
    f4ShortRootSubspace.mkQ
        (f4ModularCoroot (f4SignedSimpleRootIndex (.inl 1))) =
      f4ShortRootQuotientBasis 12 := by
  rw [f4SignedSimpleRootIndex_inl, f4ModularCoroot_castAdd]
  exact f4ShortRootQuotientBasis_twelve.symm

/-- The negative long simple-root `0` has the same coroot quotient coordinate `13`. -/
theorem f4ShortRootSubspace_mkQ_modularCoroot_inr_zero_eq_quotientBasis :
    f4ShortRootSubspace.mkQ
        (f4ModularCoroot (f4SignedSimpleRootIndex (.inr 0))) =
      f4ShortRootQuotientBasis 13 := by
  refine (congrArg (fun α => f4ShortRootSubspace.mkQ (f4ModularCoroot α))
    (f4SignedSimpleRootIndex_inr 0)).trans ?_
  exact (congrArg f4ShortRootSubspace.mkQ
    ((f4ModularCoroot_f4OppositeRootIndex (Fin.castAdd 44 (0 : Fin 4))).trans
      (f4ModularCoroot_castAdd 0))).trans
    f4ShortRootQuotientBasis_thirteen.symm

/-- The negative long simple-root `1` has the same coroot quotient coordinate `12`. -/
theorem f4ShortRootSubspace_mkQ_modularCoroot_inr_one_eq_quotientBasis :
    f4ShortRootSubspace.mkQ
        (f4ModularCoroot (f4SignedSimpleRootIndex (.inr 1))) =
      f4ShortRootQuotientBasis 12 := by
  refine (congrArg (fun α => f4ShortRootSubspace.mkQ (f4ModularCoroot α))
    (f4SignedSimpleRootIndex_inr 1)).trans ?_
  exact (congrArg f4ShortRootSubspace.mkQ
    ((f4ModularCoroot_f4OppositeRootIndex (Fin.castAdd 44 (1 : Fin 4))).trans
      (f4ModularCoroot_castAdd 1))).trans
    f4ShortRootQuotientBasis_twelve.symm

/-- On two long roots, the special root permutation preserves their Cartan integer. -/
theorem f4_pairing_specialIsogenyIndexEquiv_eq_of_long
    (α β : Fin 48) (hα : f4Length α = 2) (hβ : f4Length β = 2) :
    f4SimplyConnectedRootDatum.pairing
        (f4SpecialIsogenyIndexEquiv α) (f4SpecialIsogenyIndexEquiv β) =
      f4SimplyConnectedRootDatum.pairing α β := by
  have h := f4Length_mul_pairing_f4SpecialIsogenyIndex α β
  rw [hα, hβ] at h
  omega

/-- The first adjoint action of a short root vanishes after quotienting by the short-root ideal. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_short
    (α : Fin 48) (hα : f4Length α = 1) (x : f4ModularChevalleyLieAlgebra) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, x⁆ = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [← lie_skew (f4ModularRootVector α) x]
  exact Submodule.neg_mem _
    (f4ShortRootSubspace_lie_mem x
      (f4ModularRootVector_mem_shortRootSubspace α hα))

private theorem f4_chainBotCoeff_eq_zero_of_long_add_eq_long
    (α β γ : Fin 48) (hβ : f4Length β = 2) (hγ : f4Length γ = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.chainBotCoeff α β = 0 := by
  let P := f4SimplyConnectedRootDatum
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 1
    (by simpa only [one_zsmul] using h)
  have hαpos : 0 < f4Length α := f4Length_pos α
  have hpair : P.pairing β α = -1 := by
    -- Restate the length identity with the local datum `P` before integer arithmetic.
    change f4Length γ = f4Length β + 1 * f4Length α * P.pairing β α +
      1 ^ 2 * f4Length α at hlen
    rw [hβ, hγ] at hlen
    norm_num at hlen
    nlinarith
  rw [P.chainBotCoeff_eq_zero_iff]
  right
  rintro ⟨δ, hδ⟩
  have hδ' : P.root δ = P.root β + (-1 : ℤ) • P.root α := by
    simpa only [neg_smul, one_smul, sub_eq_add_neg] using hδ
  have hδlen := f4Length_of_root_eq_add_zsmul α β δ (-1) hδ'
  rcases f4Length_eq_one_or_eq_two δ with hδone | hδtwo
  · rw [hβ, hpair, hδone] at hδlen
    norm_num at hδlen
    nlinarith
  · rw [hβ, hpair, hδtwo] at hδlen
    norm_num at hδlen
    nlinarith

/-- A long-to-long root edge has unit first-order coefficient after reduction and hence in the
short-root quotient. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_of_long_add_eq_long
    (α β γ : Fin 48) (hβ : f4Length β = 2) (hγ : f4Length γ = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, f4ModularRootVector β⁆ =
      f4ShortRootSubspace.mkQ (f4ModularRootVector γ) := by
  rw [f4Modular_lie_rootVector_of_add_of_chainBotCoeff_eq_zero α β γ h
    (f4_chainBotCoeff_eq_zero_of_long_add_eq_long α β γ hβ hγ h)]

/-- A transported target-side root edge gives the corresponding long-source first-order
quotient column. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_of_specialMap_add
    (α β γ : Fin 48) (hα : f4Length α = 2)
    (hβ : f4Length β = 2) (hγ : f4Length γ = 2)
    (hmap : f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv γ) =
      f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
        f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv α)) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, f4ModularRootVector β⁆ =
      f4ShortRootSubspace.mkQ (f4ModularRootVector γ) := by
  have hsource :=
    (f4_root_add_smul_iff_specialIsogenyIndexEquiv_root_add α β γ hβ hγ).2 hmap
  have hspecial : f4Length (f4SpecialIsogenyIndexEquiv α) = 1 := by
    simpa only [f4SpecialIsogenyIndexEquiv_apply] using
      (f4Length_specialIsogenyIndex_eq_one_iff α).2 hα
  apply f4ShortRootSubspace_mkQ_lie_rootVector_of_long_add_eq_long α β γ hβ hγ
  simpa only [hspecial, one_zsmul] using hsource

/-- The opposite-root first-order column is the corresponding coroot class. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_opposite (α : Fin 48) :
    f4ShortRootSubspace.mkQ
        ⁅f4ModularRootVector α, f4ModularRootVector (f4OppositeRootIndex α)⁆ =
      f4ShortRootSubspace.mkQ (f4ModularCoroot α) := by
  rw [f4Modular_lie_rootVector_opposite]

/-- The first-order column on every simple-coroot lift is the source root vector scaled by the
reduced Cartan integer, with the sign from bracket order. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_simpleCoroot
    (α : Fin 48) (i : Fin F4.rank) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, f4ModularSimpleCoroot i⁆ =
      -(f4SimplyConnectedRootDatum.pairing α
        (Fin.castAdd 44 (Fin.cast rank_F4 i)) : ZMod 2) •
          f4ShortRootSubspace.mkQ (f4ModularRootVector α) := by
  let c : ZMod 2 := f4SimplyConnectedRootDatum.pairing α
    (Fin.castAdd 44 (Fin.cast rank_F4 i))
  have hlie : ⁅f4ModularRootVector α, f4ModularSimpleCoroot i⁆ =
      -c • f4ModularRootVector α := by
    rw [← lie_skew, f4Modular_lie_simpleCoroot_rootVector, neg_smul]
  rw [hlie, map_smul]

/-- A self root-vector column is zero before and after passing to the quotient. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_self (α : Fin 48) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, f4ModularRootVector α⁆ = 0 := by
  rw [lie_self, map_zero]

/-- If the rational root-space sum is absent, the corresponding first-order quotient column is
zero. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_rootSpace_add_eq_bot
    (α β : Fin 48)
    (hbot : rootSpace (F4.cartanSubalgebra valid_F4)
      ((f4KillingRoot α : (F4.cartanSubalgebra valid_F4) → ℚ) +
        (f4KillingRoot β : (F4.cartanSubalgebra valid_F4) → ℚ)) = ⊥) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, f4ModularRootVector β⁆ = 0 := by
  rw [f4Modular_lie_rootVector_eq_zero_of_rootSpace_add_eq_bot α β hbot, map_zero]

/-- For a non-opposite pair of long roots, absence of the transported target edge forces the
first-order quotient column to vanish. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_no_specialMap_edge
    (α β : Fin 48) (hα : f4Length α = 2) (hβ : f4Length β = 2)
    (hopp : β ≠ f4OppositeRootIndex α)
    (hno : ∀ δ : Fin 48, f4Length δ = 1 →
      f4SimplyConnectedRootDatum.root δ ≠
        f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
          f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv α)) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, f4ModularRootVector β⁆ = 0 := by
  let H := F4.cartanSubalgebra valid_F4
  have hopp' : α ≠ f4OppositeRootIndex β := by
    intro h
    apply hopp
    rw [h, f4OppositeRootIndex_f4OppositeRootIndex]
  have hsum := f4KillingRoot_add_ne_zero_of_ne_opposite α β hopp'
  have hbot : rootSpace H
      ((f4KillingRoot α : H → ℚ) + (f4KillingRoot β : H → ℚ)) = ⊥ := by
    by_contra hne
    obtain ⟨δ, hsource⟩ :=
      exists_f4Root_eq_add_of_rootSpace_ne_bot α β hsum hne
    have hδlong : f4Length δ = 2 := by
      have hlen := f4Length_of_root_eq_add_zsmul α β δ 1
        (by simpa only [one_zsmul] using hsource)
      rcases f4Length_eq_one_or_eq_two δ with hδ | hδ
      · rw [hα, hβ, hδ] at hlen
        norm_num at hlen
        omega
      · exact hδ
    have hδshort : f4Length (f4SpecialIsogenyIndexEquiv δ) = 1 := by
      simpa only [f4SpecialIsogenyIndexEquiv_apply] using
        (f4Length_specialIsogenyIndex_eq_one_iff δ).2 hδlong
    apply hno (f4SpecialIsogenyIndexEquiv δ) hδshort
    apply (f4_root_add_smul_iff_specialIsogenyIndexEquiv_root_add
      α β δ hβ hδlong).1
    have hspecial : f4Length (f4SpecialIsogenyIndexEquiv α) = 1 := by
      simpa only [f4SpecialIsogenyIndexEquiv_apply] using
        (f4Length_specialIsogenyIndex_eq_one_iff α).2 hα
    simpa only [hspecial, one_zsmul] using hsource
  exact f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_rootSpace_add_eq_bot
    α β hbot

private theorem f4ModularDividedAdjointSquare_rootVector_of_long_add_two_short
    (k : Fin 4 ⊕ Fin 4) (β γ : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 1)
    (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (2 : ℤ) • f4SimplyConnectedRootDatum.root (f4SignedSimpleRootIndex k)) :
    f4ModularDividedAdjointSquare k (f4ModularRootVector β) =
      f4ModularRootVector γ := by
  obtain ⟨ε, hεabs, hε⟩ :=
    exists_f4_dividedAd_sq_rootVector_eq_smul_of_long_add_two_short
      (f4SignedSimpleRootIndex k) β γ hα hβ h
  have hεsign : ε = 1 ∨ ε = -1 := by omega
  have hε' :
      Associative.dividedPower 2
          (ad ℚ (F4.lieAlgebra valid_F4)
            (f4ChevalleyRootVector
              (f4KillingRoot (f4SignedSimpleRootIndex k)))) •
          f4ChevalleyRootVector (f4KillingRoot β) =
        (ε : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
    rw [Associative.dividedPower_def, Module.End.smul_def, LinearMap.smul_apply]
    exact hε
  have hintegral :
      f4IntegralDividedAdjointSquare k (f4IntegralRootVector β) =
        ε • f4IntegralRootVector γ := by
    apply Subtype.ext
    calc
      ((f4IntegralDividedAdjointSquare k (f4IntegralRootVector β) :
          f4ChevalleyLieLattice) : F4.lieAlgebra valid_F4) =
          Associative.dividedPower 2
            (ad ℚ (F4.lieAlgebra valid_F4)
              (f4ChevalleyRootVector
                (f4KillingRoot (f4SignedSimpleRootIndex k)))) •
            (f4IntegralRootVector β : F4.lieAlgebra valid_F4) :=
        coe_f4IntegralDividedAdjointSquare_apply k (f4IntegralRootVector β)
      _ = (ε : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
        rw [coe_f4IntegralRootVector]
        exact hε'
      _ = ((ε • f4IntegralRootVector γ : f4ChevalleyLieLattice) :
          F4.lieAlgebra valid_F4) := by
        change _ = f4ChevalleyLieLattice.toSubmodule.subtype
          (ε • f4IntegralRootVector γ)
        rw [map_smul, Submodule.subtype_apply, coe_f4IntegralRootVector,
          Int.cast_smul_eq_zsmul]
  rw [f4ModularRootVector_eq, f4ModularDividedAdjointSquare_tmul, hintegral,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', f4ModularRootVector_eq]
  rcases hεsign with rfl | rfl <;> simp

private theorem f4_dividedPower_two_ad_rootVector_eq_zero_of_no_endpoint
    (α β : Fin 48) (hopp : β ≠ f4OppositeRootIndex α)
    (hno : ∀ γ : Fin 48, f4SimplyConnectedRootDatum.root γ ≠
      f4SimplyConnectedRootDatum.root β +
        (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    Associative.dividedPower 2
        (ad ℚ (F4.lieAlgebra valid_F4)
          (f4ChevalleyRootVector (f4KillingRoot α))) •
        f4ChevalleyRootVector (f4KillingRoot β) = 0 := by
  let H := F4.cartanSubalgebra valid_F4
  have hαnz : (f4KillingRoot α).IsNonZero :=
    H.isNonZero_coe_root (f4KillingRootLabel α)
  have hβnz : (f4KillingRoot β).IsNonZero :=
    H.isNonZero_coe_root (f4KillingRootLabel β)
  have hopp' : α ≠ f4OppositeRootIndex β := by
    intro h
    apply hopp
    rw [h, f4OppositeRootIndex_f4OppositeRootIndex]
  have hsum := f4KillingRoot_add_ne_zero_of_ne_opposite α β hopp'
  rcases f4ChevalleyRootVector_isChevalleySystem.ad_pow_rootVector_eq_zero_or_exists
      hαnz hβnz hsum 2 with hzero | hnonzero
  · rw [Associative.dividedPower_def, Module.End.smul_def, LinearMap.smul_apply,
      hzero, smul_zero]
  · obtain ⟨γ, hγcoe, -, -⟩ := hnonzero
    have hγnz : γ.IsNonZero := by
      rw [Weight.IsNonZero, Weight.IsZero, hγcoe]
      exact coe_add_natCast_smul_ne_zero hαnz hβnz hsum 2
    have hγroot : γ ∈ H.root := by
      simpa only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and] using hγnz
    let δ : Fin 48 := f4PinnedRootIndex ⟨γ, hγroot⟩
    have hδweight : f4KillingRoot δ = γ := by
      -- The Killing weight is the underlying function of its root-label subtype.
      change (f4KillingRootLabel δ : Weight ℚ H (F4.lieAlgebra valid_F4)) = γ
      exact congrArg Subtype.val (f4KillingRootLabel_f4PinnedRootIndex ⟨γ, hγroot⟩)
    apply (hno δ).elim
    apply (f4KillingRoot_eq_add_zsmul_iff α β δ 2).mp
    rw [hδweight]
    simpa using hγcoe

private theorem f4_pairing_ge_neg_one_of_long_ne_opposite
    (α β : Fin 48) (hα : f4Length α = 2) (hβ : f4Length β = 2)
    (hopp : β ≠ f4OppositeRootIndex α) :
    -1 ≤ f4SimplyConnectedRootDatum.pairing β α := by
  let P := f4SimplyConnectedRootDatum
  have hsym : P.pairing β α = P.pairing α β := by
    have hs := f4Length_mul_pairing_comm α β
    rw [hα, hβ] at hs
    have hs' : f4SimplyConnectedRootDatum.pairing β α =
        f4SimplyConnectedRootDatum.pairing α β := by omega
    simpa only [P] using hs'
  have hnegroot : P.root β ≠ -P.root α := by
    intro hroot
    apply hopp
    apply f4KillingRoot_injective
    rw [f4KillingRoot_f4OppositeRootIndex]
    have hk := (f4KillingRoot_eq_add_zsmul_iff α α β (-2)).mpr (by
      rw [hroot]
      module)
    apply Weight.ext
    intro y
    have hy := congrFun hk y
    simp only [Pi.add_apply, Pi.smul_apply, Int.cast_neg, Int.cast_ofNat] at hy
    -- Evaluation of negation is negation of the underlying weight function.
    change f4KillingRoot β y = -f4KillingRoot α y
    linear_combination hy
  have hneNegTwo : P.pairing β α ≠ -2 := by
    intro hp
    apply hnegroot
    exact (P.pairing_neg_two_neg_two_iff β α).mp ⟨hp, hsym.symm.trans hp⟩
  have hbdd := abs_pairing_f4SimplyConnectedRootDatum_le_two β α
  -- Expand the local datum `P` to use the global Cartan-pairing bound.
  change -1 ≤ f4SimplyConnectedRootDatum.pairing β α
  have hlower := (abs_le.mp hbdd).1
  have hne : f4SimplyConnectedRootDatum.pairing β α ≠ -2 := by
    simpa only [P] using hneNegTwo
  omega

private theorem f4_dividedPower_two_ad_rootVector_eq_zero_of_long
    (α β : Fin 48) (hα : f4Length α = 2) (hβ : f4Length β = 2)
    (hopp : β ≠ f4OppositeRootIndex α) :
    Associative.dividedPower 2
        (ad ℚ (F4.lieAlgebra valid_F4)
          (f4ChevalleyRootVector (f4KillingRoot α))) •
        f4ChevalleyRootVector (f4KillingRoot β) = 0 := by
  apply f4_dividedPower_two_ad_rootVector_eq_zero_of_no_endpoint α β hopp
  intro γ hγ
  have hpairLower := f4_pairing_ge_neg_one_of_long_ne_opposite α β hα hβ hopp
  rw [f4SimplyConnectedRootDatum_pairing] at hpairLower
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 2 hγ
  rcases f4Length_eq_one_or_eq_two γ with hlenγ | hlenγ
  · rw [hα, hβ, hlenγ] at hlen
    norm_num at hlen
    omega
  · rw [hα, hβ, hlenγ] at hlen
    norm_num at hlen
    omega

private theorem f4ModularDividedAdjointSquare_rootVector_eq_zero_of_long
    (k : Fin 4 ⊕ Fin 4) (β : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 2)
    (hβ : f4Length β = 2)
    (hopp : β ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k)) :
    f4ModularDividedAdjointSquare k (f4ModularRootVector β) = 0 := by
  have hintegral :
      f4IntegralDividedAdjointSquare k (f4IntegralRootVector β) = 0 := by
    apply Subtype.ext
    rw [coe_f4IntegralDividedAdjointSquare_apply, coe_f4IntegralRootVector,
      ZeroMemClass.coe_zero]
    exact f4_dividedPower_two_ad_rootVector_eq_zero_of_long
      (f4SignedSimpleRootIndex k) β hα hβ (by
        exact hopp)
  rw [f4ModularRootVector_eq, f4ModularDividedAdjointSquare_tmul, hintegral,
    TensorProduct.tmul_zero]

private theorem f4ModularDividedAdjointSquare_rootVector_eq_zero_of_no_endpoint
    (k : Fin 4 ⊕ Fin 4) (β : Fin 48)
    (hopp : β ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k))
    (hno : ∀ γ : Fin 48, f4SimplyConnectedRootDatum.root γ ≠
      f4SimplyConnectedRootDatum.root β +
        (2 : ℤ) •
          f4SimplyConnectedRootDatum.root (f4SignedSimpleRootIndex k)) :
    f4ModularDividedAdjointSquare k (f4ModularRootVector β) = 0 := by
  have hintegral :
      f4IntegralDividedAdjointSquare k (f4IntegralRootVector β) = 0 := by
    apply Subtype.ext
    rw [coe_f4IntegralDividedAdjointSquare_apply, coe_f4IntegralRootVector,
      ZeroMemClass.coe_zero]
    exact f4_dividedPower_two_ad_rootVector_eq_zero_of_no_endpoint
      (f4SignedSimpleRootIndex k) β (by
        exact hopp) hno
  rw [f4ModularRootVector_eq, f4ModularDividedAdjointSquare_tmul, hintegral,
    TensorProduct.tmul_zero]

/-- For a long source and a non-opposite long-root lift, the second divided-power quotient column
is zero. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_rootVector_eq_zero_of_long
    (k : Fin 4 ⊕ Fin 4) (β : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 2)
    (hβ : f4Length β = 2)
    (hopp : β ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k)) :
    f4ShortRootSubspace.mkQ
      (f4ModularDividedAdjointSquare k (f4ModularRootVector β)) = 0 := by
  rw [f4ModularDividedAdjointSquare_rootVector_eq_zero_of_long k β hα hβ hopp,
    map_zero]

/-- For a short source and long-root lift, absence of the transported target edge forces the
second divided-power quotient column to vanish. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_rootVector_eq_zero_of_no_specialMap_edge
    (k : Fin 4 ⊕ Fin 4) (β : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 1)
    (hβ : f4Length β = 2)
    (hopp : β ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k))
    (hno : ∀ δ : Fin 48, f4Length δ = 1 →
      f4SimplyConnectedRootDatum.root δ ≠
        f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
          f4SimplyConnectedRootDatum.root
            (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k))) :
    f4ShortRootSubspace.mkQ
      (f4ModularDividedAdjointSquare k (f4ModularRootVector β)) = 0 := by
  have hspecial :
      f4Length (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k)) = 2 := by
    simpa only [f4SpecialIsogenyIndexEquiv_apply] using
      (f4Length_specialIsogenyIndex_eq_two_iff
        (f4SignedSimpleRootIndex k)).2 hα
  have hzero := f4ModularDividedAdjointSquare_rootVector_eq_zero_of_no_endpoint k β hopp
    (fun γ hγ ↦ by
      have hγlong := (f4_pairings_of_long_add_two_short
        (f4SignedSimpleRootIndex k) β γ hα hβ hγ).2.2
      have hγshort : f4Length (f4SpecialIsogenyIndexEquiv γ) = 1 := by
        simpa only [f4SpecialIsogenyIndexEquiv_apply] using
          (f4Length_specialIsogenyIndex_eq_one_iff γ).2 hγlong
      apply hno (f4SpecialIsogenyIndexEquiv γ) hγshort
      apply (f4_root_add_smul_iff_specialIsogenyIndexEquiv_root_add
        (f4SignedSimpleRootIndex k) β γ hβ hγlong).1
      simpa only [hspecial] using hγ)
  rw [hzero, map_zero]

/-- A short-source, long-to-long divided-square column survives in the quotient with unit
coefficient. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_rootVector_of_long_add_two_short
    (k : Fin 4 ⊕ Fin 4) (β γ : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 1)
    (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (2 : ℤ) • f4SimplyConnectedRootDatum.root (f4SignedSimpleRootIndex k)) :
    f4ShortRootSubspace.mkQ
        (f4ModularDividedAdjointSquare k (f4ModularRootVector β)) =
      f4ShortRootSubspace.mkQ (f4ModularRootVector γ) := by
  rw [f4ModularDividedAdjointSquare_rootVector_of_long_add_two_short k β γ hα hβ h]

/-- The special root permutation turns a short-source quadratic quotient column into an
ordinary root-addition edge on the target side. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_rootVector_of_specialMap_add
    (k : Fin 4 ⊕ Fin 4) (β γ : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 1)
    (hβ : f4Length β = 2) (hγ : f4Length γ = 2)
    (hmap : f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv γ) =
      f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
        f4SimplyConnectedRootDatum.root
          (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k))) :
    f4ShortRootSubspace.mkQ
        (f4ModularDividedAdjointSquare k (f4ModularRootVector β)) =
      f4ShortRootSubspace.mkQ (f4ModularRootVector γ) := by
  have hsource :=
    (f4_root_add_smul_iff_specialIsogenyIndexEquiv_root_add
      (f4SignedSimpleRootIndex k) β γ hβ hγ).2 hmap
  have hspecial :
      f4Length (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k)) = 2 :=
    by
      simpa only [f4SpecialIsogenyIndexEquiv_apply] using
        (f4Length_specialIsogenyIndex_eq_two_iff
          (f4SignedSimpleRootIndex k)).2 hα
  apply f4ShortRootSubspace_mkQ_dividedSquare_rootVector_of_long_add_two_short
    k β γ hα hβ
  simpa only [hspecial] using hsource

/-- The opposite-root divided-square column descends to the class of the source root vector. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_rootVector_opposite
    (k : Fin 4 ⊕ Fin 4) :
    f4ShortRootSubspace.mkQ
        (f4ModularDividedAdjointSquare k
          (f4ModularRootVector (f4OppositeRootIndex (f4SignedSimpleRootIndex k)))) =
      f4ShortRootSubspace.mkQ
        (f4ModularRootVector (f4SignedSimpleRootIndex k)) := by
  rw [f4ModularDividedAdjointSquare_rootVector_opposite]

/-- Every simple-coroot lift has zero second divided-power column in the quotient. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_simpleCoroot_eq_zero
    (k : Fin 4 ⊕ Fin 4) (i : Fin F4.rank) :
    f4ShortRootSubspace.mkQ
        (f4ModularDividedAdjointSquare k (f4ModularSimpleCoroot i)) = 0 := by
  rw [f4ModularDividedAdjointSquare_simpleCoroot_eq_zero, map_zero]


end

end TauCeti.DynkinType
