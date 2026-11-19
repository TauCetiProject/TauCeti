/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.DividedAction
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

/-- The first adjoint action of a short root vanishes after quotienting by the short-root ideal. -/
@[simp] theorem f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_short
    (α : Fin 48) (hα : f4Length α = 1) (x : f4ModularChevalleyLieAlgebra) :
    (Submodule.Quotient.mk ⁅f4ModularRootVector α, x⁆ :
      f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, ← lie_skew (f4ModularRootVector α) x]
  exact Submodule.neg_mem _
    (f4ShortRootSubspace_lie_mem x
      (f4ModularRootVector_mem_shortRootSubspace α hα))

/-- The opposite-root first-order quotient column is the corresponding coroot lift. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_opposite (α : Fin 48) :
    f4ShortRootSubspace.mkQ
        ⁅f4ModularRootVector α, f4ModularRootVector (f4OppositeRootIndex α)⁆ =
      f4ShortRootSubspace.mkQ (f4ModularCoroot α) := by
  rw [f4Modular_lie_rootVector_opposite]

/-- The simple-coroot first-order column has the signed reduced Cartan coefficient. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_simpleCoroot
    (α : Fin 48) (i : Fin F4.rank) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, f4ModularSimpleCoroot i⁆ =
      -(f4SimplyConnectedRootDatum.pairing α
        (Fin.castAdd 44 (Fin.cast rank_F4 i)) : ZMod 2) •
          f4ShortRootSubspace.mkQ (f4ModularRootVector α) := by
  rw [f4Modular_lie_rootVector_simpleCoroot, map_smul]

/-- A non-opposite root column vanishes when its transported target edge is absent. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_no_specialMap_edge
    (α β : Fin 48) (hopp : β ≠ f4OppositeRootIndex α)
    (hno : ∀ δ : Fin 48, f4Length δ = 1 →
      f4SimplyConnectedRootDatum.root δ ≠
        f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
          f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv α)) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, f4ModularRootVector β⁆ = 0 := by
  by_cases hα : f4Length α = 1
  · exact (Submodule.mkQ_apply _ _).trans
      (f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_short α hα _)
  have hα := (f4Length_eq_one_or_eq_two α).resolve_left hα
  by_cases hβ : f4Length β = 1
  · exact (Submodule.mkQ_apply _ _).trans ((Submodule.Quotient.mk_eq_zero _).2
      (f4ShortRootSubspace_lie_mem _ (f4ModularRootVector_mem_shortRootSubspace β hβ)))
  have hβ := (f4Length_eq_one_or_eq_two β).resolve_left hβ
  let H := F4.cartanSubalgebra valid_F4
  have hsum := f4KillingRoot_add_ne_zero_of_ne_opposite α β
    ((ne_f4OppositeRootIndex_comm α β).mp hopp)
  have hbot : rootSpace H
      ((f4KillingRoot α : H → ℚ) + (f4KillingRoot β : H → ℚ)) = ⊥ := by
    by_contra hne
    obtain ⟨δ, hsource⟩ :=
      exists_f4_root_eq_add_of_rootSpace_ne_bot α β hsum hne
    have hδlong : f4Length δ = 2 :=
      f4Length_eq_two_of_root_eq_add_of_long_long α β δ hα hβ hsource
    have hδshort := (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff δ).2 hδlong
    apply hno (f4SpecialIsogenyIndexEquiv δ) hδshort
    exact (f4_root_add_iff_specialIsogenyIndexEquiv_root_add_of_long
      α β δ hα hβ hδlong).1 hsource
  exact (congrArg f4ShortRootSubspace.mkQ
    (f4Modular_lie_rootVector_eq_zero_of_rootSpace_add_eq_bot α β hbot)).trans (map_zero _)

/-- Transport a target root edge to a first-order quotient column between source roots of equal
length. Both sides vanish when the sources are short, since the target `γ` is then short, and when
the sources are long but `γ` is short. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_of_specialMap_add
    (α β γ : Fin 48) (hαβ : f4Length α = f4Length β)
    (hmap : f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv γ) =
      f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
        f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv α)) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, f4ModularRootVector β⁆ =
      f4ShortRootSubspace.mkQ (f4ModularRootVector γ) := by
  by_cases hα : f4Length α = 1
  · have hγ' := f4Length_eq_two_of_root_eq_add_of_long_long _ _ _
      ((f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff α).2 hα)
      ((f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff β).2 (hαβ.symm.trans hα)) hmap
    exact ((Submodule.mkQ_apply _ _).trans
      (f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_short α hα _)).trans
        (f4ShortRootSubspace_mkQ_rootVector_eq_zero_of_short γ
          ((f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff γ).1 hγ')).symm
  have hα := (f4Length_eq_one_or_eq_two α).resolve_left hα
  have hβ := hαβ.symm.trans hα
  by_cases hγ : f4Length γ = 1
  · have hγ' := (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff γ).2 hγ
    refine (f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_no_specialMap_edge α β ?_
      fun δ hδ hδeq => ?_).trans (f4ShortRootSubspace_mkQ_rootVector_eq_zero_of_short γ hγ).symm
    · -- the special permutation commutes with negation, so an opposite pair would sum to zero
      rintro rfl
      rw [f4SpecialIsogenyIndexEquiv_f4OppositeRootIndex, f4OppositeRootIndex_eq_reflectionPerm,
        f4SimplyConnectedRootDatum.root_reflectionPerm,
        f4SimplyConnectedRootDatum.reflection_apply_self, neg_add_cancel] at hmap
      exact f4SimplyConnectedRootDatum.ne_zero _ hmap
    · have hδγ := f4SimplyConnectedRootDatum.root.injective (hδeq.trans hmap.symm)
      rw [hδγ, hγ'] at hδ
      omega
  have hγ := (f4Length_eq_one_or_eq_two γ).resolve_left hγ
  exact congrArg f4ShortRootSubspace.mkQ
    (f4Modular_lie_rootVector_of_add_of_length_eq α β γ (hβ.trans hγ.symm)
      ((f4_root_add_iff_specialIsogenyIndexEquiv_root_add_of_long α β γ hα hβ hγ).2 hmap))

/-- A long-source divided-square column on a non-opposite root lift vanishes. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_rootVector_eq_zero_of_long
    (k : Fin 4 ⊕ Fin 4) (β : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 2)
    (hopp : β ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k)) :
    f4ShortRootSubspace.mkQ
      (f4ModularDividedAdjointSquare k (f4ModularRootVector β)) = 0 :=
  (congrArg f4ShortRootSubspace.mkQ
    (f4ModularDividedAdjointSquare_rootVector_eq_zero_of_dividedPower_eq_zero k β
      (f4_dividedPower_two_ad_rootVector_eq_zero_of_long _ β hα hopp))).trans (map_zero _)

/-- The exceptional divided-square quotient column is the source root-vector lift. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_rootVector_opposite (k : Fin 4 ⊕ Fin 4) :
    f4ShortRootSubspace.mkQ (f4ModularDividedAdjointSquare k
      (f4ModularRootVector (f4OppositeRootIndex (f4SignedSimpleRootIndex k)))) =
    f4ShortRootSubspace.mkQ (f4ModularRootVector (f4SignedSimpleRootIndex k)) := by
  rw [f4ModularDividedAdjointSquare_rootVector_opposite]

/-- Every simple-coroot divided-square quotient column vanishes. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_simpleCoroot_eq_zero
    (k : Fin 4 ⊕ Fin 4) (i : Fin F4.rank) :
    f4ShortRootSubspace.mkQ
      (f4ModularDividedAdjointSquare k (f4ModularSimpleCoroot i)) = 0 := by
  rw [f4ModularDividedAdjointSquare_simpleCoroot_eq_zero, map_zero]

/-- A short-source divided-square column vanishes without a transported target edge. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_rootVector_eq_zero_of_no_specialMap_edge
    (k : Fin 4 ⊕ Fin 4) (β : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 1)
    (hno : ∀ δ : Fin 48, f4Length δ = 1 →
      f4SimplyConnectedRootDatum.root δ ≠
        f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
          f4SimplyConnectedRootDatum.root
            (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k))) :
    f4ShortRootSubspace.mkQ
      (f4ModularDividedAdjointSquare k (f4ModularRootVector β)) = 0 := by
  by_cases hβ : f4Length β = 1
  · by_cases hopp : β = f4OppositeRootIndex (f4SignedSimpleRootIndex k)
    · rw [hopp, f4ShortRootSubspace_mkQ_dividedSquare_rootVector_opposite]
      exact f4ShortRootSubspace_mkQ_rootVector_eq_zero_of_short _ hα
    exact (congrArg f4ShortRootSubspace.mkQ
      (f4ModularDividedAdjointSquare_rootVector_eq_zero_of_short k β hβ hopp)).trans (map_zero _)
  · have hβ := (f4Length_eq_one_or_eq_two β).resolve_left hβ
    have hzero := f4ModularDividedAdjointSquare_rootVector_eq_zero_of_no_endpoint k β
      (fun γ hγ ↦ by
        have hγlong := (f4_pairings_of_long_add_two_short
          (f4SignedSimpleRootIndex k) β γ hα hβ hγ).2.2
        have hγshort := (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff γ).2 hγlong
        apply hno (f4SpecialIsogenyIndexEquiv γ) hγshort
        exact (f4_root_add_two_iff_specialIsogenyIndexEquiv_root_add_of_short
          (f4SignedSimpleRootIndex k) β γ hα hγlong).1 hγ)
    exact (congrArg f4ShortRootSubspace.mkQ hzero).trans (map_zero _)

/-- Transport a target root edge to a short-source divided-square quotient column. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_rootVector_of_specialMap_add
    (k : Fin 4 ⊕ Fin 4) (β γ : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 1)
    (hmap : f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv γ) =
      f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv β) +
        f4SimplyConnectedRootDatum.root
          (f4SpecialIsogenyIndexEquiv (f4SignedSimpleRootIndex k))) :
    f4ShortRootSubspace.mkQ
        (f4ModularDividedAdjointSquare k (f4ModularRootVector β)) =
      f4ShortRootSubspace.mkQ (f4ModularRootVector γ) := by
  by_cases hγ : f4Length γ = 1
  · refine (f4ShortRootSubspace_mkQ_dividedSquare_rootVector_eq_zero_of_no_specialMap_edge
      k β hα fun δ hδ hδeq => ?_).trans
        (f4ShortRootSubspace_mkQ_rootVector_eq_zero_of_short γ hγ).symm
    have hδγ := f4SimplyConnectedRootDatum.root.injective (hδeq.trans hmap.symm)
    have h2 := (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff γ).2 hγ
    rw [← hδγ, hδ] at h2
    omega
  · have hγ := (f4Length_eq_one_or_eq_two γ).resolve_left hγ
    exact congrArg f4ShortRootSubspace.mkQ
      (f4ModularDividedAdjointSquare_rootVector_of_long_add_two_short k β γ
        ((f4_root_add_two_iff_specialIsogenyIndexEquiv_root_add_of_short
          (f4SignedSimpleRootIndex k) β γ hα hγ).2 hmap))

end

end TauCeti.DynkinType
