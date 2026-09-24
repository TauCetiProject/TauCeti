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

/-- A long-root lift is the quotient basis vector indexed by its short special-map image. -/
theorem f4ShortRootSubspace_mkQ_rootVector_eq_quotientBasis
    (γ : Fin 48) (hγ : f4Length γ = 2) :
    f4ShortRootSubspace.mkQ (f4ModularRootVector γ) =
      f4ShortRootQuotientBasis
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl
          ⟨f4SpecialIsogenyIndexEquiv γ, by
            exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff γ).2 hγ⟩)) := by
  rw [f4ShortRootQuotientBasis_symm_inl]
  apply congrArg f4ShortRootSubspace.mkQ
  apply congrArg f4ModularRootVector
  exact (f4SpecialIsogenyIndexEquiv_f4SpecialIsogenyIndexEquiv γ).symm

/-- The first adjoint action of a short root vanishes after quotienting by the short-root ideal. -/
theorem f4ShortRootSubspace_mkQ_lie_rootVector_eq_zero_of_short
    (α : Fin 48) (hα : f4Length α = 1) (x : f4ModularChevalleyLieAlgebra) :
    f4ShortRootSubspace.mkQ ⁅f4ModularRootVector α, x⁆ = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [← lie_skew (f4ModularRootVector α) x]
  exact Submodule.neg_mem _
    (f4ShortRootSubspace_lie_mem x
      (f4ModularRootVector_mem_shortRootSubspace α hα))

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
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff α).2 hα
  apply congrArg f4ShortRootSubspace.mkQ
  exact f4Modular_lie_rootVector_of_add_of_length_eq α β γ
    (hβ.trans hγ.symm) (by simpa only [hspecial, one_zsmul] using hsource)

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
  have hopp' : α ≠ f4OppositeRootIndex β :=
    (ne_f4OppositeRootIndex_comm α β).mp hopp
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
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff δ).2 hδlong
    apply hno (f4SpecialIsogenyIndexEquiv δ) hδshort
    apply (f4_root_add_smul_iff_specialIsogenyIndexEquiv_root_add
      α β δ hβ hδlong).1
    have hspecial : f4Length (f4SpecialIsogenyIndexEquiv α) = 1 := by
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff α).2 hα
    simpa only [hspecial, one_zsmul] using hsource
  rw [f4Modular_lie_rootVector_eq_zero_of_rootSpace_add_eq_bot α β hbot, map_zero]

/-- For a long source and a non-opposite long-root lift, the second divided-power quotient column
is zero. -/
theorem f4ShortRootSubspace_mkQ_dividedSquare_rootVector_eq_zero_of_long
    (k : Fin 4 ⊕ Fin 4) (β : Fin 48)
    (hα : f4Length (f4SignedSimpleRootIndex k) = 2)
    (hβ : f4Length β = 2)
    (hopp : β ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k)) :
    f4ShortRootSubspace.mkQ
      (f4ModularDividedAdjointSquare k (f4ModularRootVector β)) = 0 := by
  rw [f4ModularDividedAdjointSquare_rootVector_eq_zero_of_dividedPower_eq_zero k β
    (f4_dividedPower_two_ad_rootVector_eq_zero_of_long
      (f4SignedSimpleRootIndex k) β hα hβ hopp), map_zero]

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
    exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff (f4SignedSimpleRootIndex k)).2 hα
  have hzero := f4ModularDividedAdjointSquare_rootVector_eq_zero_of_no_endpoint k β hopp
    (fun γ hγ ↦ by
      have hγlong := (f4_pairings_of_long_add_two_short
        (f4SignedSimpleRootIndex k) β γ hα hβ hγ).2.2
      have hγshort : f4Length (f4SpecialIsogenyIndexEquiv γ) = 1 := by
        exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_one_iff γ).2 hγlong
      apply hno (f4SpecialIsogenyIndexEquiv γ) hγshort
      apply (f4_root_add_smul_iff_specialIsogenyIndexEquiv_root_add
        (f4SignedSimpleRootIndex k) β γ hβ hγlong).1
      simpa only [hspecial] using hγ)
  rw [hzero, map_zero]

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
      exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff (f4SignedSimpleRootIndex k)).2 hα
  apply congrArg f4ShortRootSubspace.mkQ
  exact f4ModularDividedAdjointSquare_rootVector_of_long_add_two_short
    k β γ hα hβ (by simpa only [hspecial] using hsource)



end

end TauCeti.DynkinType
