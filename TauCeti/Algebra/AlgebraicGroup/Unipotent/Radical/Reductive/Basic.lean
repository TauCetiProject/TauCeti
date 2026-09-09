/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange

/-!
# The unipotent radical and reductivity

This file connects the construction of the geometric unipotent radical to the definition of a
reductive finite-type affine group. It records that reductivity is equivalent to smoothness,
geometric connectedness, and triviality of the unipotent radical after base change to an
algebraic closure. It also records that triviality of the radical after any field extension
descends to the ground field.

## Main declarations

* `reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation`:
  reductivity is equivalent to smoothness, geometric connectedness, and triviality of the
  geometric unipotent radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation`:
  triviality of the unipotent radical after a field extension descends to the ground field.
* `TauCeti.reductiveCommHopfAlgProperty.unipotentRadicalDefiningIdeal_eq_augmentation`:
  a reductive group's unipotent radical over the ground field is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.

This connects Layer 5, "The unipotent radical", to the definition of reductivity in Layer 6 of
the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

universe u

noncomputable section

/-- A finite-type affine group is reductive exactly when it is smooth and geometrically
connected and its geometric unipotent radical is trivial. -/
theorem reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    reductiveCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        geometricallyConnectedCommHopfAlgProperty k H.obj ∧
          FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) =
            HopfIdeal.augmentation (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  rw [reductiveCommHopfAlgProperty_iff]
  constructor
  · rintro ⟨hsmooth, hconnected, htrivial⟩
    refine ⟨hsmooth, hconnected, ?_⟩
    rw [FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff]
    intro I hI
    exact htrivial I hI.isNormal hI.geometricallyConnected hI.smoothUnipotent
  · rintro ⟨hsmooth, hconnected, hradical⟩
    refine ⟨hsmooth, hconnected, ?_⟩
    intro I hnormal hIconnected hIunipotent
    exact (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)).mp hradical I
        (HopfIdeal.IsUnipotentRadicalCandidate.mk hnormal hIconnected hIunipotent)

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

namespace FiniteTypeCommHopfAlgCat

/-- Triviality of the unipotent radical after base change to a field extension descends to the
ground field. -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation
    {K : Type u} [Field K] [Algebra k K]
    (hgeometric :
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
          (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) =
        HopfIdeal.augmentation K
          (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H =
      HopfIdeal.augmentation k H := by
  apply CommHopfAlgCat.baseChangeHopfIdeal_injective (K := K)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  apply le_antisymm
  · exact HopfIdeal.le_augmentation K _ _
  · rw [← hgeometric]
    exact FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_le H

end FiniteTypeCommHopfAlgCat

namespace reductiveCommHopfAlgProperty

open FiniteTypeCommHopfAlgCat

/-- The unipotent radical of a reductive finite-type affine group over its ground field is the
identity subgroup. -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation
    (hH : reductiveCommHopfAlgProperty k H) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H =
      HopfIdeal.augmentation k H :=
  unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation
      (K := AlgebraicClosure k)
      ((reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
        k H).mp hH |>.2.2)

end reductiveCommHopfAlgProperty

end

end TauCeti
