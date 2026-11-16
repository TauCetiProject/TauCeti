/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Descent

/-!
# The unipotent radical and reductivity

This file connects the construction of the geometric unipotent radical to the definition of a
reductive finite-type affine group. It records that reductivity is equivalent to smoothness,
geometric connectedness, and triviality of the unipotent radical after base change to an
algebraic closure; over a perfect field, Galois descent of the unipotent radical reduces this to
triviality of the unipotent radical over the ground field. It also records that the unipotent
radical of a reductive group over its ground field is trivial.

## Main declarations

* `reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation`:
  reductivity is equivalent to smoothness, geometric connectedness, and triviality of the
  geometric unipotent radical.
* `reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation`: over a
  perfect field, reductivity is equivalent to smoothness, geometric connectedness, and triviality
  of the unipotent radical over the ground field.
* `TauCeti.reductiveCommHopfAlgProperty.unipotentRadicalDefiningIdeal_eq_augmentation`:
  a reductive group's unipotent radical over the ground field is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.45--6.46 and Proposition 19.9.
* A. Borel, *Linear Algebraic Groups*, §11.21.
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

/-- Over a perfect field, reductivity is equivalent to smoothness, geometric connectedness, and
triviality of the unipotent radical over the ground field. -/
theorem reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation
    (k : Type u) [Field k] [PerfectField k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    reductiveCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        geometricallyConnectedCommHopfAlgProperty k H.obj ∧
          FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H =
            HopfIdeal.augmentation k H := by
  rw [reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation,
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff]

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

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
