/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange

/-!
# The unipotent radical and reductivity

This file connects the construction of the geometric unipotent radical to the definition of a
reductive finite-type affine group. It records that reductivity is equivalent to smoothness,
geometric connectedness, and triviality of the unipotent radical after base change to an
algebraic closure. It also records that the unipotent radical of a reductive group over its
ground field is trivial.

## Main declarations

* `reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation`:
  reductivity is equivalent to smoothness, geometric connectedness, and triviality of the
  geometric unipotent radical.
* `TauCeti.reductiveCommHopfAlgProperty.unipotentRadicalDefiningIdeal_eq_augmentation`:
  a reductive group's unipotent radical over the ground field is trivial.
* `TauCeti.reductiveCommHopfAlgProperty.of_baseChange_algebraicClosure`: a finite-type affine
  group is reductive once its geometric fibre is.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.
-/

public section

open scoped TensorProduct

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

/-- A finite-type affine group over `k` is reductive once its base change to an algebraic closure
of `k` is reductive. -/
theorem of_baseChange_algebraicClosure
    (hH : reductiveCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)) :
    reductiveCommHopfAlgProperty k H := by
  let _ : Algebra.Smooth (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H.obj) :=
    smooth_baseChange_obj hH.smooth
  exact (reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
      k H).2
    ⟨Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := k) (S := H.obj)
        (AlgebraicClosure k),
      geometricallyConnectedCommHopfAlgProperty.of_baseChange k _ H.obj hH.geometricallyConnected,
      hH.unipotentRadicalDefiningIdeal_eq_augmentation⟩

end reductiveCommHopfAlgProperty

end

end TauCeti
