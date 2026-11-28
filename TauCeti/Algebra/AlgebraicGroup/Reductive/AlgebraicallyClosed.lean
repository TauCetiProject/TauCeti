/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Descent

/-!
# Reductivity over perfect and algebraically closed fields

Over a perfect field `k`, `AlgebraicClosure k / k` is separable algebraic, so formation of the
unipotent radical commutes with passage to the geometric fibre
(`TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff`).
Reductivity can therefore be tested directly by triviality of the unipotent radical over `k`.

Since algebraically closed fields are perfect, this criterion applies in particular to
`AlgebraicClosure k`, showing that the geometric fibre of any reductive group is itself reductive.
Results proved over algebraically closed fields can thus be applied to the geometric fibre and
descended.

## Main declarations

* `TauCeti.reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation`: over a
  perfect field, reductivity is equivalent to smoothness, geometric connectedness and triviality of
  the unipotent radical over the ground field.
* `TauCeti.reductiveCommHopfAlgProperty.algebraicClosureBaseChange`: the geometric fibre of a
  reductive affine group is reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 6 and 19.
-/

public section

namespace TauCeti

universe u

/-- Over a perfect field, reductivity is equivalent to smoothness, geometric connectedness and
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

/-- The geometric fibre of a reductive affine group is reductive. -/
theorem reductiveCommHopfAlgProperty.algebraicClosureBaseChange
    {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : reductiveCommHopfAlgProperty k H) :
    reductiveCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  rw [reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation]
  let _ : Algebra.Smooth k H := hH.smooth
  exact ⟨inferInstance,
    geometricallyConnectedCommHopfAlgProperty.baseChange k (AlgebraicClosure k) H.obj
      hH.geometricallyConnected,
    ((reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
      k H).mp hH).2.2⟩

end TauCeti
