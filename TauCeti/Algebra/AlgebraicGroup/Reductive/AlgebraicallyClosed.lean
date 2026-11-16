/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic

/-!
# Reductivity of the geometric fibre

This file records that the geometric fibre of a reductive affine group `G` is itself
reductive, deduced from the perfect-field characterization
`TauCeti.reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation` applied
to the algebraically closed field `AlgebraicClosure k`. This lets results over algebraically
closed fields be applied to the geometric fibre and then descended.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 6 and 19.
-/

public section

namespace TauCeti

universe u

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
