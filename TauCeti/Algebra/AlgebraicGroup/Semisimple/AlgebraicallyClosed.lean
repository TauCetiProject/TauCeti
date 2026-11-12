/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Semisimple
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Descent

/-!
# Semisimplicity over an algebraically closed field

Over an algebraically closed field, a smooth geometrically connected affine group is
semisimple exactly when its solvable radical over that field is trivial. The comparison
with the geometric definition uses descent of radical candidates along the isomorphism
from the ground field to its algebraic closure.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 21.
-/

public section

namespace TauCeti

universe u

/-- Over an algebraically closed field, semisimplicity can be tested using the solvable
radical over the ground field. -/
theorem semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_eq_augmentation
    (k : Type u) [Field k] [IsAlgClosed k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    semisimpleCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        geometricallyConnectedCommHopfAlgProperty k H.obj ∧
          FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal H =
            HopfIdeal.augmentation k H := by
  rw [semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation,
    ← FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_solvableRadicalDefiningIdeal_of_surjective H
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2,
    ← CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
    (CommHopfAlgCat.baseChangeHopfIdeal_injective (K := AlgebraicClosure k)).eq_iff

end TauCeti
