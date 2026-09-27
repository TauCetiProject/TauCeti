/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.D4.EulerForm
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Correspondence

/-!
# The `D₄` quiver has finite representation type

The Tits form of the `D₄` quiver is positive definite (`TauCeti.Quiver.D4.titsForm_posDef`), so
the Gabriel correspondence identifies its finite-dimensional indecomposable representations up to
isomorphism with the twelve positive roots counted by `TauCeti.Quiver.D4.card_positiveRoots`.

This is the first case of the affirming half of Gabriel's dichotomy that is not settled by an
explicit classification. The `A₂` quiver was: `TauCeti.isFiniteRepType_kronecker` reads its finite
representation type off the list of its three indecomposables, in
`TauCeti.card_skeleton_indecomposable_kronecker`. No such list is available for `D₄`, and none is
needed; the count comes from the general correspondence and the explicit positive-root calculation.

## Main results

* `TauCeti.isFiniteRepType_d4`: **the `D₄` quiver has finite representation type over every
  field.**
* `TauCeti.card_skeleton_indecomposable_d4`: it has exactly twelve finite-dimensional
  indecomposable representations up to isomorphism.

## References

This is the affirming half of the “`D₄` quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose Layer 5 count
milestone asks for the twelve indecomposables of `D₄`. See Assem--Simson--Skowroński, *Elements of
the Representation Theory of Associative Algebras* I, Ch. VII.
-/

public section

namespace TauCeti

open CategoryTheory

universe u x

/-- **The `D₄` quiver has finite representation type over every field.** Its Tits form is positive
definite, so `TauCeti.isFiniteRepType_of_titsForm_posDef` bounds the isomorphism classes of its
finite-dimensional indecomposables by the roots of that form. -/
theorem isFiniteRepType_d4 (k : Type u) [Field k] :
    IsFiniteRepType.{u, 0, 1, max 1 x} k Quiver.D4 :=
  isFiniteRepType_of_titsForm_posDef Quiver.D4.titsForm_posDef

/-- **The `D₄` quiver has exactly twelve finite-dimensional indecomposable representations up
to isomorphism**, one for each positive root of its Tits form. -/
theorem card_skeleton_indecomposable_d4 (k : Type u) [Field k] :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, 0, 1, max u 1 x} k Quiver.D4 ↦
        IsFinDim k Quiver.D4 M ∧ Indecomposable M))) = 12 :=
  (card_skeleton_indecomposable_eq_card_positiveRoots
    Quiver.D4.titsForm_posDef).trans Quiver.D4.card_positiveRoots

end TauCeti
