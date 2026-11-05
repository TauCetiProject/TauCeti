/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Duality in full monoidal subcategories

An exact pairing between two objects of a monoidal category restricts to any full monoidal
subcategory containing both objects: it is pulled back along the fully faithful monoidal
inclusion by `CategoryTheory.ExactPairing.ofFullyFaithful`. Its evaluation and coevaluation are
the ambient ones on underlying objects. Consequently an object and a chosen dual that both
satisfy a monoidal property remain dual to one another after imposing that property.

## Main declarations

* `CategoryTheory.ObjectProperty.exactPairingFullSubcategory`: an ambient exact pairing induces
  one in a full monoidal subcategory.
-/

public section

noncomputable section

namespace CategoryTheory.ObjectProperty

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] {P : ObjectProperty C} [P.IsMonoidal]

/-- An exact pairing between the underlying objects of a full monoidal subcategory is an exact
pairing in that subcategory, obtained by pulling back along the inclusion `P.ι`. -/
instance exactPairingFullSubcategory (X Y : P.FullSubcategory) [ExactPairing X.obj Y.obj] :
    ExactPairing X Y :=
  letI : ExactPairing (P.ι.obj X) (P.ι.obj Y) := inferInstanceAs (ExactPairing X.obj Y.obj)
  .ofFullyFaithful P.ι X Y

/-- The coevaluation of an ambient exact pairing, restricted to a full monoidal subcategory, is
the ambient coevaluation on underlying objects. -/
@[simp]
theorem exactPairingFullSubcategory_coevaluation_hom (X Y : P.FullSubcategory)
    [ExactPairing X.obj Y.obj] : (η_ X Y).hom = η_ X.obj Y.obj :=
  -- By definition of `ExactPairing.ofFullyFaithful`, the coevaluation is the preimage under `P.ι`
  -- of the ambient one composed with the (identity) monoidal constraints of `P.ι`.
  (P.ι.map_preimage _).trans (by simp [← Functor.Monoidal.inv_ε])

/-- The evaluation of an ambient exact pairing, restricted to a full monoidal subcategory, is
the ambient evaluation on underlying objects. -/
@[simp]
theorem exactPairingFullSubcategory_evaluation_hom (X Y : P.FullSubcategory)
    [ExactPairing X.obj Y.obj] : (ε_ X Y).hom = ε_ X.obj Y.obj :=
  -- As above, the evaluation is by definition a preimage under `P.ι`.
  (P.ι.map_preimage _).trans (by simp)

end CategoryTheory.ObjectProperty
