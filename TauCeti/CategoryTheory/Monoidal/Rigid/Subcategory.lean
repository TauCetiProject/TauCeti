/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Duality in full monoidal subcategories

An exact pairing between two objects of a monoidal category restricts to any full monoidal
subcategory containing both objects. Its evaluation and coevaluation are the same morphisms,
regarded in the full subcategory. Consequently an object and a chosen dual that both satisfy a
monoidal property remain dual to one another after imposing that property.

## Main declarations

* `CategoryTheory.ObjectProperty.exactPairingFullSubcategory`: an ambient exact pairing induces
  one in a full monoidal subcategory.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe v u

noncomputable section

namespace ObjectProperty

open _root_.CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {P : ObjectProperty C} [P.IsMonoidal]

/-- An exact pairing between the underlying objects of a full monoidal subcategory is an exact
pairing in that subcategory. -/
instance _root_.CategoryTheory.ObjectProperty.exactPairingFullSubcategory
    (X Y : P.FullSubcategory) [ExactPairing X.obj Y.obj] :
    ExactPairing X Y where
  coevaluation' := homMk (η_ X.obj Y.obj)
  evaluation' := homMk (ε_ X.obj Y.obj)
  coevaluation_evaluation' := by
    apply hom_ext
    exact ExactPairing.coevaluation_evaluation X.obj Y.obj
  evaluation_coevaluation' := by
    apply hom_ext
    exact ExactPairing.evaluation_coevaluation X.obj Y.obj

/-- The coevaluation of an ambient exact pairing, restricted to a full monoidal subcategory, is
the ambient coevaluation on underlying objects. -/
@[simp]
theorem _root_.CategoryTheory.ObjectProperty.exactPairingFullSubcategory_coevaluation_hom
    (X Y : P.FullSubcategory) [ExactPairing X.obj Y.obj] :
    (@ExactPairing.coevaluation P.FullSubcategory _ _ X Y
      (exactPairingFullSubcategory X Y)).hom = η_ X.obj Y.obj :=
  rfl

/-- The evaluation of an ambient exact pairing, restricted to a full monoidal subcategory, is
the ambient evaluation on underlying objects. -/
@[simp]
theorem _root_.CategoryTheory.ObjectProperty.exactPairingFullSubcategory_evaluation_hom
    (X Y : P.FullSubcategory) [ExactPairing X.obj Y.obj] :
    (@ExactPairing.evaluation P.FullSubcategory _ _ X Y
      (exactPairingFullSubcategory X Y)).hom = ε_ X.obj Y.obj :=
  rfl

end ObjectProperty

end

end TauCeti
