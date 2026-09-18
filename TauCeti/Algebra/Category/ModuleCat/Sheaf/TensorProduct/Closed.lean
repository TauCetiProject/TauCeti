/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Closed.Preadditive

/-!
# The closed monoidal category of sheaves of modules

Let `R` be a sheaf of commutative rings on a small site. This file makes sheaves of `R`-modules
into a closed symmetric monoidal category. Consequently, tensoring on the left has the internal
Hom functor as a right adjoint; Mathlib's standard `ihom.adjunction`, `ihom.ev`, and `ihom.coev`
provide the tensor--Hom adjunction, evaluation, and coevaluation.

Presheaves of modules form a closed monoidal category by
`TauCeti.PresheafOfModules.monoidalClosed`. Day's reflection theorem transports this closed
structure across the reflective sheafification adjunction. Thus the internal Hom of sheaves is
the sheafification of the presheaf internal Hom.

## Main declarations

* `TauCeti.SheafOfModules.presheafMonoidalClosed` transfers the closed structure of
  `TauCeti.PresheafOfModules.monoidalClosed` to presheaves of modules over the ring presheaf
  underlying `R`;
* `TauCeti.SheafOfModules.monoidalClosed` gives the closed structure on sheaves of modules;
* `TauCeti.SheafOfModules.monoidalPreadditive` makes tensoring additive in each variable;
* `SheafOfModules.ihom_obj` identifies its internal Hom object with the sheafification of the
  presheaf internal Hom.

The use of the special adjoint functor theorem and Day reflection follows the construction of
closed monoidal structures on sheaf categories in Mathlib's
`CategoryTheory.Monoidal.Braided.Reflection` and `Condensed.Light.Monoidal`.
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed PresheafOfModules

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})

/-- The closed monoidal structure on presheaves of modules over the ring presheaf underlying `R`,
transferred from `TauCeti.PresheafOfModules.monoidalClosed` so that instance search finds it at
`(ringCatSheaf R).obj`. -/
instance presheafMonoidalClosed :
    MonoidalClosed (PresheafOfModules.{u} (ringCatSheaf R).obj) :=
  inferInstanceAs (MonoidalClosed (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat.{u})))

/-- The closed symmetric monoidal structure on sheaves of `R`-modules. It is obtained from the
closed structure on presheaves of modules by Day's reflection theorem. -/
instance monoidalClosed : MonoidalClosed (SheafOfModules.{u} (ringCatSheaf R)) :=
  Monoidal.Reflective.monoidalClosed
    (PresheafOfModules.sheafificationAdjunction (R := ringCatSheaf R)
      (R₀ := (ringCatSheaf R).obj) (J := J) (𝟙 (ringCatSheaf R).obj))

/-- The tensor product of sheaves of modules is additive in each variable. -/
instance monoidalPreadditive : MonoidalPreadditive (SheafOfModules.{u} (ringCatSheaf R)) :=
  monoidalPreadditive_of_monoidalClosed _

variable {R}

/-- The internal Hom of sheaves of modules is the sheafification of the internal Hom of their
underlying presheaves of modules. -/
@[simp]
theorem _root_.SheafOfModules.ihom_obj
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (ihom M).obj N =
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
        ((ihom M.val).obj N.val) := rfl

/-- On morphisms, the internal Hom of sheaves of modules is induced by sheafification from the
internal Hom of presheaves of modules. -/
@[simp]
theorem _root_.SheafOfModules.ihom_map
    (M : SheafOfModules.{u} (ringCatSheaf R)) {N P : SheafOfModules.{u} (ringCatSheaf R)}
    (f : N ⟶ P) :
    (ihom M).map f =
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        ((ihom M.val).map f.val) := rfl

end SheafOfModules

end

end TauCeti
