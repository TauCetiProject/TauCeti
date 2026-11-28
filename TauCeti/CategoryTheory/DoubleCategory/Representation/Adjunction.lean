/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.LocallyInduced.Adjunction
public import TauCeti.CategoryTheory.DoubleCategory.Representation.Bicategory

/-!
# Adjunction transfer through a horizontal representation

An adjunction between singleton paths corresponds to an adjunction between the same generators
in the represented horizontal bicategory. The correspondence includes the specified unit and
counit, conjugated by the binary and nullary comparison cells. Its inverse is the action of
singleton inclusion on adjunctions, and the two round trips recover the entire adjunction data.

Only a horizontal representation is needed. In particular the construction applies when the
vertical generating quiver is empty; it does not ask for nonexistent vertical identity
generators. Applying the same construction to the transpose transfers vertical adjunctions.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; Proposition 2.7.
-/

public section

universe s u h v

namespace TauCeti.StrictDoubleCategory.HorizontalRepresentation

open CategoryTheory
open scoped Bicategory

variable {O : Type u} {H : Quiver.{h} O} {V : Category.{v} O}
  {D : StrictDoubleCategory.{s} O (pathCategory O H) V}
  (R : D.HorizontalRepresentation) {a b : R.GeneratorBicategory}
  {f : a ⟶ b} {g : b ⟶ a}

/-- Transfer specified adjunctions between singleton paths to adjunctions between generators.
The inverse is Mathlib's action of the singleton inclusion pseudofunctor on adjunctions. -/
def singletonAdjunctionEquiv :
    (R.singletonPseudofunctor.map f ⊣ R.singletonPseudofunctor.map g) ≃ (f ⊣ g) :=
  R.inductionData.adjunctionEquiv.symm

/-- The transferred unit starts at the chosen identity generator and ends at the chosen
composite, using the inverse nullary comparison and the forward binary comparison. -/
@[simp]
theorem singletonAdjunctionEquiv_unit_hom
    (adj : R.singletonPseudofunctor.map f ⊣ R.singletonPseudofunctor.map g) :
    (R.singletonAdjunctionEquiv adj).unit.hom =
      (R.unitIso a.obj).inv ≫ adj.unit ≫ (R.mulIso f g).hom :=
  (congrArg (fun adj ↦ adj.unit.hom)
    (R.inductionData.adjunctionEquiv_symm_apply adj)).trans
      (R.inductionData.liftAdjunction_unit_hom adj)

/-- The transferred counit uses the inverse binary comparison and the forward nullary
comparison. The right adjoint occurs first in this binary composite. -/
@[simp]
theorem singletonAdjunctionEquiv_counit_hom
    (adj : R.singletonPseudofunctor.map f ⊣ R.singletonPseudofunctor.map g) :
    (R.singletonAdjunctionEquiv adj).counit.hom =
      (R.mulIso g f).inv ≫ adj.counit ≫ (R.unitIso b.obj).hom :=
  (congrArg (fun adj ↦ adj.counit.hom)
    (R.inductionData.adjunctionEquiv_symm_apply adj)).trans
      (R.inductionData.liftAdjunction_counit_hom adj)

/-- The inverse transfer is the existing pseudofunctor action on specified adjunctions. -/
@[simp]
theorem singletonAdjunctionEquiv_symm_apply (adj : f ⊣ g) :
    R.singletonAdjunctionEquiv.symm adj = R.singletonPseudofunctor.mapAdjunction adj :=
  R.inductionData.adjunctionEquiv_apply adj

/-- The unit on singleton paths reverses the changes made by the forward transfer. -/
theorem singletonAdjunctionEquiv_symm_unit (adj : f ⊣ g) :
    (R.singletonAdjunctionEquiv.symm adj).unit =
      (R.unitIso a.obj).hom ≫ adj.unit.hom ≫ (R.mulIso f g).inv := by
  rw [singletonAdjunctionEquiv_symm_apply]
  rfl

/-- The counit on singleton paths reverses the changes made by the forward transfer. -/
theorem singletonAdjunctionEquiv_symm_counit (adj : f ⊣ g) :
    (R.singletonAdjunctionEquiv.symm adj).counit =
      (R.mulIso g f).hom ≫ adj.counit.hom ≫ (R.unitIso b.obj).inv := by
  rw [singletonAdjunctionEquiv_symm_apply]
  rfl

end TauCeti.StrictDoubleCategory.HorizontalRepresentation
