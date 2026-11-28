/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import TauCeti.CategoryTheory.Simple.Classes

/-!
# Isomorphism classes of simple summands of the tensor unit

`TauCeti.UnitSimpleClasses C` is the type of isomorphism classes of simple objects admitting a
nonzero morphism into the tensor unit `𝟙_ C`. This lightweight module provides the definition,
constructors (`mkOfHomNeZero`, `unit`), monoidal equivalence transport (`equiv`), and uniqueness
when `𝟙_ C` is simple (`instUnique`), without importing finite semisimplicity or biproduct
decompositions.

## Main declarations

* `TauCeti.UnitSimpleClasses`: isomorphism classes of simple summands of `𝟙_ C`.
* `TauCeti.UnitSimpleClasses.mkOfHomNeZero`, `unit`: constructors from a nonzero morphism to `𝟙_ C`
  and from `[Simple (𝟙_ C)]`.
* `TauCeti.UnitSimpleClasses.equiv`: transport along a monoidal equivalence.
* `TauCeti.UnitSimpleClasses.instUnique`: uniqueness when `𝟙_ C` is simple.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti

section Basic

variable (C : Type u₁) [Category.{v₁} C] [HasZeroMorphisms C] [MonoidalCategory C]

/-- The isomorphism classes of simple summands of the tensor unit `𝟙_ C`, realized as the simple
classes whose representative admits a nonzero morphism to `𝟙_ C`. -/
abbrev UnitSimpleClasses :=
  {I : SimpleClasses C // ∃ f : I.repr ⟶ 𝟙_ C, f ≠ 0}

namespace UnitSimpleClasses

variable {C}

/-- The chosen representative in `C` of a simple unit summand class. -/
abbrev repr (I : UnitSimpleClasses C) : C := I.val.repr
instance (I : UnitSimpleClasses C) : Simple I.repr := I.val.property

/-- Every unit summand representative admits a nonzero morphism to `𝟙_ C`. -/
theorem exists_hom_to_unit_ne_zero (I : UnitSimpleClasses C) :
    ∃ f : I.repr ⟶ 𝟙_ C, f ≠ 0 := I.property
@[simp] theorem eq_iff_nonempty_iso (I J : UnitSimpleClasses C) :
    I = J ↔ Nonempty (I.repr ≅ J.repr) := by
  rw [Subtype.ext_iff, SimpleClasses.eq_iff_nonempty_iso]

/-- Construct a `UnitSimpleClasses C` element from a nonzero morphism out of a simple object into
`𝟙_ C`. -/
def mkOfHomNeZero {X : C} [Simple X] {f : X ⟶ 𝟙_ C} (hf : f ≠ 0) : UnitSimpleClasses C :=
  ⟨SimpleClasses.classOf X, ⟨(SimpleClasses.classOfReprIso X).hom ≫ f,
    by simpa [comp_eq_zero_iff_of_epi] using hf⟩⟩
@[simp] theorem val_mkOfHomNeZero {X : C} [Simple X] {f : X ⟶ 𝟙_ C} (hf : f ≠ 0) :
    (mkOfHomNeZero hf).val = SimpleClasses.classOf X := (rfl)

/-- When `𝟙_ C` is simple, its isomorphism class as a unit summand. -/
def unit [Simple (𝟙_ C)] : UnitSimpleClasses C := mkOfHomNeZero (CategoryTheory.id_ne_zero (𝟙_ C))
@[simp] theorem val_unit [Simple (𝟙_ C)] :
    (unit (C := C)).val = SimpleClasses.classOf (𝟙_ C) := (rfl)

section Equivalence

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [MonoidalCategory D]

private theorem map_unit_hom_ne_zero (e : C ≌ D) [e.functor.Monoidal] (I : UnitSimpleClasses C) :
    ∃ g : (SimpleClasses.equiv e I.val).repr ⟶ 𝟙_ D, g ≠ 0 := by
  obtain ⟨f, hf⟩ := I.property
  have : e.functor.PreservesZeroMorphisms := e.functor.preservesZeroMorphisms_of_isLeftAdjoint
  let d := SimpleClasses.equivApplyReprIso e I.val; let u := Functor.Monoidal.εIso e.functor
  exact ⟨d.hom ≫ e.functor.map f ≫ u.inv, by
    simpa [comp_eq_zero_iff_of_epi, comp_eq_zero_iff_of_mono, e.functor.map_eq_zero_iff] using hf⟩

/-- A monoidal equivalence induces a bijection between the simple summand classes of the tensor
units. -/
def equiv (e : C ≌ D) [e.functor.Monoidal] : UnitSimpleClasses C ≃ UnitSimpleClasses D where
  toFun I := ⟨SimpleClasses.equiv e I.val, map_unit_hom_ne_zero e I⟩
  invFun J := letI := e.inverseMonoidal
    ⟨SimpleClasses.equiv e.symm J.val, map_unit_hom_ne_zero e.symm J⟩
  left_inv I := Subtype.ext (SimpleClasses.equiv_symm_equiv e I.val)
  right_inv J := Subtype.ext (SimpleClasses.equiv_equiv_symm e J.val)
@[simp] theorem val_equiv_apply (e : C ≌ D) [e.functor.Monoidal] (I : UnitSimpleClasses C) :
    (equiv e I).val = SimpleClasses.equiv e I.val := (rfl)
@[simp] theorem equiv_symm (e : C ≌ D) [e.functor.Monoidal] :
    (equiv e).symm = @equiv D _ _ _ C _ _ _ e.symm e.inverseMonoidal := (rfl)
@[simp] theorem equiv_refl (I : UnitSimpleClasses C) :
    equiv (CategoryTheory.Equivalence.refl (C := C)) I = I :=
  Subtype.ext (SimpleClasses.equiv_refl I.val)
@[simp] theorem equiv_trans {E : Type u₃} [Category.{v₃} E] [HasZeroMorphisms E]
    [MonoidalCategory E] (e₁ : C ≌ D) (e₂ : D ≌ E) [e₁.functor.Monoidal] [e₂.functor.Monoidal]
    (I : UnitSimpleClasses C) : equiv (e₁.trans e₂) I = equiv e₂ (equiv e₁ I) :=
  Subtype.ext (SimpleClasses.equiv_trans e₁ e₂ I.val)

end Equivalence

end UnitSimpleClasses

end Basic

section SimpleUnit

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasKernels C]
  [MonoidalCategory C] [Simple (𝟙_ C)]

instance UnitSimpleClasses.instUnique : Unique (UnitSimpleClasses C) where
  default := UnitSimpleClasses.unit
  uniq I := Subtype.ext <| by
    rw [val_unit, ← SimpleClasses.classOf_repr I.val, SimpleClasses.classOf_eq_iff_exists_ne_zero]
    exact I.property

end SimpleUnit

end TauCeti
