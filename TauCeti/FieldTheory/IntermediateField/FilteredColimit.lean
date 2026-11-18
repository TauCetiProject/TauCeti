/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# An algebraic extension as a filtered colimit of finite subextensions

The finite intermediate fields form a directed system under inclusion. For an algebraic
extension `L / K`, their inclusion cocone exhibits `L` as a colimit in commutative rings.
This supplies the affine inverse system used to descend finitely presented schemes over an
algebraic extension to a finite subextension.

## Main declarations

* `TauCeti.IntermediateField.FiniteSubextension`: finite intermediate fields ordered by inclusion.
* `TauCeti.IntermediateField.finiteSubextensionDiagram`: their diagram of commutative rings.
* `TauCeti.IntermediateField.isColimitFiniteSubextensionCocone`: the extension is its colimit.
-/

public section

open CategoryTheory Limits

namespace TauCeti.IntermediateField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- Intermediate fields of `L / K` that are finite-dimensional over `K`, ordered by inclusion. -/
abbrev FiniteSubextension := {E : IntermediateField K L // FiniteDimensional K E}

instance : Nonempty (FiniteSubextension K L) := ⟨⟨⊥, inferInstance⟩⟩

instance : IsDirected (FiniteSubextension K L) (· ≤ ·) where
  directed E F := by
    have := E.2
    have := F.2
    refine ⟨⟨E.1 ⊔ F.1, inferInstance⟩, ?_, ?_⟩
    · exact le_sup_left (a := E.1) (b := F.1)
    · exact le_sup_right (a := E.1) (b := F.1)

instance : IsFiltered (FiniteSubextension K L) :=
  isFiltered_of_directed_le_nonempty _

/-- The commutative rings underlying finite intermediate fields, with their inclusions. -/
def finiteSubextensionDiagram : FiniteSubextension K L ⥤ CommRingCat where
  obj E := .of E.1
  map f := CommRingCat.ofHom (_root_.IntermediateField.inclusion (leOfHom f)).toRingHom

/-- The inclusion cocone from finite subextensions into the ambient extension. -/
def finiteSubextensionCocone : Cocone (finiteSubextensionDiagram K L) where
  pt := .of L
  ι := { app E := CommRingCat.ofHom (algebraMap E.1 L) }

/-- A stage of the finite-subextension diagram is its underlying commutative ring. -/
@[simp] theorem finiteSubextensionDiagram_obj (E : FiniteSubextension K L) :
    (finiteSubextensionDiagram K L).obj E = CommRingCat.of E.1 := (rfl)

/-- Transition maps are inclusions of intermediate fields. -/
@[simp] theorem finiteSubextensionDiagram_map {E F : FiniteSubextension K L} (f : E ⟶ F) :
    eqToHom (finiteSubextensionDiagram_obj K L E).symm ≫
        (finiteSubextensionDiagram K L).map f ≫
          eqToHom (finiteSubextensionDiagram_obj K L F) =
      CommRingCat.ofHom (_root_.IntermediateField.inclusion (leOfHom f)).toRingHom := by
  rfl

/-- The cocone point is the ambient extension. -/
@[simp] theorem finiteSubextensionCocone_pt :
    (finiteSubextensionCocone K L).pt = CommRingCat.of L := (rfl)

/-- Cocone legs are the inclusions into the ambient extension. -/
@[simp] theorem finiteSubextensionCocone_ι_app (E : FiniteSubextension K L) :
    eqToHom (finiteSubextensionDiagram_obj K L E).symm ≫
        (finiteSubextensionCocone K L).ι.app E ≫
          eqToHom (finiteSubextensionCocone_pt K L) =
      CommRingCat.ofHom (algebraMap E.1 L) := by
  rfl

/-- An algebraic extension is the filtered colimit of its finite intermediate fields. -/
noncomputable def isColimitFiniteSubextensionCocone [Algebra.IsAlgebraic K L] :
    IsColimit (finiteSubextensionCocone K L) := by
  -- The forgetful functor reflects filtered colimits. Each element belongs to a simple
  -- finite subextension, and each intermediate-field inclusion is injective.
  apply isColimitOfReflects (forget CommRingCat)
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    -- The forgetful functor and the cocone point law identify the ambient element with L.
    change L at x
    let E : FiniteSubextension K L :=
      ⟨_root_.IntermediateField.adjoin K {x},
        _root_.IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩
    exact ⟨E, ⟨x, _root_.IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro E x y hxy
    have h : x = y := Subtype.ext hxy
    exact ⟨E, 𝟙 E, by rw [h]⟩

end TauCeti.IntermediateField
