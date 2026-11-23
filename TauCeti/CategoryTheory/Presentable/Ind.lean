/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Representable ind-objects are finitely presentable

For a category `C` with morphisms in `Type v`, the ind-object `Ind.yoneda.obj X` represented by
an object `X : C` is finitely presentable: maps out of it commute with filtered colimits indexed
by categories in `Type v`. Indeed, by the Yoneda lemma such maps are the elements at `X` of the
underlying presheaf, and both the inclusion of ind-objects into presheaves and evaluation at `X`
preserve these colimits.

Concretely (`IsFinitelyPresentable.exists_hom_of_isColimit` and
`IsFinitelyPresentable.exists_eq_of_isColimit`), every map from `Ind.yoneda.obj X` to a filtered
colimit of ind-objects factors through a stage, and two such factorizations agree at a later
stage. Dually, maps from a cofiltered limit of pro-objects to a constant pro-object factor
through a stage; this is the basis of the double-limit formula for morphisms of pro-objects.

## References

* M. Kashiwara and P. Schapira, *Categories and Sheaves*, §6.1.
-/

public section

universe v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace Ind

/-- The inclusion of ind-objects into presheaves preserves filtered colimits indexed by small
categories. -/
instance : PreservesFilteredColimitsOfSize.{v, v} (Ind.inclusion C) where
  preserves_filtered_colimits _ _ _ := inferInstance

/-- A representable ind-object is finitely presentable. -/
instance (X : C) : IsFinitelyPresentable.{v} (Ind.yoneda.obj X) := by
  -- Maps out of `Ind.yoneda.obj X` are the elements at `X` of the underlying presheaf.
  let e : coyoneda.obj (op (Ind.yoneda.obj X)) ≅
      Ind.inclusion C ⋙ (evaluation Cᵒᵖ (Type v)).obj (op X) :=
    NatIso.ofComponents (fun Z ↦ Equiv.toIso
      ((Ind.inclusion.fullyFaithful.homEquiv.trans
        ((Ind.yonedaCompInclusion.app X).homCongr (Iso.refl _))).trans yonedaEquiv))
      (fun f ↦ by
        ext g
        simp [yonedaEquiv_comp])
  rw [isFinitelyPresentable_iff_preservesFilteredColimits]
  exact ⟨fun J _ _ ↦ preservesColimitsOfShape_of_natIso e.symm⟩

end Ind

end CategoryTheory
