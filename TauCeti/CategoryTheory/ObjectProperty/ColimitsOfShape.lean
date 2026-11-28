/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Colimit closure of object properties

In a category with zero morphisms, a colimit of zero objects is a zero object: the zero objects
are closed under colimits of every shape. Combined with the closure of kernels and cokernels under
colimits of morphisms (`CategoryTheory.ObjectProperty.prop_kernel_colimMap`), this says that a
colimit of isomorphisms is an isomorphism when colimits are exact.

Closure under finite and filtered colimits suffices for closure under all colimits
of the given size, by expressing coproducts as filtered colimits of finite sums.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

/-- A colimit of zero objects is a zero object. -/
instance {C : Type*} [Category* C] [HasZeroMorphisms C] {J : Type*} [Category* J] :
    IsClosedUnderColimitsOfShape (IsZero (C := C)) J where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    rw [IsZero.iff_id_eq_zero]
    exact h.isColimit.hom_ext fun j ↦ (h.prop_diag_obj j).eq_of_src _ _

universe w

variable {C : Type*} [Category* C]

/-- A full subcategory whose inclusion preserves finite colimits and whose objects are closed
under filtered colimits is closed under all small colimits, provided these exist in the ambient
category. -/
lemma isClosedUnderColimitsOfShape_of_finite_and_filtered (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] [HasColimitsOfSize.{w, w} C]
    [HasFiniteColimits P.FullSubcategory] [PreservesFiniteColimits P.ι]
    (hFiltered : ∀ (K : Type w) [SmallCategory K] [IsFiltered K],
      P.IsClosedUnderColimitsOfShape K)
    (J : Type w) [SmallCategory J] : P.IsClosedUnderColimitsOfShape J := by
  have : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts.{w} C
  have : HasFilteredColimitsOfSize.{w, w} P.FullSubcategory :=
    ⟨fun K _ _ ↦
      have := hFiltered K
      inferInstance⟩
  have : HasColimitsOfSize.{w, w} P.FullSubcategory := has_colimits_of_finite_and_filtered
  have (α : Type w) : PreservesColimitsOfShape (Discrete α) P.ι := by
    have : P.IsClosedUnderColimitsOfShape (Discrete α) := by
      refine ⟨fun X ⟨p⟩ ↦ ?_⟩
      -- The coproduct is the filtered colimit of its finite partial coproducts.
      let c := CoproductsFromFiniteFiltered.liftToFinsetColimitCocone p.diag
      refine P.prop_of_iso (c.isColimit.coconePointUniqueUpToIso p.isColimit) ?_
      have := hFiltered (Finset (Discrete α))
      refine P.prop_colimit (CoproductsFromFiniteFiltered.liftToFinsetObj p.diag) ?_
      intro S
      rw [CoproductsFromFiniteFiltered.liftToFinsetObj_obj]
      have : P.IsClosedUnderColimitsOfShape (Discrete S) :=
        P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _
      exact P.prop_colimit _ (fun s ↦ p.prop_diag_obj s.as.val)
    infer_instance
  have := preservesColimits_of_preservesCoequalizers_and_coproducts.{w} P.ι
  exact P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι J

end CategoryTheory.ObjectProperty
