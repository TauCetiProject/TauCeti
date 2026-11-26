/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite products in `Over X` of objects with a property stable under base change

Let `P` be a property of morphisms that is stable under composition and base change, and
contains the identities. The product of two objects `Y` and `Z` of `Over X` is the fibre product
`Y ×_X Z`, whose structure morphism is the base change of `Z ⟶ X` along `Y ⟶ X` followed by
`Y ⟶ X`, so it has `P` when both factors have. The terminal object is `X` itself. Hence the objects
of `Over X` whose structure morphism has `P` are closed under finite products
(`CategoryTheory.Over.isClosedUnderFiniteProducts`). For morphisms of schemes
this says, for instance, that a finite product over `S` of proper `S`-schemes is proper.

Unlike Mathlib's closure under arbitrary pullbacks in `Over X`
(`CategoryTheory.Over.closedUnderLimitsOfShape_pullback`), no cancellation
property of `P` is needed, since products are fibre products over the base itself.
-/

public section

namespace CategoryTheory

open Limits

variable {T : Type*} [Category* T] (P : MorphismProperty T) {X : T}

/-- The cone point of a limit binary fan in `Over X` has its structure morphism in every property,
stable under composition and base change, that both factors have: it is the base change of
`Y ⟶ X` along `Z ⟶ X` followed by `Z ⟶ X`. -/
theorem MorphismProperty.pt_hom_mem_of_isLimit_binaryFan [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] {Y Z : Over X} {c : BinaryFan Y Z} (hc : IsLimit c)
    (hY : P Y.hom) (hZ : P Z.hom) : P c.pt.hom := by
  have h := P.comp_mem _ _ (P.of_isPullback (Over.isPullback_of_binaryFan_isLimit c hc) hY) hZ
  rwa [CategoryTheory.Over.w] at h

/-- The objects of `Over X` whose structure morphism has `P` are closed under binary products. -/
instance Over.closedUnderLimitsOfShape_discrete_walkingPair [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] : (P.overObj (X := X)).IsClosedUnderBinaryProducts := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine .mk' ?_
  rintro _ ⟨F, hF⟩
  have : HasLimit (pair (F.obj ⟨.left⟩) (F.obj ⟨.right⟩)) := hasLimit_of_iso (diagramIsoPair F)
  exact (P.overObj (X := X)).prop_of_iso (HasLimit.isoOfNatIso (diagramIsoPair F)).symm
    (P.pt_hom_mem_of_isLimit_binaryFan (limit.isLimit _) (hF _) (hF _))

/-- The objects of `Over X` whose structure morphism has `P` are closed under finite products. -/
instance Over.isClosedUnderFiniteProducts [HasFiniteWidePullbacks T] [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] : (P.overObj (X := X)).IsClosedUnderFiniteProducts := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact .mk'

end CategoryTheory
