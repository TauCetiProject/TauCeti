/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Properties closed under finite products

If a property `P` of objects of `D` is closed under finite products and a functor `F : C ⥤ D`
preserves finite products, then the inverse image `P.inverseImage F` is closed under finite
products.

A property closed under binary products that holds for some terminal object is closed under
isomorphisms (`CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_isTerminal`), in
particular one that holds for a zero object
(`CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_containsZero`).

For a property closed under isomorphisms, closure under binary products only has to be checked on
one limit binary fan for each pair of objects satisfying the property
(`CategoryTheory.ObjectProperty.isClosedUnderBinaryProducts_of_exists_isLimit`), and in a category
with binary biproducts on the chosen biproducts `X ⊞ Y`
(`CategoryTheory.ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod`). Conversely, a
property closed under binary products holds on an existing biproduct `X ⊞ Y` whenever it holds on
`X` and on `Y`, with the conclusion in that syntactic form
(`CategoryTheory.ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts`).
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

/-- The inverse image of a property closed under finite products, along a functor preserving
finite products, is closed under finite products. -/
instance isClosedUnderFiniteProducts_inverseImage {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) [P.IsClosedUnderFiniteProducts] (F : C ⥤ D)
    [PreservesFiniteProducts F] : (P.inverseImage F).IsClosedUnderFiniteProducts :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- **A property holding for a terminal object and closed under binary products is closed under
isomorphisms.** An isomorphism `e : X ≅ Y` exhibits `Y` as a product of the terminal object with
`X`, the second projection being `e.inv`.

Here `hT` exhibits one terminal object `T`, and `hTP` asks for the property at that `T` only, not at
every terminal object. Mathlib's
`CategoryTheory.ObjectProperty.IsClosedUnderBinaryProducts.closedUnderIsomorphisms` is the same
argument, but it assumes `HasTerminal C` together with closure under the empty limit, which says
that the property holds at every limit of the empty diagram, that is, at every terminal object.
Before repleteness is known, the property at one terminal object does not give this. -/
theorem isClosedUnderIsomorphisms_of_isTerminal {C : Type*} [Category* C]
    (P : ObjectProperty C) [P.IsClosedUnderBinaryProducts] {T : C} (hT : IsTerminal T)
    (hTP : P T) : P.IsClosedUnderIsomorphisms where
  of_iso {_ Y} e hX := by
    obtain ⟨hB⟩ := (BinaryFan.isLimit_iff_isIso_snd hT (BinaryFan.mk (hT.from Y) e.inv)).2
      (by rw [BinaryFan.mk_snd]; infer_instance)
    exact P.prop_of_isLimit_binaryFan hB hTP hX

/-- **A property holding for a zero object and closed under binary products is closed under
isomorphisms.** This is `CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_isTerminal`
for the zero object supplied by `CategoryTheory.ObjectProperty.ContainsZero`, so that it applies
by type class inference alone. -/
theorem isClosedUnderIsomorphisms_of_containsZero {C : Type*} [Category* C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms := by
  obtain ⟨Z, hZ, hZP⟩ := P.exists_prop_of_containsZero
  exact P.isClosedUnderIsomorphisms_of_isTerminal hZ.isTerminal hZP

/-- **For a replete property, closure under binary products only has to be checked on one limit
binary fan for each pair.** Every binary product of `X` and `Y` is isomorphic to the point of any
limit binary fan over `X` and `Y`. -/
theorem isClosedUnderBinaryProducts_of_exists_isLimit {C : Type*} [Category* C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (h : ∀ X Y : C, P X → P Y → ∃ c : BinaryFan X Y, Nonempty (IsLimit c) ∧ P c.pt) :
    P.IsClosedUnderBinaryProducts := by
  refine IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  obtain ⟨c, ⟨hc⟩, hP⟩ := h _ _ (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)
  exact P.prop_of_iso (hc.conePointsIsoOfNatIso (limit.isLimit F) (diagramIsoPair F).symm) hP

/-- **For a replete property, closure under binary products only has to be checked on
biproducts**, since in a category with binary biproducts every binary product is one. This is
`CategoryTheory.ObjectProperty.isClosedUnderBinaryProducts_of_exists_isLimit` for the biproduct
fans `CategoryTheory.Limits.BinaryBiproduct.isLimit`. -/
theorem isClosedUnderBinaryProducts_of_prop_biprod {C : Type*} [Category* C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (h : ∀ X Y : C, P X → P Y → P (X ⊞ Y)) :
    P.IsClosedUnderBinaryProducts :=
  P.isClosedUnderBinaryProducts_of_exists_isLimit fun X Y hX hY ↦
    ⟨_, ⟨BinaryBiproduct.isLimit X Y⟩, h X Y hX hY⟩

/-- **A property closed under binary products holds on an existing biproduct `X ⊞ Y` whenever it
holds on `X` and on `Y`.** A binary biproduct is a binary product, so this is
`CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan` applied to
`CategoryTheory.Limits.BinaryBiproduct.isLimit`; naming it keeps the index of the conclusion
syntactically `X ⊞ Y`, which matters when the conclusion is the type index of a dependent
family. -/
theorem prop_biprod_of_isClosedUnderBinaryProducts {C : Type*} [Category* C]
    [HasZeroMorphisms C] (P : ObjectProperty C) [P.IsClosedUnderBinaryProducts]
    {X Y : C} [HasBinaryBiproduct X Y] (hX : P X) (hY : P Y) : P (X ⊞ Y) :=
  P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit X Y) hX hY

end CategoryTheory.ObjectProperty
