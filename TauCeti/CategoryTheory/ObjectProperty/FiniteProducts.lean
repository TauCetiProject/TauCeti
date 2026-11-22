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
isomorphisms (`CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_isTerminal`).
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

end CategoryTheory.ObjectProperty
