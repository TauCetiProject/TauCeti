/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Eventually orthogonal objects

Let `C` be a pretriangulated category and `S : ℤ → ObjectProperty C` a family of classes of
objects. An object `Y` is *eventually right orthogonal* to `S` if it lies in the right orthogonal
of `S n` for all `n` large enough, and *eventually left orthogonal* if it lies in the left
orthogonal of `S n` for all `n` large enough.

Both classes are closed under isomorphisms and retracts, contain the zero objects, and are closed
under extensions in distinguished triangles (`IsTriangulatedClosed₂`), since each right or left
orthogonal is and finitely many bounds have a maximum. If shifting moves `S n` into `S (n + c)`
for some `c` depending on the shift, they are also stable under shifts, hence triangulated
subcategories.

A typical family is given by the objects of an abelian category placed in degree `n` (or `-n`)
of its derived category: vanishing statements for morphisms to or from objects in sufficiently
high (or low) degrees then pass from generators to the thick subcategory they generate.

## Main definitions

* `CategoryTheory.ObjectProperty.eventuallyRightOrthogonal`: the objects in the right orthogonal
  of `S n` for all large `n`.
* `CategoryTheory.ObjectProperty.eventuallyLeftOrthogonal`: the objects in the left orthogonal of
  `S n` for all large `n`.

## Main results

* `CategoryTheory.ObjectProperty.isStableUnderShift_eventuallyRightOrthogonal` and
  `CategoryTheory.ObjectProperty.isStableUnderShift_eventuallyLeftOrthogonal`: stability under
  shifts, when shifts move the family along its index.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v u

namespace CategoryTheory.ObjectProperty

section ZeroMorphisms

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ℤ → ObjectProperty C)

/-- The objects in the right orthogonal of `S n` for all `n` large enough. -/
def eventuallyRightOrthogonal : ObjectProperty C :=
  fun Y ↦ ∃ n₀ : ℤ, ∀ n ≥ n₀, (S n).rightOrthogonal Y

/-- The objects in the left orthogonal of `S n` for all `n` large enough. -/
def eventuallyLeftOrthogonal : ObjectProperty C :=
  fun X ↦ ∃ n₀ : ℤ, ∀ n ≥ n₀, (S n).leftOrthogonal X

variable {S}

/-- An object is eventually right orthogonal to `S` if it is right orthogonal to `S n` for all
large `n`. -/
theorem eventuallyRightOrthogonal_iff {Y : C} :
    eventuallyRightOrthogonal S Y ↔ ∃ n₀ : ℤ, ∀ n ≥ n₀, (S n).rightOrthogonal Y :=
  Iff.rfl

/-- An object is eventually left orthogonal to `S` if it is left orthogonal to `S n` for all large
`n`. -/
theorem eventuallyLeftOrthogonal_iff {X : C} :
    eventuallyLeftOrthogonal S X ↔ ∃ n₀ : ℤ, ∀ n ≥ n₀, (S n).leftOrthogonal X :=
  Iff.rfl

instance : (eventuallyRightOrthogonal S).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨n₀, h⟩ ↦ ⟨n₀, fun n hn ↦ (S n).rightOrthogonal.prop_of_iso e (h n hn)⟩

instance : (eventuallyLeftOrthogonal S).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨n₀, h⟩ ↦ ⟨n₀, fun n hn ↦ (S n).leftOrthogonal.prop_of_iso e (h n hn)⟩

instance : (eventuallyRightOrthogonal S).IsStableUnderRetracts where
  of_retract r := fun ⟨n₀, h⟩ ↦ ⟨n₀, fun n hn _ f hX ↦ by
    rw [← Category.comp_id f, ← r.retract, ← Category.assoc, h n hn (f ≫ r.i) hX, zero_comp]⟩

instance : (eventuallyLeftOrthogonal S).IsStableUnderRetracts where
  of_retract r := fun ⟨n₀, h⟩ ↦ ⟨n₀, fun n hn _ f hX ↦ by
    rw [← Category.id_comp f, ← r.retract, Category.assoc, h n hn (r.r ≫ f) hX, comp_zero]⟩

section ZeroObject

variable [HasZeroObject C]

instance : (eventuallyRightOrthogonal S).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, 0, fun n _ ↦ (S n).rightOrthogonal.prop_of_isZero
    (isZero_zero _)⟩

instance : (eventuallyLeftOrthogonal S).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, 0, fun n _ ↦ (S n).leftOrthogonal.prop_of_isZero
    (isZero_zero _)⟩

end ZeroObject

section Shift

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).PreservesZeroMorphisms]

/-- **Shift stability of eventual right orthogonality**: if shifting by `-a` moves `S n` into
`S (n + c)` for some `c`, then the objects eventually right orthogonal to `S` are stable under
shifts. -/
theorem isStableUnderShift_eventuallyRightOrthogonal
    (hS : ∀ a : ℤ, ∃ c : ℤ, ∀ n (X : C), S n X → S (n + c) (X⟦-a⟧)) :
    (eventuallyRightOrthogonal S).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun Y ⟨n₀, h⟩ ↦ by
    obtain ⟨c, hc⟩ := hS a
    -- A morphism `X ⟶ Y⟦a⟧` corresponds to `X⟦-a⟧ ⟶ Y`, and `X⟦-a⟧` lies in `S (n + c)`.
    refine ⟨n₀ - c, fun n hn X f hX ↦ (shiftFunctor C (-a)).map_injective ?_⟩
    rw [Functor.map_zero, ← cancel_mono ((shiftFunctorCompIsoId C a (-a) (by lia)).hom.app Y),
      zero_comp]
    exact h (n + c) (by lia) _ (hc n X hX)⟩

/-- **Shift stability of eventual left orthogonality**: if shifting by `-a` moves `S n` into
`S (n + c)` for some `c`, then the objects eventually left orthogonal to `S` are stable under
shifts. -/
theorem isStableUnderShift_eventuallyLeftOrthogonal
    (hS : ∀ a : ℤ, ∃ c : ℤ, ∀ n (Y : C), S n Y → S (n + c) (Y⟦-a⟧)) :
    (eventuallyLeftOrthogonal S).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun X ⟨n₀, h⟩ ↦ by
    obtain ⟨c, hc⟩ := hS a
    -- A morphism `X⟦a⟧ ⟶ Y` corresponds to `X ⟶ Y⟦-a⟧`, and `Y⟦-a⟧` lies in `S (n + c)`.
    refine ⟨n₀ - c, fun n hn Y f hY ↦ (shiftFunctor C (-a)).map_injective ?_⟩
    rw [Functor.map_zero, ← cancel_epi ((shiftFunctorCompIsoId C a (-a) (by lia)).inv.app X),
      comp_zero]
    exact h (n + c) (by lia) _ (hc n Y hY)⟩

end Shift

end ZeroMorphisms

section Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {S : ℤ → ObjectProperty C}

instance : (eventuallyRightOrthogonal S).IsTriangulatedClosed₂ :=
  .mk' fun T hT ⟨n₁, h₁⟩ ⟨n₃, h₃⟩ ↦ ⟨max n₁ n₃, fun n hn ↦
    (S n).rightOrthogonal.ext_of_isTriangulatedClosed₂ T hT (h₁ n (by lia)) (h₃ n (by lia))⟩

instance : (eventuallyLeftOrthogonal S).IsTriangulatedClosed₂ :=
  .mk' fun T hT ⟨n₁, h₁⟩ ⟨n₃, h₃⟩ ↦ ⟨max n₁ n₃, fun n hn ↦
    (S n).leftOrthogonal.ext_of_isTriangulatedClosed₂ T hT (h₁ n (by lia)) (h₃ n (by lia))⟩

end Pretriangulated

end CategoryTheory.ObjectProperty
