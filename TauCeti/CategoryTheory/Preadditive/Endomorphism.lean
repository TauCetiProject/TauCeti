/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.RingTheory.Idempotents

/-!
# Endomorphism rings under isomorphisms and additive functors

In a preadditive category, isomorphic objects have isomorphic endomorphism rings: conjugation
`Iso.conj` is additive. The corner of `End X` at a split idempotent is the endomorphism ring of its
image. An additive functor `F` induces a ring homomorphism
`End X →+* End (F.obj X)`, refining the monoid homomorphism `Functor.mapEnd`, and it is surjective
when `F` is full.

## Main definitions

* `CategoryTheory.Iso.endRingEquiv`: the ring isomorphism `End X ≃+* End Y` induced by `X ≅ Y`.
* `CategoryTheory.Functor.mapEndRingHom`: the ring homomorphism `End X →+* End (F.obj X)` of an
  additive functor.
* `IsIdempotentElem.cornerRingEquivEnd`: for an idempotent `e = p ≫ i` of `X` split through `Y`
  (`i ≫ p = 𝟙 Y`), the corner `e (End X) e` is the endomorphism ring of `Y`.

## Main results

* `CategoryTheory.Iso.endRingEquiv_apply_asHom` and
  `CategoryTheory.Functor.mapEndRingHom_apply_asHom`: the underlying morphisms.
* `CategoryTheory.Functor.mapEndRingHom_surjective`: a full additive functor is surjective on
  endomorphism rings.
-/

public section

namespace CategoryTheory.Iso

variable {C : Type*} [Category* C] [Preadditive C]

/-- Isomorphic objects have isomorphic endomorphism rings: `Iso.conj` is additive. -/
def endRingEquiv {X Y : C} (φ : X ≅ Y) : End X ≃+* End Y where
  __ := φ.conj
  map_add' f g := by ext; simp

/-- The ring isomorphism of `φ : X ≅ Y` conjugates an endomorphism by `φ`. -/
@[simp]
theorem endRingEquiv_apply_asHom {X Y : C} (φ : X ≅ Y) (f : End X) :
    (φ.endRingEquiv f).asHom = φ.inv ≫ f.asHom ≫ φ.hom := by
  simp [endRingEquiv]

end CategoryTheory.Iso

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- An additive functor induces a ring homomorphism on endomorphism rings, refining
`CategoryTheory.Functor.mapEnd`. -/
def mapEndRingHom (F : C ⥤ D) [F.Additive] (X : C) : End X →+* End (F.obj X) where
  __ := F.mapEnd X
  map_zero' := by ext; simp [mapEnd]
  map_add' f g := by ext; simp [mapEnd]

/-- The ring homomorphism of an additive functor applies the functor to an endomorphism. -/
@[simp]
theorem mapEndRingHom_apply_asHom (F : C ⥤ D) [F.Additive] (X : C) (f : End X) :
    (F.mapEndRingHom X f).asHom = F.map f.asHom := by
  simp [mapEndRingHom, mapEnd]

/-- A full additive functor induces a surjection on endomorphism rings. -/
theorem mapEndRingHom_surjective (F : C ⥤ D) [F.Additive] [F.Full] (X : C) :
    Function.Surjective (F.mapEndRingHom X) := fun f ↦
  ⟨End.of (F.preimage f.asHom), by ext; simp⟩

end CategoryTheory.Functor

namespace IsIdempotentElem

open CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C]

/-- **The corner of `End X` at a split idempotent is the endomorphism ring of its image**: if
`e = p ≫ i` with `i ≫ p = 𝟙 Y`, then `g ↦ p ≫ g ≫ i` identifies `End Y` with `e (End X) e`. -/
noncomputable def cornerRingEquivEnd {X Y : C} {e : End X} (he : IsIdempotentElem e)
    (i : Y ⟶ X) (p : X ⟶ Y) (hip : i ≫ p = 𝟙 Y) (hpi : p ≫ i = e.asHom) :
    End Y ≃+* he.Corner where
  toFun g := ⟨End.of (p ≫ g.asHom ≫ i), by
    refine (Subsemigroup.mem_corner_iff he).2 ⟨End.ext ?_, End.ext ?_⟩ <;>
      simp [← hpi, reassoc_of% hip]⟩
  invFun c := End.of (i ≫ c.1.asHom ≫ p)
  left_inv g := End.ext (by simp [reassoc_of% hip, hip])
  right_inv c := by
    obtain ⟨c, hc⟩ := c
    obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff he).1 hc
    have hl' : c.asHom ≫ e.asHom = c.asHom := by simpa using congrArg End.asHom hl
    have hr' : e.asHom ≫ c.asHom = c.asHom := by simpa using congrArg End.asHom hr
    refine Subtype.ext (End.ext ?_)
    -- Unfold the two `End.of` wrappers to compare the underlying morphisms.
    change p ≫ (i ≫ c.asHom ≫ p) ≫ i = c.asHom
    calc p ≫ (i ≫ c.asHom ≫ p) ≫ i = (p ≫ i) ≫ c.asHom ≫ (p ≫ i) := by simp only [Category.assoc]
      _ = c.asHom := by rw [hpi, hl', hr']
  map_mul' g h := by
    apply Subtype.ext
    -- The corner is a subtype of `End X` whose product is the product of `End X`.
    change End.of (p ≫ (g * h).asHom ≫ i) = End.of (p ≫ g.asHom ≫ i) * End.of (p ≫ h.asHom ≫ i)
    ext
    simp [reassoc_of% hip]
  map_add' g h := by
    apply Subtype.ext
    -- The corner is a subtype of `End X` whose sum is the sum of `End X`.
    change End.of (p ≫ (g + h).asHom ≫ i) = End.of (p ≫ g.asHom ≫ i) + End.of (p ≫ h.asHom ≫ i)
    ext
    simp

@[simp]
theorem cornerRingEquivEnd_apply_val_asHom {X Y : C} {e : End X} (he : IsIdempotentElem e)
    (i : Y ⟶ X) (p : X ⟶ Y) (hip : i ≫ p = 𝟙 Y) (hpi : p ≫ i = e.asHom) (g : End Y) :
    (he.cornerRingEquivEnd i p hip hpi g).1.asHom = p ≫ g.asHom ≫ i :=
  (rfl)

@[simp]
theorem cornerRingEquivEnd_symm_apply_asHom {X Y : C} {e : End X} (he : IsIdempotentElem e)
    (i : Y ⟶ X) (p : X ⟶ Y) (hip : i ≫ p = 𝟙 Y) (hpi : p ≫ i = e.asHom) (c : he.Corner) :
    ((he.cornerRingEquivEnd i p hip hpi).symm c).asHom = i ≫ c.1.asHom ≫ p :=
  (rfl)

end IsIdempotentElem
