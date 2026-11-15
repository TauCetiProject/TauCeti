/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Functor
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Morphism ideals in the idempotent completion

An ideal extends to the Karoubi envelope by testing the underlying morphism in the original
category. Extension and restriction along `toKaroubi` are mutually inverse: every formal summand
is a retract of its ambient object, and ideal membership is preserved by composition with the
retraction maps. In particular, idempotent completion introduces no new morphism ideals.

The construction uses Mathlib's `Karoubi.inclusionHom` and its canonical retractions
`Karoubi.decompId_i` and `Karoubi.decompId_p`.
-/

public section

open CategoryTheory CategoryTheory.Idempotents

namespace TauCeti.MorphismIdeal

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Extend an ideal to formal summands by testing the underlying morphism. -/
def karoubi (I : MorphismIdeal C) : MorphismIdeal (Karoubi C) where
  hom P Q := (I.hom P.X Q.X).comap (Karoubi.inclusionHom P Q)
  comp_mem_left f _ hg := I.comp_mem_left f.f hg
  comp_mem_right g hf := I.comp_mem_right g.f hf

/-- Membership in the extended ideal is membership of the underlying morphism. -/
@[simp]
theorem mem_karoubi_hom (I : MorphismIdeal C) {P Q : Karoubi C} {f : P ⟶ Q} :
    f ∈ I.karoubi.hom P Q ↔ f.f ∈ I.hom P.X Q.X := Iff.rfl

/-- Restriction of the extension along the idempotent-completion embedding recovers the ideal. -/
@[simp]
theorem karoubi_comap_toKaroubi (I : MorphismIdeal C) :
    I.karoubi.comap (toKaroubi C) = I := by
  ext X Y f
  simp

/-- An ideal of the idempotent completion contains a morphism exactly when it contains its
underlying morphism between the ambient objects, embedded with identity idempotents. -/
theorem mem_hom_iff_toKaroubi_map (J : MorphismIdeal (Karoubi C)) {P Q : Karoubi C}
    (f : P ⟶ Q) : f ∈ J.hom P Q ↔ (toKaroubi C).map f.f ∈
      J.hom ((toKaroubi C).obj P.X) ((toKaroubi C).obj Q.X) := by
  constructor
  · intro hf
    have h := J.comp_mem_right (Karoubi.decompId_i Q)
      (J.comp_mem_left (Karoubi.decompId_p P) hf)
    have he : (Karoubi.decompId_p P ≫ f) ≫ Karoubi.decompId_i Q =
        (toKaroubi C).map f.f := by ext; simp
    rwa [he] at h
  · intro hf
    have h := J.comp_mem_right (Karoubi.decompId_p Q)
      (J.comp_mem_left (Karoubi.decompId_i P) hf)
    have he : (Karoubi.decompId_i P ≫ (toKaroubi C).map f.f) ≫ Karoubi.decompId_p Q = f := by
      ext
      simp
    rwa [he] at h

/-- Every ideal of the idempotent completion is the extension of its restriction. -/
@[simp]
theorem comap_toKaroubi_karoubi (J : MorphismIdeal (Karoubi C)) :
    (J.comap (toKaroubi C)).karoubi = J := by
  ext P Q f
  simp only [mem_karoubi_hom, mem_comap_hom]
  exact (J.mem_hom_iff_toKaroubi_map f).symm

/-- Extension to formal summands preserves and reflects inclusion of ideals. -/
@[simp]
theorem karoubi_le_karoubi_iff {I J : MorphismIdeal C} : I.karoubi ≤ J.karoubi ↔ I ≤ J := by
  constructor
  · intro h
    simpa using comap_mono (toKaroubi C) h
  · intro h
    exact le_def.mpr fun _ _ _ hf => (le_def.mp h) _ hf

end TauCeti.MorphismIdeal
