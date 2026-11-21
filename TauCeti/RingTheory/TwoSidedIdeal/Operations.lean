/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Pushforward and pullback operations on two-sided ideals

This file supplements `Mathlib.RingTheory.TwoSidedIdeal.Operations` with basic lemmas on
`TwoSidedIdeal.map` and `TwoSidedIdeal.comap` along nonunital ring homomorphisms.

## Main results

* `TwoSidedIdeal.map_le_iff_le_comap`: Galois connection between `TwoSidedIdeal.map` and
  `TwoSidedIdeal.comap`.
* `TwoSidedIdeal.coe_map_of_surjective` and `TwoSidedIdeal.mem_map_of_surjective`: under a
  surjective nonunital ring homomorphism `f`, the pushforward ideal `TwoSidedIdeal.map f I` has
  underlying set `f '' I`.
-/

public section

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {A B F : Type*} [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B]
  [FunLike F A B] [NonUnitalRingHomClass F A B]

/-- Galois connection between `TwoSidedIdeal.map` and `TwoSidedIdeal.comap`. -/
theorem map_le_iff_le_comap {f : F} {I : TwoSidedIdeal A} {J : TwoSidedIdeal B} :
    TwoSidedIdeal.map f I ≤ J ↔ I ≤ TwoSidedIdeal.comap f J := by
  rw [TwoSidedIdeal.map, TwoSidedIdeal.span_le]
  refine ⟨fun h a ha => (TwoSidedIdeal.mem_comap f).mpr (h (Set.mem_image_of_mem f ha)), ?_⟩
  rintro h _ ⟨a, ha, rfl⟩
  exact (TwoSidedIdeal.mem_comap f).mp (h ha)

/-- Under a surjective nonunital ring homomorphism, the pushforward ideal `TwoSidedIdeal.map f I`
has underlying set `f '' I` without needing further ideal generation. -/
theorem coe_map_of_surjective {f : F} (hf : Function.Surjective f) (I : TwoSidedIdeal A) :
    (TwoSidedIdeal.map f I : Set B) = f '' (I : Set A) := by
  let K : TwoSidedIdeal B := TwoSidedIdeal.mk' (f '' (I : Set A))
    ⟨0, I.zero_mem, map_zero f⟩
    (by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, I.add_mem hx hy, map_add f x y⟩)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨-x, I.neg_mem hx, map_neg f x⟩)
    (by rintro b _ ⟨y, hy, rfl⟩; obtain ⟨a, rfl⟩ := hf b
        exact ⟨a * y, I.mul_mem_left a y hy, map_mul f a y⟩)
    (by rintro _ b ⟨x, hx, rfl⟩; obtain ⟨a, rfl⟩ := hf b
        exact ⟨x * a, I.mul_mem_right x a hx, map_mul f x a⟩)
  refine Set.Subset.antisymm ?_ TwoSidedIdeal.subset_span
  have hle : TwoSidedIdeal.map f I ≤ K :=
    TwoSidedIdeal.span_le.mpr fun b hb => (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ b).mpr hb
  exact fun b hb => (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ b).mp (hle hb)

/-- Membership in `TwoSidedIdeal.map f I` for a surjective nonunital ring homomorphism `f`. -/
theorem mem_map_of_surjective {f : F} (hf : Function.Surjective f) {I : TwoSidedIdeal A}
    {b : B} : b ∈ TwoSidedIdeal.map f I ↔ ∃ a ∈ I, f a = b := by
  rw [← SetLike.mem_coe, coe_map_of_surjective hf, Set.mem_image]
  simp

end NonUnitalNonAssocRing

end TwoSidedIdeal
