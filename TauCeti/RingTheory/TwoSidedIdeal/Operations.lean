/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Pushforwards of two-sided ideals under surjective homomorphisms

For a surjective nonunital ring homomorphism `f : F` (`R →ₙ+* S`), the set-theoretic image
`f '' (I : Set R)` of a two-sided ideal `I : TwoSidedIdeal R` is already closed under addition,
negation, and left and right multiplication by `S`. Hence `I.map f` (defined in Mathlib as
`TwoSidedIdeal.span (f '' I)`) has underlying set `f '' I`
(`TwoSidedIdeal.coe_map_of_surjective`), giving the elementwise membership characterization
`TwoSidedIdeal.mem_map_iff_of_surjective` analogous to `Ideal.mem_map_iff_of_surjective`.
-/

public section

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R S F : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  [FunLike F R S] [NonUnitalRingHomClass F R S]

/-- The underlying set of the pushforward `I.map f` of a two-sided ideal along a surjective
nonunital ring homomorphism `f` is the set-theoretic image `f '' I`. -/
theorem coe_map_of_surjective (I : TwoSidedIdeal R) (f : F) (hf : Function.Surjective f) :
    (I.map f : Set S) = f '' (I : Set R) := by
  let J : TwoSidedIdeal S := TwoSidedIdeal.mk' (f '' (I : Set R))
    ⟨0, I.zero_mem, map_zero f⟩
    (by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, I.add_mem hx hy, map_add f x y⟩)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨-x, I.neg_mem hx, map_neg f x⟩)
    (by
      rintro b _ ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨a * x, I.mul_mem_left a x hx, map_mul f a x⟩)
    (by
      rintro _ b ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨x * a, I.mul_mem_right x a hx, map_mul f x a⟩)
  have hIJ : I.map f = J :=
    le_antisymm
      (TwoSidedIdeal.span_le.mpr fun _ hx => (TwoSidedIdeal.mem_mk' ..).mpr hx)
      fun _ hx => TwoSidedIdeal.subset_span ((TwoSidedIdeal.mem_mk' ..).mp hx)
  rw [hIJ]
  exact TwoSidedIdeal.coe_mk' ..

/-- An element `y` belongs to the pushforward `I.map f` along a surjective nonunital ring
homomorphism `f` if and only if `y = f x` for some `x ∈ I`. -/
theorem mem_map_iff_of_surjective {I : TwoSidedIdeal R} (f : F) (hf : Function.Surjective f)
    {y : S} : y ∈ I.map f ↔ ∃ x ∈ I, f x = y := by
  rw [← SetLike.mem_coe, coe_map_of_surjective I f hf]
  rfl

end NonUnitalNonAssocRing

end TwoSidedIdeal
