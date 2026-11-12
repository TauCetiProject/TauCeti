/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# The zero section and the zeros of a section

The zero section `Bundle.zeroSection F E : B → TotalSpace F E` of a bundle whose fibres have a
zero is injective (`Bundle.zeroSection_injective`). The image of a section `s` meets the image of
the zero section exactly over the zeros of `s` (`Bundle.range_mk_inter_range_zeroSection`): two
sections of a bundle meet only over the points where they agree. No topology or linear structure
is used. A point of the total space lies on the zero section exactly when its fibre component
is zero (`Bundle.mk_mem_range_zeroSection_iff`).
-/

public section

open Set

namespace Bundle

variable {B F : Type*} {E : B → Type*} [∀ x, Zero (E x)]

variable (F E) in
/-- The zero section of a bundle is injective, since the projection is a left inverse of it. -/
theorem zeroSection_injective : Function.Injective (zeroSection F E) :=
  Function.LeftInverse.injective (g := TotalSpace.proj) fun _ ↦ rfl

/-- A point `(x, v)` of the total space lies on the zero section exactly when `v = 0`. -/
-- The priority lets this fire before `Set.mem_range` unfolds the membership.
@[simp 1001]
theorem mk_mem_range_zeroSection_iff {x : B} {v : E x} :
    TotalSpace.mk' F x v ∈ range (zeroSection F E) ↔ v = 0 := by
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun h ↦ ⟨x, by simp [zeroSection, h]⟩⟩
  -- The point lies over `x`, so the zero it equals is the zero of the fibre over `x`.
  obtain rfl : y = x := congrArg TotalSpace.proj hy
  exact (TotalSpace.mk_inj.mp hy).symm

/-- **A section meets the zero section over its zeros.** The image of a section `s` of a bundle
meets the image of the zero section exactly in the zero vectors over the points where `s`
vanishes. -/
theorem range_mk_inter_range_zeroSection (s : ∀ x, E x) :
    range (fun x ↦ TotalSpace.mk' F x (s x)) ∩ range (zeroSection F E) =
      zeroSection F E '' {x | s x = 0} := by
  ext v
  simp only [mem_inter_iff, mem_range, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, rfl⟩, y, hy⟩
    -- Both sections pass through `v`, so they lie over the same point and agree there.
    obtain rfl : y = x := congrArg TotalSpace.proj hy
    exact ⟨y, (TotalSpace.mk_inj.mp hy).symm, hy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, by rw [zeroSection, hx]⟩, x, rfl⟩

end Bundle
