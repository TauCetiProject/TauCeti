/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# The zero section of a bundle and the graphs of sections

The zero section `Bundle.zeroSection F E : B → TotalSpace F E` of a bundle whose fibres have a
zero sends `x` to the zero of the fibre over `x`. It is injective
(`Bundle.zeroSection_injective`), a point `(x, v)` of the total space lies on it exactly when
`v = 0` (`Bundle.mk_mem_range_zeroSection_iff`), and so the graph of a section `s` meets the zero
section exactly over the zeros of `s` (`Bundle.range_section_inter_range_zeroSection`). These
are the set-theoretic facts used to count the intersection points of the graph of a section with
the zero section, for instance the intersections of the graph of a one-form with the zero section
of a cotangent bundle. No topology or linear structure is involved.
-/

public section

open Set

namespace Bundle

variable {B F : Type*} {E : B → Type*} [∀ x, Zero (E x)]

variable (F E) in
/-- The zero section of a bundle is injective. -/
theorem zeroSection_injective : Function.Injective (zeroSection F E) :=
  Function.LeftInverse.injective (g := TotalSpace.proj) (zeroSection_proj F E)

/-- A point `(x, v)` of the total space lies on the zero section exactly when `v = 0`. -/
-- The priority lets this fire before `Set.mem_range` unfolds the membership.
@[simp 1001]
theorem mk_mem_range_zeroSection_iff {x : B} {v : E x} :
    TotalSpace.mk' F x v ∈ range (zeroSection F E) ↔ v = 0 := by
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun h ↦ ⟨x, by simp [zeroSection, h]⟩⟩
  -- The point lies over `x`, so the zero it equals is the zero of the fibre over `x`.
  obtain rfl : y = x := congrArg TotalSpace.proj hy
  exact (TotalSpace.mk_inj.mp hy).symm

/-- **The graph of a section meets the zero section over its zeros.** The graph of a section `s`
of a bundle meets the zero section in the zeros of the fibres over the zeros of `s`. -/
theorem range_section_inter_range_zeroSection (s : ∀ x, E x) :
    range (fun x ↦ TotalSpace.mk' F x (s x)) ∩ range (zeroSection F E) =
      zeroSection F E '' {x | s x = 0} := by
  ext z
  constructor
  · rintro ⟨⟨x, rfl⟩, hz⟩
    have hx : s x = 0 := mk_mem_range_zeroSection_iff.mp hz
    exact ⟨x, hx, by simp [zeroSection, hx]⟩
  · rintro ⟨x, hx : s x = 0, rfl⟩
    exact ⟨⟨x, by simp [zeroSection, hx]⟩, mem_range_self x⟩

end Bundle
