/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Extreme

/-!
# Transporting extreme points into a face

An injective linear map preserves and reflects extreme points when it identifies the source set
with a face of the target set. The scalar assumptions allow semirings and additive monoids, so
the result applies to measures with scalars in `ℝ≥0∞`.
-/

public section

open Set

namespace TauCeti

/-- A point `x` is extreme if and only if its image under an injective linear map is extreme,
when membership in the target pulls back to the source set, the source maps into a face, and
that face lies in the map's range. -/
theorem mem_extremePoints_iff_linearMap_mem_extremePoints
    {𝕜 E F : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    {C : Set E} {D D' : Set F} (x : E) (hface : _root_.IsExtreme 𝕜 D D')
    (f : E →ₗ[𝕜] F) (hf : Function.Injective f)
    (hmem : ∀ x, f x ∈ D ↔ x ∈ C) (hmaps : MapsTo f C D')
    (hsurj : D' ⊆ range f) :
    x ∈ extremePoints 𝕜 C ↔ f x ∈ extremePoints 𝕜 D := by
  simp only [mem_extremePoints_iff_left]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨(hmem x).2 hx, ?_⟩
    intro y₁ hy₁ y₂ hy₂ hsegment
    obtain ⟨x₁, rfl⟩ := hsurj (hface.left_mem_of_mem_openSegment hy₁ hy₂ (hmaps hx) hsegment)
    obtain ⟨x₂, rfl⟩ := hsurj (hface.right_mem_of_mem_openSegment hy₁ hy₂ (hmaps hx) hsegment)
    apply congrArg f
    apply h x₁ ((hmem x₁).1 hy₁) x₂ ((hmem x₂).1 hy₂)
    obtain ⟨a, b, ha, hb, hab, hmix⟩ := hsegment
    exact ⟨a, b, ha, hb, hab, hf (by simpa only [map_add, map_smul] using hmix)⟩
  · rintro ⟨hx, h⟩
    refine ⟨(hmem x).1 hx, ?_⟩
    rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hmix⟩
    apply hf
    apply h (f x₁) ((hmem x₁).2 hx₁) (f x₂) ((hmem x₂).2 hx₂)
    exact ⟨a, b, ha, hb, hab, by simpa only [map_add, map_smul] using congrArg f hmix⟩

end TauCeti
