/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Extreme

/-!
# Extreme subsets and convex combinations

An injective linear map preserves and reflects extreme points when it identifies the source set
with a face of the target set. The scalar assumptions allow semirings and additive monoids, so
the result applies to measures with scalars in `ℝ≥0∞`.

Over a linearly ordered field, an extreme subset `B` of `A` absorbs every convex combination with
strictly positive weights that it meets, as long as the convex hull of the points combined lies in
`A`: all those points then lie in `B` (`IsExtreme.mem_of_centerMass_mem`). Consequently a point of
`B` in the convex hull of `s` is already in the convex hull of `s ∩ B`
(`IsExtreme.convexHull_inter_subset`). This is how a triangulation of a convex set restricts to
each of its faces.
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

section LinearOrderedField

open Finset

variable {𝕜 E ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] {A B : Set E}

/-- If a convex combination with strictly positive weights lies in an extreme subset `B` of a set
`A` which contains the convex hull of the points combined, then each of these points lies in
`B`. -/
theorem IsExtreme.mem_of_centerMass_mem (hAB : IsExtreme 𝕜 A B) {t : Finset ι} {w : ι → 𝕜}
    {z : ι → E} (hw : ∀ i ∈ t, 0 < w i) (hzA : convexHull 𝕜 (z '' t) ⊆ A)
    (hB : t.centerMass w z ∈ B) {i : ι} (hi : i ∈ t) : z i ∈ B := by
  classical
  have hwi := hw i hi
  rcases (t.erase i).eq_empty_or_nonempty with he | he
  · rwa [← insert_erase hi, he, insert_empty, centerMass_singleton _ _ hwi.ne'] at hB
  have hw' : ∀ j ∈ t.erase i, 0 < w j := fun j hj => hw j (mem_of_mem_erase hj)
  have hpos : 0 < ∑ j ∈ t.erase i, w j := sum_pos hw' he
  have hz : ∀ j ∈ t, z j ∈ convexHull 𝕜 (z '' t) := fun j hj =>
    subset_convexHull 𝕜 _ (Set.mem_image_of_mem z (mem_coe.2 hj))
  rw [← insert_erase hi, centerMass_insert i (t.erase i) z (notMem_erase i t) hpos.ne'] at hB
  refine hAB.left_mem_of_mem_openSegment (hzA (hz i hi)) (hzA ?_) hB
    ⟨_, _, div_pos hwi (add_pos hwi hpos), div_pos hpos (add_pos hwi hpos), ?_, rfl⟩
  · exact (convex_convexHull 𝕜 _).centerMass_mem (fun j hj => (hw' j hj).le) hpos
      fun j hj => hz j (mem_of_mem_erase hj)
  · rw [← add_div, div_self (add_pos hwi hpos).ne']

/-- A point of an extreme subset `B` of `A` which is a convex combination of points of `s` is a
convex combination of the points of `s` lying in `B`, provided the convex hull of `s` lies in
`A`. -/
theorem IsExtreme.convexHull_inter_subset (hAB : IsExtreme 𝕜 A B) {s : Set E}
    (hsA : convexHull 𝕜 s ⊆ A) : convexHull 𝕜 s ∩ B ⊆ convexHull 𝕜 (s ∩ B) := by
  classical
  rintro x ⟨hx, hxB⟩
  rw [_root_.convexHull_eq] at hx
  obtain ⟨ι, t, w, z, hw₀, hw₁, hzs, rfl⟩ := hx
  rw [← centerMass_filter_ne_zero] at hxB ⊢
  have hpos : ∀ i ∈ {i ∈ t | w i ≠ 0}, 0 < w i := fun i hi =>
    (hw₀ i (mem_filter.1 hi).1).lt_of_ne' (mem_filter.1 hi).2
  have hzs' : ∀ i ∈ {i ∈ t | w i ≠ 0}, z i ∈ s := fun i hi => hzs i (mem_filter.1 hi).1
  refine centerMass_mem_convexHull _ (fun i hi => (hpos i hi).le) ?_
    fun i hi => ⟨hzs' i hi, hAB.mem_of_centerMass_mem hpos ?_ hxB hi⟩
  · rw [sum_filter_ne_zero, hw₁]
    exact one_pos
  · exact (convexHull_mono (Set.image_subset_iff.2 hzs')).trans hsA

end LinearOrderedField
