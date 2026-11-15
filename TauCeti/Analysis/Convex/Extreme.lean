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

Every subfamily of an affinely independent family spans an extreme subset of its convex hull
(`AffineIndependent.isExtreme_convexHull`). Thus the faces of a simplex are extreme, without
any topological or finite-dimensional assumption.
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

section Simplex

variable {𝕜 E ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {p : ι → E}

/-- The convex hull of any subfamily of an affinely independent family is an extreme subset
of the convex hull of the whole family. In particular, every face of a simplex is extreme. -/
theorem AffineIndependent.isExtreme_convexHull (hp : AffineIndependent 𝕜 p) (s : Set ι) :
    IsExtreme 𝕜 (convexHull 𝕜 (Set.range p)) (convexHull 𝕜 (p '' s)) := by
  classical
  obtain ⟨t, hpt, ht, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hp.range
  let b : AffineBasis t 𝕜 E := ⟨Subtype.val, ht, by simpa using hspan⟩
  let c (i : ι) := b.coord ⟨p i, hpt (Set.mem_range_self i)⟩
  have hcp (i j : ι) : c i (p j) = if i = j then 1 else 0 := by
    -- The chosen basis is the inclusion of `t`; expose its value to apply `coord_apply`.
    rw [show p j = b ⟨p j, hpt (Set.mem_range_self j)⟩ from rfl, b.coord_apply]
    simp [hp.injective.eq_iff]
  have hnn (i : ι) : convexHull 𝕜 (Set.range p) ⊆ {x | 0 ≤ c i x} :=
    convexHull_min (by rintro _ ⟨j, rfl⟩; rw [Set.mem_ofPred_eq, hcp]; split_ifs <;> simp)
      ((convex_Ici 0).affine_preimage (c i))
  have hzero (i : ι) (hi : i ∉ s) : convexHull 𝕜 (p '' s) ⊆ {x | c i x = 0} :=
    convexHull_min (by rintro _ ⟨j, hj, rfl⟩; simp [hcp, ne_of_mem_of_not_mem hj hi |>.symm])
      ((convex_singleton 0).affine_preimage (c i))
  refine ⟨convexHull_mono (Set.image_subset_range _ _), ?_⟩
  rintro x hx y hy z hz ⟨a, d, ha, hd, had, hmix⟩
  have hcx (i : ι) (hi : i ∉ s) : c i x = 0 := by
    have heq : a * c i x + d * c i y = 0 := by
      simpa only [Convex.combo_affine_apply had, smul_eq_mul] using
        (congrArg (c i) hmix).trans (hzero i hi hz)
    exact (mul_eq_zero.mp ((add_eq_zero_iff_of_nonneg
      (mul_nonneg ha.le (hnn i hx)) (mul_nonneg hd.le (hnn i hy))).mp heq).1).resolve_left
        ha.ne'
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨u, w, hw, hw₁, rfl⟩ := hx
  have hws : ∀ i ∈ u, w i ≠ 0 → i ∈ s := by
    intro i hi hwi
    by_contra his
    have := hcx i his
    rw [Finset.map_affineCombination _ _ _ hw₁,
      Finset.affineCombination_eq_linear_combination _ _ _ hw₁] at this
    exact hwi (by simpa [hcp, hi] using this)
  have hsum : ∑ i ∈ u.filter (· ∈ s), w i = 1 := by
    rwa [Finset.sum_filter_of_ne hws]
  rw [← u.affineCombination_filter_of_ne w p hws,
    affineCombination_eq_centerMass hsum]
  exact Finset.centerMass_mem_convexHull _ (fun i hi => hw i (Finset.mem_filter.mp hi).1)
    (by rw [hsum]; exact zero_lt_one)
    (fun i hi => Set.mem_image_of_mem p (Finset.mem_filter.mp hi).2)

end Simplex
