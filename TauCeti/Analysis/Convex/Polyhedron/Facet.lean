/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Direction
public import Mathlib.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.Exposed
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.Minimal
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Facet presentations and relative frontiers

A polyhedron admits a half-space presentation within its affine span
in which every row defines a genuine facet. Its relative frontier is therefore
covered by facets. This identifies the geometric boundary used by signed facet
sums, including for unbounded and lower-dimensional polyhedra with lineality.

Adapted from `Mei/Geometry/Convex/Polyhedron/Face/Facet.lean` at
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).

The construction uses `Convex.exists_mem_zero_iff_forall` to obtain simultaneous
strict inequalities and `TauCeti.vectorSpan_active_eq` to identify each facet direction.
Its relative dimension follows from `Module.Dual.finrank_ker_inf_add_one`.
The selected indices belong to the input family, so their original normal and offset data are
preserved. The thinning and active-row witnesses need neither a topology nor finite dimension.
Only the facet dimension formula needs the direction of the polyhedron to be finite-dimensional.
With continuous scalar multiplication the intrinsic frontier is the union of the facets and
also the union of all proper exposed faces.
-/

public section

open Set Module AffineSubspace

namespace TauCeti

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] {P : Set V}

/-- The segment from a strictly feasible point to a point violating just row `j` crosses that
row at zero while all the other rows remain strict. -/
theorem exists_mem_openSegment_single_active (g : ι → (V →ᵃ[ℝ] ℝ)) (j : ι) {q x : V}
    (hq : ∀ l, g l q < 0) (hxj : 0 < g j x) (hx : ∀ l ≠ j, g l x ≤ 0) :
    ∃ p ∈ openSegment ℝ q x, g j p = 0 ∧ ∀ l ≠ j, g l p < 0 := by
  have hzero : 0 ∈ (g j) '' openSegment ℝ q x := by
    rw [image_openSegment, openSegment_eq_Ioo ((hq j).trans hxj)]
    exact ⟨hq j, hxj⟩
  obtain ⟨p, hp, hpj⟩ := hzero
  refine ⟨p, hp, hpj, fun l hl => ?_⟩
  rw [openSegment_eq_image_lineMap] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  rw [(g l).apply_lineMap, AffineMap.lineMap_apply_ring]
  exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (sub_pos.mpr ht.2) (hq l))
    (mul_nonpos_of_nonneg_of_nonpos ht.1.le (hx l hl))

/-- Thin a finite relative half-space presentation to a subfamily of its own rows. Each
retained row has a point where it alone is active; its face direction is the kernel of a
functional that is nonzero on the direction of the polyhedron. -/
theorem exists_irredundant_affine_subfamily [Finite ι] (f : ι → (V →ᵃ[ℝ] ℝ))
    (hf : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0}) :
    ∃ S : Finset ι, P = {x | x ∈ affineSpan ℝ P ∧ ∀ j ∈ S, f j x ≤ 0} ∧
      ∀ j : S, (∃ p ∈ P, f j p = 0 ∧ ∀ l : S, l ≠ j → f l p < 0) ∧
        vectorSpan ℝ {p ∈ P | f j p = 0} = vectorSpan ℝ P ⊓ (f j).linear.ker ∧
        ¬ vectorSpan ℝ P ≤ (f j).linear.ker := by
  classical
  rcases P.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp⟩
  let := Fintype.ofFinite ι
  let A := affineSpan ℝ P
  let presents (S : Finset ι) := P = {x | x ∈ A ∧ ∀ j ∈ S, f j x ≤ 0}
  have hu : presents Finset.univ := by simpa only [presents, Finset.mem_univ, forall_const] using hf
  obtain ⟨S, hS⟩ := exists_minimal_of_wellFoundedLT presents ⟨_, hu⟩
  have hpres : P = {x | x ∈ A ∧ ∀ j ∈ S, f j x ≤ 0} := hS.1
  have hwitness (j : S) : ∃ x ∈ A, (∀ l ∈ S.erase j.val, f l x ≤ 0) ∧ 0 < f j.val x := by
    by_contra! hn
    have herase : presents (S.erase j.val) := by
      apply Set.Subset.antisymm
      · intro x hx
        exact ⟨subset_affineSpan ℝ P hx,
          fun l hl => (hpres ▸ hx).2 l (Finset.mem_of_mem_erase hl)⟩
      · rintro x ⟨hxA, hx⟩
        rw [hpres]
        refine ⟨hxA, fun l hl => ?_⟩
        by_cases he : l = j.val
        · subst l
          exact hn x hxA hx
        · exact hx l (Finset.mem_erase.mpr ⟨he, hl⟩)
    have he := hS.2 herase (Finset.erase_subset _ _)
    exact Finset.notMem_erase j.val S (he j.property)
  have hconv : Convex ℝ P := by
    have hc := A.convex.inter (convex_iInter fun j => (convex_Iic (0 : ℝ)).affine_preimage (f j))
    convert hc using 1
    ext p
    simpa only [A, SetLike.mem_coe, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_Iic] using
      Set.ext_iff.mp hf p
  obtain ⟨q, hq, hqzero⟩ := hconv.exists_mem_zero_iff_forall hne (fun j : S => f j)
    (fun j y hy => (hpres ▸ hy).2 j j.property)
  have hqstrict (j : S) : f j q < 0 := by
    refine lt_of_le_of_ne ((hpres ▸ hq).2 j j.property) fun hz => ?_
    obtain ⟨x, hxA, _, hx⟩ := hwitness j
    have heq : P.EqOn (f j) (AffineMap.const ℝ V 0) := by
      simpa only [Set.EqOn, AffineMap.const_apply] using (hqzero j).mp hz
    exact hx.ne' ((AffineMap.eqOn_affineSpan heq hxA).trans (AffineMap.const_apply _ _ _ _))
  refine ⟨S, hpres, fun j => ?_⟩
  obtain ⟨x, hxA, hxother, hxj⟩ := hwitness j
  obtain ⟨p, hseg, hpj, hpstrict⟩ :=
    exists_mem_openSegment_single_active (fun l : S => f l) j hqstrict hxj
      (fun l hl => hxother l (Finset.mem_erase.mpr ⟨fun e => hl (Subtype.ext e), l.property⟩))
  have hpA := A.convex.segment_subset (subset_affineSpan ℝ P hq) hxA
    (openSegment_subset_segment _ _ _ hseg)
  have hpP : p ∈ P := by
    rw [hpres]
    refine ⟨hpA, fun l hl => ?_⟩
    by_cases he : (⟨l, hl⟩ : S) = j
    · simpa only [← he] using hpj.le
    · exact (hpstrict ⟨l, hl⟩ he).le
  have hspan := vectorSpan_active_eq (fun l : S => f l) A j hpA hpj hpstrict
  have hset : {y | y ∈ A ∧ (∀ l : S, f l y ≤ 0) ∧ f j y = 0} = {y ∈ P | f j y = 0} := by
    ext y
    simp only [hpres, Set.mem_ofPred_eq, Subtype.forall, and_assoc]
  rw [hset, direction_affineSpan] at hspan
  refine ⟨⟨p, hpP, hpj, hpstrict⟩, hspan, fun h => ?_⟩
  have hv : (f j).linear (p -ᵥ q) = 0 := h (vsub_mem_vectorSpan ℝ hpP hq)
  rw [AffineMap.linear_apply_vsub, hpj, vsub_eq_sub, zero_sub, neg_eq_zero] at hv
  exact (hqstrict j).ne hv

/-- The active row cuts the dimension by one if its kernel gives the face direction and
the row is nonzero on the direction of the parent. -/
theorem finrank_vectorSpan_active_add_one (f : V →ᵃ[ℝ] ℝ)
    [FiniteDimensional ℝ (vectorSpan ℝ P)]
    (hdir : vectorSpan ℝ {x ∈ P | f x = 0} = vectorSpan ℝ P ⊓ f.linear.ker)
    (hn : ¬ vectorSpan ℝ P ≤ f.linear.ker) :
    finrank ℝ (vectorSpan ℝ {x ∈ P | f x = 0}) + 1 = finrank ℝ (vectorSpan ℝ P) := by
  rw [hdir, inf_comm]
  exact Module.Dual.finrank_ker_inf_add_one hn

variable [TopologicalSpace V]

/-- A relative frontier point satisfies the given finite family of inequalities, with
at least one original row active at that point. -/
theorem mem_and_exists_eq_zero_of_mem_intrinsicFrontier [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hpres : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0}) {x : V}
    (hx : x ∈ intrinsicFrontier ℝ P) : x ∈ P ∧ ∃ j, g j x = 0 := by
  let A := affineSpan ℝ P
  obtain ⟨a, ha, rfl⟩ := mem_intrinsicFrontier.mp hx
  have hcarrier : ((↑) ⁻¹' P : Set A) = ⋂ j, {y : A | g j (y : V) ≤ 0} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    exact (Set.ext_iff.mp hpres _).trans (and_iff_right y.property)
  have hclosed : IsClosed ((↑) ⁻¹' P : Set A) := hcarrier ▸ isClosed_iInter fun j =>
    isClosed_le ((g j).continuous.comp continuous_subtype_val) continuous_const
  have hxP := hclosed.frontier_subset ha
  refine ⟨hxP, ?_⟩
  by_contra! hn
  let U : Set A := {y | ∀ j, g j (y : V) < 0}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt ((g j).continuous.comp continuous_subtype_val) continuous_const
  have haU : a ∈ U := fun j => lt_of_le_of_ne ((Set.ext_iff.mp hpres _).mp hxP |>.2 j) (hn j)
  have hUP : U ⊆ ((↑) ⁻¹' P : Set A) := fun y hy =>
    (Set.ext_iff.mp hpres _).mpr ⟨y.property, fun j => (hy j).le⟩
  exact ha.2 (interior_mono hUP (by rwa [hU.interior_eq]))

variable [IsTopologicalAddGroup V] [FiniteDimensional ℝ (vectorSpan ℝ P)]

/-- Select facets from a specified finite presentation, retaining the original functionals
and their labels. Each retained row is uniquely active somewhere on its facet. -/
theorem exists_facet_subfamily [Finite ι] (f : ι → (V →ᴬ[ℝ] ℝ))
    (hf : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0}) :
    ∃ S : Finset ι, P = {x | x ∈ affineSpan ℝ P ∧ ∀ j ∈ S, f j x ≤ 0} ∧
      ∀ j : S, IsExposed ℝ P {x ∈ P | f j x = 0} ∧
        (∃ p ∈ P, f j p = 0 ∧ ∀ l : S, l ≠ j → f l p < 0) ∧
        finrank ℝ (vectorSpan ℝ {x ∈ P | f j x = 0}) + 1 = finrank ℝ (vectorSpan ℝ P) := by
  obtain ⟨S, hS, hrows⟩ := exists_irredundant_affine_subfamily (fun j => (f j).toAffineMap)
    (by simpa only [ContinuousAffineMap.coe_toAffineMap] using hf)
  refine ⟨S, hS, fun j => ?_⟩
  obtain ⟨hw, hk, hn⟩ := hrows j
  refine ⟨?_, hw, finrank_vectorSpan_active_add_one (f j).toAffineMap hk hn⟩
  have hsub : P ⊆ {x | ∀ l, f l x ≤ 0} := fun x hx => ((Set.ext_iff.mp hf x).mp hx).2
  convert (isExposed_setOf_active f {j.val}).inter_of_subset hsub using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_singleton, forall_eq]
  exact ⟨fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

namespace IsConvexPolyhedron

/-- A polyhedron has a finite presentation inside its affine span by exposed facets.
At each retained row a witness satisfies every other retained inequality strictly. -/
theorem exists_facet_presentation (hP : IsConvexPolyhedron P) :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → (V →ᴬ[ℝ] ℝ)),
      P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0} ∧
      ∀ j, IsExposed ℝ P {x ∈ P | g j x = 0} ∧
        (∃ p ∈ P, g j p = 0 ∧ ∀ l ≠ j, g l p < 0) ∧
        finrank ℝ (vectorSpan ℝ {x ∈ P | g j x = 0}) + 1 = finrank ℝ (vectorSpan ℝ P) := by
  obtain ⟨_, f, hf⟩ := isConvexPolyhedron_iff.mp hP
  have hrel : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0} := by
    ext x
    exact ⟨fun hx => ⟨subset_affineSpan ℝ P hx, (Set.ext_iff.mp hf x).mp hx⟩,
      fun hx => (Set.ext_iff.mp hf x).mpr hx.2⟩
  obtain ⟨S, hS, hrows⟩ := exists_facet_subfamily f hrel
  exact ⟨S, inferInstance, fun j => f j, by simpa only [Subtype.forall] using hS, hrows⟩

/-- Every relative frontier point lies on an exposed face of relative codimension one. -/
theorem exists_facet_of_mem_intrinsicFrontier (hP : IsConvexPolyhedron P) {x : V}
    (hx : x ∈ intrinsicFrontier ℝ P) : ∃ F, IsExposed ℝ P F ∧ x ∈ F ∧
      finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P) := by
  obtain ⟨_, _, g, hpres, hrows⟩ := hP.exists_facet_presentation
  obtain ⟨hxp, j, hj⟩ := mem_and_exists_eq_zero_of_mem_intrinsicFrontier g hpres hx
  exact ⟨_, (hrows j).1, ⟨hxp, hj⟩, (hrows j).2.2⟩

variable [ContinuousSMul ℝ V]

/-- The relative boundary consists precisely of the points on exposed facets. -/
theorem mem_intrinsicFrontier_iff_exists_facet (hP : IsConvexPolyhedron P) {x : V} :
    x ∈ intrinsicFrontier ℝ P ↔ ∃ F, IsExposed ℝ P F ∧ x ∈ F ∧
      finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P) := by
  refine ⟨hP.exists_facet_of_mem_intrinsicFrontier, ?_⟩
  rintro ⟨F, hF, hxF, hd⟩
  exact hF.subset_intrinsicFrontier (fun he => by subst F; omega) hxF

/-- The relative boundary is the union of the exposed facets. -/
theorem intrinsicFrontier_eq_sUnion_facets (hP : IsConvexPolyhedron P) :
    intrinsicFrontier ℝ P = ⋃₀ {F | IsExposed ℝ P F ∧
      finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P)} := by
  ext x
  simpa only [Set.mem_sUnion, Set.mem_ofPred_eq, exists_and_left, and_assoc, and_left_comm,
    and_comm] using hP.mem_intrinsicFrontier_iff_exists_facet (x := x)

/-- The relative boundary consists precisely of the points on proper exposed faces. -/
theorem mem_intrinsicFrontier_iff_exists_proper_isExposed (hP : IsConvexPolyhedron P) {x : V} :
    x ∈ intrinsicFrontier ℝ P ↔ ∃ F, IsExposed ℝ P F ∧ F ≠ P ∧ x ∈ F := by
  refine ⟨fun hx => ?_, fun ⟨_, hF, hne, hxF⟩ => hF.subset_intrinsicFrontier hne hxF⟩
  obtain ⟨F, hF, hxF, hd⟩ := hP.exists_facet_of_mem_intrinsicFrontier hx
  exact ⟨F, hF, fun he => by subst F; omega, hxF⟩

/-- The relative boundary is the union of all proper exposed faces. -/
theorem intrinsicFrontier_eq_sUnion_proper_isExposed (hP : IsConvexPolyhedron P) :
    intrinsicFrontier ℝ P = ⋃₀ {F | IsExposed ℝ P F ∧ F ≠ P} := by
  ext x
  simpa only [Set.mem_sUnion, Set.mem_ofPred_eq, and_assoc] using
    hP.mem_intrinsicFrontier_iff_exists_proper_isExposed (x := x)

end IsConvexPolyhedron

end TauCeti
