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
The facet dimension formulas and facet coverage assume that the parent direction is
finite-dimensional. With continuous scalar multiplication the intrinsic frontier is the union of
all nonempty proper exposed subsets, without finite dimension. In the finite-dimensional case it
is also the union of the nonempty exposed facets.
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

/-- Select a minimal finite subfamily of a relative presentation. Each retained row has a
point in the affine span violating it while satisfying every other retained inequality. -/
theorem exists_affine_subfamily_with_exterior_witness [Finite ι] (f : ι → (V →ᵃ[ℝ] ℝ))
    (hf : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0}) :
    ∃ S : Finset ι, P = {x | x ∈ affineSpan ℝ P ∧ ∀ j ∈ S, f j x ≤ 0} ∧
      ∀ j : S, ∃ x ∈ affineSpan ℝ P, 0 < f j x ∧ ∀ l : S, l ≠ j → f l x ≤ 0 := by
  classical
  let := Fintype.ofFinite ι
  let presents (S : Finset ι) := P = {x | x ∈ affineSpan ℝ P ∧ ∀ j ∈ S, f j x ≤ 0}
  have hu : presents Finset.univ := by simpa only [presents, Finset.mem_univ, forall_const] using hf
  obtain ⟨S, hS⟩ := exists_minimal_of_wellFoundedLT presents ⟨_, hu⟩
  have hpres := hS.1
  refine ⟨S, hpres, fun j => ?_⟩
  have hw : ∃ x ∈ affineSpan ℝ P, (∀ l ∈ S.erase j.val, f l x ≤ 0) ∧ 0 < f j.val x := by
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
  obtain ⟨x, hx, hother, hj⟩ := hw
  exact ⟨x, hx, hj, fun l hl => hother l
    (Finset.mem_erase.mpr ⟨fun e => hl (Subtype.ext e), l.property⟩)⟩

/-- For a nonempty finite relative presentation with an exterior violation witness for every
row, each row has a feasible point where only it is active. The active face direction is its
linear kernel inside the parent direction, and the row is nonzero on that direction. -/
theorem single_active_of_exterior_witness [Finite ι] (g : ι → (V →ᵃ[ℝ] ℝ))
    (hf : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0}) (hne : P.Nonempty)
    (hw : ∀ j, ∃ x ∈ affineSpan ℝ P, 0 < g j x ∧ ∀ l ≠ j, g l x ≤ 0) :
    ∀ j, (∃ p ∈ P, g j p = 0 ∧ ∀ l ≠ j, g l p < 0) ∧
      vectorSpan ℝ {p ∈ P | g j p = 0} = vectorSpan ℝ P ⊓ (g j).linear.ker ∧
      ¬ vectorSpan ℝ P ≤ (g j).linear.ker := by
  classical
  let A := affineSpan ℝ P
  have hconv : Convex ℝ P := by
    have hc := A.convex.inter (convex_iInter fun j => (convex_Iic (0 : ℝ)).affine_preimage (g j))
    convert hc using 1
    ext p
    simpa only [A, SetLike.mem_coe, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_Iic] using Set.ext_iff.mp hf p
  obtain ⟨q, hq, hqzero⟩ := hconv.exists_mem_zero_iff_forall hne g
    (fun j y hy => (hf ▸ hy).2 j)
  have hqstrict (j : ι) : g j q < 0 := by
    refine lt_of_le_of_ne ((hf ▸ hq).2 j) fun hz => ?_
    obtain ⟨x, hxA, hx, _⟩ := hw j
    have heq : P.EqOn (g j) (AffineMap.const ℝ V 0) := by
      simpa only [Set.EqOn, AffineMap.const_apply] using (hqzero j).mp hz
    exact hx.ne' ((AffineMap.eqOn_affineSpan heq hxA).trans (AffineMap.const_apply _ _ _ _))
  intro j
  obtain ⟨x, hxA, hxj, hxother⟩ := hw j
  obtain ⟨p, hseg, hpj, hpstrict⟩ :=
    exists_mem_openSegment_single_active g j hqstrict hxj hxother
  have hpA := A.convex.segment_subset (subset_affineSpan ℝ P hq) hxA
    (openSegment_subset_segment _ _ _ hseg)
  have hpP : p ∈ P := by
    rw [hf]
    refine ⟨hpA, fun l => ?_⟩
    by_cases he : l = j
    · simpa only [he] using hpj.le
    · exact (hpstrict l he).le
  have hspan := vectorSpan_active_eq g A j hpA hpj hpstrict
  have hset : {y | y ∈ A ∧ (∀ l, g l y ≤ 0) ∧ g j y = 0} = {y ∈ P | g j y = 0} := by
    ext y
    exact ⟨fun h => ⟨(Set.ext_iff.mp hf y).mpr ⟨h.1, h.2.1⟩, h.2.2⟩,
      fun h => ⟨((Set.ext_iff.mp hf y).mp h.1).1, ((Set.ext_iff.mp hf y).mp h.1).2, h.2⟩⟩
  rw [hset, direction_affineSpan] at hspan
  refine ⟨⟨p, hpP, hpj, hpstrict⟩, hspan, fun h => ?_⟩
  have hv : (g j).linear (p -ᵥ q) = 0 := h (vsub_mem_vectorSpan ℝ hpP hq)
  rw [AffineMap.linear_apply_vsub, hpj, vsub_eq_sub, zero_sub, neg_eq_zero] at hv
  exact (hqstrict j).ne hv

/-- Thin a finite relative half-space presentation to its own rows, retaining a strict
single-active witness, its face-direction kernel identity and non-containment for each row. -/
theorem exists_irredundant_affine_subfamily [Finite ι] (f : ι → (V →ᵃ[ℝ] ℝ))
    (hf : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0}) :
    ∃ S : Finset ι, P = {x | x ∈ affineSpan ℝ P ∧ ∀ j ∈ S, f j x ≤ 0} ∧
      ∀ j : S, (∃ p ∈ P, f j p = 0 ∧ ∀ l : S, l ≠ j → f l p < 0) ∧
        vectorSpan ℝ {p ∈ P | f j p = 0} = vectorSpan ℝ P ⊓ (f j).linear.ker ∧
        ¬ vectorSpan ℝ P ≤ (f j).linear.ker := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp⟩
  obtain ⟨S, hS, hw⟩ := exists_affine_subfamily_with_exterior_witness f hf
  refine ⟨S, hS, single_active_of_exterior_witness (fun j : S => f j) ?_ hne hw⟩
  simpa only [Subtype.forall] using hS

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

variable [IsTopologicalAddGroup V]

/-- The zero locus of one row of a relative half-space presentation exposes a subset
of its carrier. -/
theorem isExposed_setOf_eq_zero_of_relative_presentation (f : ι → (V →ᴬ[ℝ] ℝ))
    (hf : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0}) (j : ι) :
    IsExposed ℝ P {x ∈ P | f j x = 0} := by
  have hsub : P ⊆ {x | ∀ l, f l x ≤ 0} := fun x hx => ((Set.ext_iff.mp hf x).mp hx).2
  convert (isExposed_setOf_active f {j}).inter_of_subset hsub using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_singleton, forall_eq]
  exact ⟨fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

section FiniteDimension

variable [FiniteDimensional ℝ (vectorSpan ℝ P)]

/-- Select facets from a specified finite presentation, retaining the original functionals
and their labels. Each retained row is uniquely active somewhere on its facet. -/
theorem exists_facet_subfamily [Finite ι] (f : ι → (V →ᴬ[ℝ] ℝ))
    (hf : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0}) :
    ∃ S : Finset ι, P = {x | x ∈ affineSpan ℝ P ∧ ∀ j ∈ S, f j x ≤ 0} ∧
      ∀ j : S, IsExposed ℝ P {x ∈ P | f j x = 0} ∧
        (∃ p ∈ P, f j p = 0 ∧ ∀ l : S, l ≠ j → f l p < 0) ∧
        vectorSpan ℝ {x ∈ P | f j x = 0} = vectorSpan ℝ P ⊓ (f j).toAffineMap.linear.ker ∧
        ¬ vectorSpan ℝ P ≤ (f j).toAffineMap.linear.ker ∧
        finrank ℝ (vectorSpan ℝ {x ∈ P | f j x = 0}) + 1 = finrank ℝ (vectorSpan ℝ P) := by
  obtain ⟨S, hS, hrows⟩ := exists_irredundant_affine_subfamily (fun j => (f j).toAffineMap)
    (by simpa only [ContinuousAffineMap.coe_toAffineMap] using hf)
  simp only [ContinuousAffineMap.coe_toAffineMap] at hS hrows
  refine ⟨S, hS, fun j => ?_⟩
  obtain ⟨hw, hk, hn⟩ := hrows j
  refine ⟨isExposed_setOf_eq_zero_of_relative_presentation f hf j, hw, hk, hn, ?_⟩
  rw [hk, inf_comm]
  exact Module.Dual.finrank_ker_inf_add_one hn

namespace IsConvexPolyhedron

/-- A polyhedron has a finite presentation inside its affine span by exposed facets.
At each retained row a witness satisfies every other retained inequality strictly. -/
theorem exists_facet_presentation (hP : IsConvexPolyhedron P) :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → (V →ᴬ[ℝ] ℝ)),
      P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0} ∧
      ∀ j, IsExposed ℝ P {x ∈ P | g j x = 0} ∧
        (∃ p ∈ P, g j p = 0 ∧ ∀ l ≠ j, g l p < 0) ∧
        vectorSpan ℝ {x ∈ P | g j x = 0} = vectorSpan ℝ P ⊓ (g j).toAffineMap.linear.ker ∧
        ¬ vectorSpan ℝ P ≤ (g j).toAffineMap.linear.ker ∧
        finrank ℝ (vectorSpan ℝ {x ∈ P | g j x = 0}) + 1 = finrank ℝ (vectorSpan ℝ P) := by
  obtain ⟨_, f, hf⟩ := isConvexPolyhedron_iff.mp hP
  have hrel : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0} := by
    change P = (affineSpan ℝ P : Set V) ∩ {x | ∀ j, f j x ≤ 0}
    rw [← hf]
    exact (Set.inter_eq_right.mpr (subset_affineSpan ℝ P)).symm
  obtain ⟨S, hS, hrows⟩ := exists_facet_subfamily f hrel
  exact ⟨S, inferInstance, fun j => f j, by simpa only [Subtype.forall] using hS, hrows⟩

/-- Every relative frontier point lies on an exposed face of relative codimension one. -/
theorem exists_facet_of_mem_intrinsicFrontier (hP : IsConvexPolyhedron P) {x : V}
    (hx : x ∈ intrinsicFrontier ℝ P) : ∃ F, IsExposed ℝ P F ∧ x ∈ F ∧
      finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P) := by
  obtain ⟨_, _, g, hpres, hrows⟩ := hP.exists_facet_presentation
  obtain ⟨hxp, j, hj⟩ := mem_and_exists_eq_zero_of_mem_intrinsicFrontier g hpres hx
  exact ⟨_, (hrows j).1, ⟨hxp, hj⟩, (hrows j).2.2.2.2⟩

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
    intrinsicFrontier ℝ P = ⋃₀ {F | IsExposed ℝ P F ∧ F.Nonempty ∧
      finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P)} := by
  ext x
  rw [hP.mem_intrinsicFrontier_iff_exists_facet]
  simp only [Set.mem_sUnion, Set.mem_ofPred_eq]
  exact ⟨fun ⟨F, hF, hxF, hd⟩ => ⟨F, ⟨hF, ⟨x, hxF⟩, hd⟩, hxF⟩,
    fun ⟨F, ⟨hF, _, hd⟩, hxF⟩ => ⟨F, hF, hxF, hd⟩⟩

end IsConvexPolyhedron

end FiniteDimension

namespace IsConvexPolyhedron

variable [ContinuousSMul ℝ V]

/-- In a topological real module, without a finite-dimensionality assumption, the relative
boundary of a polyhedron consists of points on nonempty proper exposed subsets. -/
theorem mem_intrinsicFrontier_iff_exists_isExposed_ne (hP : IsConvexPolyhedron P) {x : V} :
    x ∈ intrinsicFrontier ℝ P ↔ ∃ F, IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧ x ∈ F := by
  refine ⟨fun hx => ?_, fun ⟨_, hF, _, hne, hxF⟩ => hF.subset_intrinsicFrontier hne hxF⟩
  obtain ⟨_, f, hf⟩ := isConvexPolyhedron_iff.mp hP
  have hrel : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0} := by
    change P = (affineSpan ℝ P : Set V) ∩ {x | ∀ j, f j x ≤ 0}
    rw [← hf]
    exact (Set.inter_eq_right.mpr (subset_affineSpan ℝ P)).symm
  obtain ⟨S, hS, hrows⟩ := exists_irredundant_affine_subfamily (fun j => (f j).toAffineMap)
    (by simpa only [ContinuousAffineMap.coe_toAffineMap] using hrel)
  simp only [ContinuousAffineMap.coe_toAffineMap] at hS hrows
  have hpres : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j : S, f j x ≤ 0} := by
    simpa only [Subtype.forall] using hS
  obtain ⟨hxp, j, hj⟩ := mem_and_exists_eq_zero_of_mem_intrinsicFrontier (fun j : S => f j) hpres hx
  refine ⟨_, isExposed_setOf_eq_zero_of_relative_presentation f hrel j,
    ⟨x, hxp, hj⟩, ?_, ⟨hxp, hj⟩⟩
  intro he
  obtain ⟨_, hk, hn⟩ := hrows j
  rw [he] at hk
  exact hn (inf_eq_left.mp hk.symm)

/-- Without a finite-dimensionality assumption, the relative boundary is the union of
all nonempty proper exposed subsets. -/
theorem intrinsicFrontier_eq_sUnion_isExposed_ne (hP : IsConvexPolyhedron P) :
    intrinsicFrontier ℝ P = ⋃₀ {F | IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P} := by
  ext x
  simpa only [Set.mem_sUnion, Set.mem_ofPred_eq, and_assoc] using
    hP.mem_intrinsicFrontier_iff_exists_isExposed_ne (x := x)

end IsConvexPolyhedron

end TauCeti
