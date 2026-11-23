/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Direction
public import Mathlib.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.Polyhedron.Boundary
import TauCeti.LinearAlgebra.AffineSpace.Span
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
The continuous irredundant presentation additionally retains exposedness, without finite
dimension. The facet dimension formulas and facet coverage assume that the parent direction is
finite-dimensional. With continuous addition and scalar multiplication, the intrinsic frontier
is the union of its nonempty exposed facets.
General proper-exposed boundary characterizations belong to
`TauCeti.Analysis.Convex.Polyhedron.Boundary`.
-/

public section

open Set Module AffineSubspace

namespace TauCeti

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] {P : Set V}

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
    exact hS.not_prop_of_lt (Finset.erase_ssubset j.property) herase
  obtain ⟨x, hx, hother, hj⟩ := hw
  exact ⟨x, hx, hj, fun l hl => hother l
    (Finset.mem_erase.mpr ⟨fun e => hl (Subtype.ext e), l.property⟩)⟩

/-- For a finite relative presentation with an exterior violation witness for every
row, each row has a feasible point where only it is active. The active face direction is its
linear kernel inside the parent direction, and the row is nonzero on that direction. -/
theorem single_active_of_exterior_witness [Finite ι] (g : ι → (V →ᵃ[ℝ] ℝ))
    (hf : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0})
    (hw : ∀ j, ∃ x ∈ affineSpan ℝ P, 0 < g j x ∧ ∀ l ≠ j, g l x ≤ 0) :
    ∀ j, (∃ p ∈ P, g j p = 0 ∧ ∀ l ≠ j, g l p < 0) ∧
      vectorSpan ℝ {p ∈ P | g j p = 0} = vectorSpan ℝ P ⊓ (g j).linear.ker ∧
      ¬ vectorSpan ℝ P ≤ (g j).linear.ker := by
  classical
  intro j
  have hne : P.Nonempty := by
    obtain ⟨x, hxA, _, _⟩ := hw j
    exact (affineSpan_nonempty ℝ).mp ⟨x, hxA⟩
  let A := affineSpan ℝ P
  have hconv : Convex ℝ P := by
    rw [hf, Set.ofPred_and, SetLike.setOfPred_mem_eq, Set.ofPred_forall]
    exact A.convex.inter (convex_iInter fun j => (convex_Iic (0 : ℝ)).affine_preimage (g j))
  obtain ⟨q, hq, hqzero⟩ := hconv.exists_mem_zero_iff_forall hne g
    (fun j y hy => (hf ▸ hy).2 j)
  have hqstrict (j : ι) : g j q < 0 := by
    refine lt_of_le_of_ne ((hf ▸ hq).2 j) fun hz => ?_
    obtain ⟨x, hxA, hx, _⟩ := hw j
    have heq : P.EqOn (g j) (AffineMap.const ℝ V 0) := by
      simpa only [Set.EqOn, AffineMap.const_apply] using (hqzero j).mp hz
    exact hx.ne' ((AffineMap.eqOn_affineSpan heq hxA).trans (AffineMap.const_apply _ _ _ _))
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
  have hv := LinearMap.mem_ker.mp (h (vsub_mem_vectorSpan ℝ hpP hq))
  rw [AffineMap.linear_apply_vsub] at hv
  have hgq : g j q = 0 := by simpa [hpj] using hv
  exact (hqstrict j).ne hgq

/-- A finite subfamily `S` of `f` still presents `P` within its affine span. Each `j ∈ S`
has a point of `P` where `j` is active and every other retained row in `S` is strictly negative.
The face direction is the row kernel within the parent direction, and `vectorSpan ℝ P`
is not contained in `(f j).linear.ker`. -/
theorem exists_irredundant_affine_subfamily [Finite ι] (f : ι → (V →ᵃ[ℝ] ℝ))
    (hf : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0}) :
    ∃ S : Finset ι, P = {x | x ∈ affineSpan ℝ P ∧ ∀ j ∈ S, f j x ≤ 0} ∧
      ∀ j : S, (∃ p ∈ P, f j p = 0 ∧ ∀ l : S, l ≠ j → f l p < 0) ∧
        vectorSpan ℝ {p ∈ P | f j p = 0} = vectorSpan ℝ P ⊓ (f j).linear.ker ∧
        ¬ vectorSpan ℝ P ≤ (f j).linear.ker := by
  obtain ⟨S, hS, hw⟩ := exists_affine_subfamily_with_exterior_witness f hf
  refine ⟨S, hS, single_active_of_exterior_witness (fun j : S => f j) ?_ hw⟩
  simpa only [Subtype.forall] using hS

variable [TopologicalSpace V]

/-- A finite subfamily `S` of `f` still presents `P` within its affine span. Each `j ∈ S`
has an exposed active face and a witness `p ∈ P` where `f j p = 0` and every other selected row
`l ∈ S` is strictly negative. Its face direction is `vectorSpan ℝ P ⊓ (f j).toAffineMap.linear.ker`,
and the parent direction is not contained in `(f j).toAffineMap.linear.ker`. -/
theorem exists_irredundant_subfamily [Finite ι] (f : ι → (V →ᴬ[ℝ] ℝ))
    (hf : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, f j x ≤ 0}) :
    ∃ S : Finset ι, P = {x | x ∈ affineSpan ℝ P ∧ ∀ j ∈ S, f j x ≤ 0} ∧
      ∀ j : S, IsExposed ℝ P {x ∈ P | f j x = 0} ∧
        (∃ p ∈ P, f j p = 0 ∧ ∀ l : S, l ≠ j → f l p < 0) ∧
        vectorSpan ℝ {x ∈ P | f j x = 0} = vectorSpan ℝ P ⊓ (f j).toAffineMap.linear.ker ∧
        ¬ vectorSpan ℝ P ≤ (f j).toAffineMap.linear.ker := by
  obtain ⟨S, hS, hrows⟩ := exists_irredundant_affine_subfamily (fun j => (f j).toAffineMap)
    (by simpa only [ContinuousAffineMap.coe_toAffineMap] using hf)
  simp only [ContinuousAffineMap.coe_toAffineMap] at hS hrows
  exact ⟨S, hS, fun j => ⟨(f j).isExposed_setOf_eq_of_le
    (fun y hy => ((Set.ext_iff.mp hf y).mp hy).2 j), hrows j⟩⟩

/-- A polyhedron has an irredundant continuous presentation within its affine span.
The single chosen presentation retains strict witnesses, face kernels and non-containment,
without a finite-dimensionality assumption. -/
theorem IsConvexPolyhedron.exists_irredundant_presentation (hP : IsConvexPolyhedron P) :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → (V →ᴬ[ℝ] ℝ)),
      P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0} ∧
      ∀ j, IsExposed ℝ P {x ∈ P | g j x = 0} ∧
        (∃ p ∈ P, g j p = 0 ∧ ∀ l ≠ j, g l p < 0) ∧
        vectorSpan ℝ {x ∈ P | g j x = 0} = vectorSpan ℝ P ⊓ (g j).toAffineMap.linear.ker ∧
        ¬ vectorSpan ℝ P ≤ (g j).toAffineMap.linear.ker := by
  obtain ⟨_, f, hf⟩ := isConvexPolyhedron_iff.mp hP
  have hrel := eq_setOf_mem_affineSpan_and (k := ℝ) hf
  obtain ⟨S, hS, hrows⟩ := exists_irredundant_subfamily f hrel
  exact ⟨S, inferInstance, fun j => f j, by simpa only [Subtype.forall] using hS, hrows⟩

section FiniteDimension

variable [FiniteDimensional ℝ (vectorSpan ℝ P)]

namespace IsConvexPolyhedron

/-- Every relative frontier point lies on an exposed face of relative codimension one. -/
theorem exists_facet_of_mem_intrinsicFrontier (hP : IsConvexPolyhedron P) {x : V}
    (hx : x ∈ intrinsicFrontier ℝ P) : ∃ F, IsExposed ℝ P F ∧ x ∈ F ∧
      finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P) := by
  obtain ⟨_, _, g, hpres, hrows⟩ := hP.exists_irredundant_presentation
  obtain ⟨j, _, hxp, hj⟩ :=
    Set.mem_iUnion₂.mp (intrinsicFrontier_subset_iUnion_active g hpres hx)
  obtain ⟨he, _, hk, hn⟩ := hrows j
  refine ⟨_, he, ⟨hxp, hj⟩, ?_⟩
  rw [hk, inf_comm]
  exact Module.Dual.finrank_ker_inf_add_one hn

variable [ContinuousAdd V] [ContinuousSMul ℝ V]

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

end TauCeti
