/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Exposed
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.LinearAlgebra.AffineSpace.Codimension
import TauCeti.LinearAlgebra.AffineSpace.Span

/-!
# Relative interiors and boundaries of polyhedra

In a finite affine halfspace presentation, the relative interior is obtained by
making every inequality strict except those that vanish on the whole polyhedron.
The relative boundary is the union of the active-row faces of the remaining rows.
Redundant inequalities, empty and lower-dimensional polyhedra, unboundedness and lineality are
allowed. The reverse interior implication and active-row frontier cover only require a topology
on the real module. The full interior characterization requires continuous addition and scalar
multiplication. Proper-exposed frontier coverage requires only the ambient topology. Its converse
and union characterization require continuous addition and scalar multiplication, without finite
dimension.

When the parent affine direction is finite-dimensional, the relative boundary of a polyhedron
is covered by finitely many affine subspaces of strictly smaller direction dimension. In particular,
a polyhedron of codimension one has relative boundary contained in finitely many affine subspaces
of codimension at least two.

## Main results

* `TauCeti.mem_intrinsicInterior_iff_forall_lt`: relative interior of a presented polyhedron.
* `TauCeti.intrinsicFrontier_eq_iUnion_active`: relative boundary of a presented polyhedron.
* `TauCeti.IsConvexPolyhedron.exists_finite_intrinsicFrontier_cover`: the relative boundary is
  covered by finitely many affine subspaces of smaller dimension.
* `TauCeti.IsConvexPolyhedron.exists_finite_intrinsicFrontier_cover_codim_two`: for a polyhedron
  of codimension one, the covering subspaces have codimension at least two.

## Attribution

Adapted from `Mei/Geometry/Convex/Polyhedron/Boundary.lean` and
`Mei/Geometry/Convex/Polyhedron/Boundary/Codimension.lean` in Mei at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca/Mei/Geometry/Convex/Polyhedron/Boundary.lean
-/

public section

open Set AffineSubspace

namespace TauCeti

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V]

variable [TopologicalSpace V]

/-- Strictness of every row which is nonzero on the carrier gives relative interior,
for a finite continuous relative half-space presentation. No continuity of the vector-space
operations is required. -/
theorem mem_intrinsicInterior_of_forall_lt [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    {P : Set V} (hP : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0}) {x : V}
    (hxP : x ∈ P) (hxstrict : ∀ j, (∃ p ∈ P, g j p < 0) → g j x < 0) :
    x ∈ intrinsicInterior ℝ P := by
  let A := affineSpan ℝ P
  let xA : A := ⟨x, subset_affineSpan ℝ P hxP⟩
  let J : Set ι := {j | ∃ p ∈ P, g j p < 0}
  let U : Set A := {y | ∀ j : J, g j.val (y : V) < 0}
  have hU : IsOpen U := by
    have heq : U = ⋂ j : J, {y : A | g j.val (y : V) < 0} := by ext y; simp [U]
    rw [heq]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt ((g j.val).continuous.comp continuous_subtypeVal) continuous_const
  have hxU : xA ∈ U := fun j => hxstrict j.val j.property
  have hUP : U ⊆ ((↑) ⁻¹' P : Set A) := by
    intro y hy
    rw [hP]
    refine ⟨y.property, fun j => ?_⟩
    by_cases hj : j ∈ J
    · exact (hy ⟨j, hj⟩).le
    · have hzero : ∀ p ∈ P, g j p = 0 := by
        intro p hp
        have hle : g j p ≤ 0 := by rw [hP] at hp; exact hp.2 j
        apply le_antisymm hle
        by_contra hn
        exact hj ⟨p, hp, lt_of_not_ge hn⟩
      have heq : P.EqOn (g j).toAffineMap (0 : V →ᵃ[ℝ] ℝ) := by
        simpa only [Set.EqOn, ContinuousAffineMap.coe_toAffineMap, FunLike.coe_zero,
          Pi.zero_apply] using hzero
      have hspan := AffineMap.eqOn_affineSpan heq y.property
      simp only [ContinuousAffineMap.coe_toAffineMap, FunLike.coe_zero, Pi.zero_apply] at hspan
      exact le_of_eq hspan
  have hxint : xA ∈ interior U := by rwa [hU.interior_eq]
  exact mem_intrinsicInterior.mpr ⟨xA, interior_mono hUP hxint, rfl⟩

/-- A finite continuous relative presentation covers its relative frontier by the active
faces of rows which do not vanish on the carrier. Only the ambient topology is used. -/
theorem intrinsicFrontier_subset_iUnion_active [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    {P : Set V} (hP : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0}) :
    intrinsicFrontier ℝ P ⊆
      ⋃ j ∈ {j | ∃ p ∈ P, g j p < 0}, {x ∈ P | g j x = 0} := by
  intro x hx
  have hcarrier : ((↑) ⁻¹' P : Set (affineSpan ℝ P)) =
      ⋂ j, {y : affineSpan ℝ P | g j (y : V) ≤ 0} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    exact (Set.ext_iff.mp hP _).trans (and_iff_right y.property)
  have hclosed : IsClosed ((↑) ⁻¹' P : Set (affineSpan ℝ P)) :=
    hcarrier ▸ isClosed_iInter fun j =>
      isClosed_le ((g j).continuous.comp continuous_subtypeVal) continuous_const
  rw [← intrinsicClosure_sdiff_intrinsicInterior, hclosed.intrinsicClosure] at hx
  have hn : ¬ ∀ j, (∃ p ∈ P, g j p < 0) → g j x < 0 :=
    fun h => hx.2 (mem_intrinsicInterior_of_forall_lt g hP hx.1 h)
  push Not at hn
  obtain ⟨j, hj, hgj⟩ := hn
  have hle : g j x ≤ 0 := ((Set.ext_iff.mp hP _).mp hx.1).2 j
  exact Set.mem_iUnion₂.mpr ⟨j, hj, hx.1, le_antisymm hle hgj⟩

section TopologicalModule

variable [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- A point is in the relative interior of a presented polyhedron precisely when it belongs to the
polyhedron and every defining row that is not identically zero on the polyhedron is strict at that
point. -/
theorem mem_intrinsicInterior_iff_forall_lt [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    {P : Set V} (hP : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0}) {x : V} :
    x ∈ intrinsicInterior ℝ P ↔
      x ∈ P ∧ ∀ j, (∃ p ∈ P, g j p < 0) → g j x < 0 := by
  constructor
  · intro hx
    refine ⟨intrinsicInterior_subset hx, fun j ⟨p, hp, hgp⟩ => ?_⟩
    have hle (y : V) (hy : y ∈ P) : g j y ≤ 0 := (hP ▸ hy).2 j
    refine lt_of_le_of_ne (hle x (intrinsicInterior_subset hx)) fun hx0 => ?_
    have := eq_zero_of_nonneg_of_mem_intrinsicInterior (g := -(g j).toAffineMap)
      (fun y hy => by simpa using hle y hy) hx (by simp [hx0]) hp
    simp only [FunLike.coe_neg, Pi.neg_apply, neg_eq_zero] at this
    exact hgp.ne this
  · rintro ⟨hxP, hxstrict⟩
    exact mem_intrinsicInterior_of_forall_lt g hP hxP hxstrict

/-- The relative boundary of a presented polyhedron is exactly the union of the active-row faces
whose rows are not identically zero on the polyhedron. Every indexed face is proper; empty row
faces may occur and contribute nothing to the union. -/
theorem intrinsicFrontier_eq_iUnion_active [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    {P : Set V} (hP : P = {x | x ∈ affineSpan ℝ P ∧ ∀ j, g j x ≤ 0}) :
    intrinsicFrontier ℝ P =
      ⋃ j ∈ {j | ∃ p ∈ P, g j p < 0}, {x ∈ P | g j x = 0} := by
  refine Set.Subset.antisymm (intrinsicFrontier_subset_iUnion_active g hP) ?_
  rintro x hx
  obtain ⟨j, hj, hxP, hgj⟩ := Set.mem_iUnion₂.mp hx
  rw [← intrinsicClosure_sdiff_intrinsicInterior]
  refine ⟨subset_intrinsicClosure hxP, ?_⟩
  intro hi
  have hlt := (mem_intrinsicInterior_iff_forall_lt g hP).mp hi |>.2 j hj
  exact hlt.ne hgj

end TopologicalModule

namespace IsConvexPolyhedron

/-- Every relative frontier point lies in a proper exposed subset of a polyhedron.
The forward coverage needs only the ambient topology, without continuity of the module
operations or finite dimension. -/
theorem exists_isExposed_ne_of_mem_intrinsicFrontier {P : Set V}
    (hP : IsConvexPolyhedron P) {x : V} (hx : x ∈ intrinsicFrontier ℝ P) :
    ∃ F, IsExposed ℝ P F ∧ x ∈ F ∧ F ≠ P := by
  obtain ⟨_, g, hg⟩ := isConvexPolyhedron_iff.mp hP
  have hrel := eq_setOf_mem_affineSpan_and (k := ℝ) hg
  obtain ⟨j, ⟨p, hp, hjp⟩, hxP, hjx⟩ :=
    Set.mem_iUnion₂.mp (intrinsicFrontier_subset_iUnion_active g hrel hx)
  refine ⟨_, (g j).isExposed_setOf_eq_of_le (fun y hy => (hg ▸ hy) j),
    ⟨hxP, hjx⟩, ?_⟩
  intro he
  have hz : g j p = 0 := (he.symm ▸ hp).2
  exact hjp.ne hz

variable [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- In a topological real module the relative frontier of a polyhedron consists of
points belonging to proper exposed subsets, without finite dimension. -/
theorem mem_intrinsicFrontier_iff_exists_isExposed_ne {P : Set V}
    (hP : IsConvexPolyhedron P) {x : V} :
    x ∈ intrinsicFrontier ℝ P ↔ ∃ F, IsExposed ℝ P F ∧ x ∈ F ∧ F ≠ P :=
  ⟨hP.exists_isExposed_ne_of_mem_intrinsicFrontier,
    fun ⟨_, hF, hxF, hne⟩ => hF.subset_intrinsicFrontier hne hxF⟩

/-- The relative frontier of a polyhedron is the union of all its nonempty proper
exposed subsets, without finite dimension. Nonemptiness omits the empty subset from the family. -/
theorem intrinsicFrontier_eq_sUnion_isExposed_ne {P : Set V} (hP : IsConvexPolyhedron P) :
    intrinsicFrontier ℝ P = ⋃₀ {F | IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P} := by
  ext x
  rw [hP.mem_intrinsicFrontier_iff_exists_isExposed_ne]
  simp only [Set.mem_sUnion, Set.mem_ofPred_eq]
  exact ⟨fun ⟨F, hF, hxF, hne⟩ => ⟨F, ⟨hF, ⟨x, hxF⟩, hne⟩, hxF⟩,
    fun ⟨F, ⟨hF, _, hne⟩, hxF⟩ => ⟨F, hF, hxF, hne⟩⟩

end IsConvexPolyhedron

/-- The relative boundary of a polyhedron is contained in finitely many affine
subspaces, each of strictly smaller direction dimension than the polyhedron.
Empty active faces are omitted, so the statement also handles empty sets. -/
theorem IsConvexPolyhedron.exists_finite_intrinsicFrontier_cover {P : Set V}
    [FiniteDimensional ℝ (affineSpan ℝ P).direction] (hP : IsConvexPolyhedron P) :
    ∃ S : Finset (AffineSubspace ℝ V),
      intrinsicFrontier ℝ P ⊆ ⋃ A ∈ S, (A : Set V) ∧
      ∀ A ∈ S, Module.finrank ℝ A.direction <
        Module.finrank ℝ (affineSpan ℝ P).direction := by
  classical
  obtain ⟨n, g, hP⟩ := isConvexPolyhedron_iff.mp hP
  let J := {j : Fin n | (∃ p ∈ P, g j p < 0) ∧ {x ∈ P | g j x = 0}.Nonempty}
  let S : Finset (AffineSubspace ℝ V) :=
    (Finset.univ.filter (fun j => j ∈ J)).image
      (fun j => affineSpan ℝ {x ∈ P | g j x = 0})
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, hxP, hzero⟩ := Set.mem_iUnion₂.mp
      (intrinsicFrontier_subset_iUnion_active g (eq_setOf_mem_affineSpan_and hP) hx)
    apply Set.mem_iUnion₂.mpr
    refine ⟨affineSpan ℝ {x ∈ P | g j x = 0}, ?_, subset_affineSpan ℝ _ ⟨hxP, hzero⟩⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hj, ⟨x, hxP, hzero⟩⟩, rfl⟩
  · intro A hA
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨⟨p, hp, hgp⟩, hne⟩ := (Finset.mem_filter.mp hj).2
    exact (g j).toAffineMap.finrank_direction_inter_zero_lt hne ⟨p, hp, ne_of_lt hgp⟩

/-- The relative boundary of a codimension-one polyhedron is covered by
finitely many affine subspaces of codimension at least two. -/
theorem IsConvexPolyhedron.exists_finite_intrinsicFrontier_cover_codim_two {P : Set V}
    (hP : IsConvexPolyhedron P)
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + 1 = Module.finrank ℝ V) :
    ∃ S : Finset (AffineSubspace ℝ V),
      intrinsicFrontier ℝ P ⊆ ⋃ A ∈ S, (A : Set V) ∧
      ∀ A ∈ S, Module.finrank ℝ A.direction + 1 < Module.finrank ℝ V := by
  have : FiniteDimensional ℝ V := .of_finrank_eq_succ hdim.symm
  obtain ⟨S, hcover, hS⟩ := hP.exists_finite_intrinsicFrontier_cover
  refine ⟨S, hcover, fun A hA => ?_⟩
  rw [← hdim]
  exact Nat.add_lt_add_right (hS A hA) 1

end TauCeti
