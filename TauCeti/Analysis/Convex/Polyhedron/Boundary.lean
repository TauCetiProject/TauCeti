/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Intrinsic
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.LinearAlgebra.AffineSpace.Codimension

/-!
# Relative interiors and boundaries of polyhedra

In a finite affine halfspace presentation, the relative interior is obtained by
making every inequality strict except those that vanish on the whole polyhedron.
The relative boundary is the union of the active-row faces of the remaining rows.
Redundant inequalities, empty and lower-dimensional polyhedra, unboundedness and lineality are
allowed.

Consequently the relative boundary of a polyhedron is covered by finitely many affine
subspaces of strictly smaller dimension. In particular, a polyhedron of codimension one has
relative boundary contained in finitely many affine subspaces of codimension at least two.

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

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A point is in the relative interior of a presented polyhedron precisely when it belongs to the
polyhedron and every defining row that is not identically zero on the polyhedron is strict at that
point. -/
theorem mem_intrinsicInterior_iff_forall_lt [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    {P : Set V} (hP : P = {x | ∀ j, g j x ≤ 0}) {x : V} :
    x ∈ intrinsicInterior ℝ P ↔
      x ∈ P ∧ ∀ j, (∃ p ∈ P, g j p < 0) → g j x < 0 := by
  constructor
  · intro hx
    refine ⟨intrinsicInterior_subset hx, fun j ⟨p, hp, hgp⟩ => ?_⟩
    have hle (y : V) (hy : y ∈ P) : g j y ≤ 0 := (hP ▸ hy) j
    refine lt_of_le_of_ne (hle x (intrinsicInterior_subset hx)) fun hx0 => ?_
    have := eq_zero_of_nonneg_of_mem_intrinsicInterior (g := -(g j).toAffineMap)
      (fun y hy => by simpa using hle y hy) hx (by simp [hx0]) hp
    simp only [FunLike.coe_neg, Pi.neg_apply, neg_eq_zero] at this
    exact hgp.ne this
  · rintro ⟨hxP, hxstrict⟩
    let A := affineSpan ℝ P
    let xA : A := ⟨x, subset_affineSpan ℝ P hxP⟩
    let J : Set ι := {j | ∃ p ∈ P, g j p < 0}
    let U : Set A := {y | ∀ j : J, g j.val (y : V) < 0}
    have hU : IsOpen U := by
      have heq : U = ⋂ j : J, {y : A | g j.val (y : V) < 0} := by ext y; simp [U]
      rw [heq]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt ((g j.val).continuous.comp continuous_subtype_val) continuous_const
    have hxU : xA ∈ U := fun j => hxstrict j.val j.property
    have hUP : U ⊆ ((↑) ⁻¹' P : Set A) := by
      intro y hy
      rw [hP]
      intro j
      by_cases hj : j ∈ J
      · exact (hy ⟨j, hj⟩).le
      · have hzero : ∀ p ∈ P, g j p = 0 := by
          intro p hp
          have hle : g j p ≤ 0 := by rw [hP] at hp; exact hp j
          apply le_antisymm hle
          by_contra hn
          exact hj ⟨p, hp, lt_of_not_ge hn⟩
        have heq : P.EqOn (g j).toAffineMap (0 : V →ᵃ[ℝ] ℝ) := hzero
        have hspan := AffineMap.eqOn_affineSpan heq y.property
        exact le_of_eq hspan
    have hxint : xA ∈ interior U := by rwa [hU.interior_eq]
    exact ⟨xA, interior_mono hUP hxint, rfl⟩

/-- The relative boundary of a presented polyhedron is exactly the union of the active-row faces
whose rows are not identically zero on the polyhedron. Every indexed face is proper; empty row
faces may occur and contribute nothing to the union. -/
theorem intrinsicFrontier_eq_iUnion_active [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    {P : Set V} (hP : P = {x | ∀ j, g j x ≤ 0}) :
    intrinsicFrontier ℝ P =
      ⋃ j ∈ {j | ∃ p ∈ P, g j p < 0}, {x ∈ P | g j x = 0} := by
  have hclosed : IsClosed P := by
    rw [hP]
    exact (isConvexPolyhedron_setOf_forall g).isClosed
  have hrel : intrinsicClosure ℝ P = P :=
    IsClosed.intrinsicClosure (hclosed.preimage
      (continuous_subtype_val : Continuous ((↑) : affineSpan ℝ P → V)))
  rw [← intrinsicClosure_sdiff_intrinsicInterior, hrel]
  ext x
  rw [Set.mem_sdiff, mem_intrinsicInterior_iff_forall_lt g hP]
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxP, hxnot⟩
    have hnot : ¬ ∀ j, (∃ p ∈ P, g j p < 0) → g j x < 0 :=
      fun h => hxnot ⟨hxP, h⟩
    push Not at hnot
    obtain ⟨j, hj, hgj⟩ := hnot
    have hle : g j x ≤ 0 := by rw [hP] at hxP; exact hxP j
    exact ⟨j, hj, hxP, le_antisymm hle hgj⟩
  · rintro ⟨j, hj, hxP, hgj⟩
    refine ⟨hxP, ?_⟩
    rintro ⟨_, hstrict⟩
    have hlt := hstrict j hj
    rw [hgj] at hlt
    exact lt_irrefl 0 hlt

variable [FiniteDimensional ℝ V]

/-- The relative boundary of a polyhedron is contained in finitely many affine
subspaces, each of strictly smaller direction dimension than the polyhedron.
Empty active faces are omitted, so the statement also handles empty sets. -/
theorem IsConvexPolyhedron.exists_finite_intrinsicFrontier_cover {P : Set V}
    (hP : IsConvexPolyhedron P) :
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
    rw [intrinsicFrontier_eq_iUnion_active g hP] at hx
    obtain ⟨j, hj, hxP, hzero⟩ := Set.mem_iUnion₂.mp hx
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
  obtain ⟨S, hcover, hS⟩ := hP.exists_finite_intrinsicFrontier_cover
  refine ⟨S, hcover, fun A hA => ?_⟩
  rw [← hdim]
  exact Nat.add_lt_add_right (hS A hA) 1

end TauCeti
