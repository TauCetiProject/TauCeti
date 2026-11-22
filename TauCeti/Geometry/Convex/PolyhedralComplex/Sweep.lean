/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Sweep.Exceptional
public import TauCeti.Geometry.Convex.PolyhedralComplex.Skeleton

/-!
# Sweep exceptions for a polyhedral skeleton

For a finite set of directions, the affine spans of the sweeps of the
codimension-at-least-two cells form an exceptional arrangement. A base point
outside that arrangement has its full line in every specified direction
disjoint from each of those cell spans and hence from the skeleton.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Discriminant.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : Toric.IsIntegralLattice i}

/-- The arrangement of affine spans of sweeps of the codimension-at-least-two
cells in the specified directions. Zero and tangent directions are allowed. -/
noncomputable def skeletonSweepExceptions (C : FinitePolyhedralComplex h)
    (vectors : Finset V) : ExceptionalArrangement ℝ V :=
  ExceptionalArrangement.ofSweeps ((C.codimensionGE 2).cells ×ˢ vectors) (by
    intro z hz _
    have hd := (mem_cells_codimensionGE.mp (Finset.mem_product.mp hz).1).2
    rw [← direction_affineSpan]
    omega)

open Classical in
/-- The exceptions are the affine spans of the sweeps of the skeleton cells. -/
@[simp]
theorem exceptions_skeletonSweepExceptions (C : FinitePolyhedralComplex h)
    (vectors : Finset V) :
    (C.skeletonSweepExceptions vectors).exceptions =
      ((C.codimensionGE 2).cells ×ˢ vectors).image
        (fun z => affineSpan ℝ (Set.sweep ℝ z.1 z.2)) := by
  classical
  exact ExceptionalArrangement.exceptions_ofSweeps _ _

/-- Genericity means that the line in each specified direction misses the
affine span of each cell of codimension at least two. -/
@[simp]
theorem isGeneric_skeletonSweepExceptions_iff {C : FinitePolyhedralComplex h}
    {vectors : Finset V} {x : V} :
    (C.skeletonSweepExceptions vectors).IsGeneric x ↔
      ∀ P ∈ (C.codimensionGE 2).cells, ∀ v ∈ vectors, ∀ t : ℝ, x + t • v ∉ affineSpan ℝ P := by
  rw [skeletonSweepExceptions, ExceptionalArrangement.isGeneric_ofSweeps_iff]
  constructor
  · intro hx P hP v hv t
    exact hx (P, v) (Finset.mem_product.mpr ⟨hP, hv⟩) t
  · rintro hx ⟨P, v⟩ hz t
    obtain ⟨hP, hv⟩ := Finset.mem_product.mp hz
    exact hx P hP v hv t

/-- Every full line from a generic base point in a specified direction misses
the support of the codimension-at-least-two skeleton. -/
theorem add_smul_notMem_support_codimensionGE_two {C : FinitePolyhedralComplex h}
    {vectors : Finset V} {x v : V} (hx : (C.skeletonSweepExceptions vectors).IsGeneric x)
    (hv : v ∈ vectors) (t : ℝ) : x + t • v ∉ (C.codimensionGE 2).support := by
  intro ht
  obtain ⟨P, hP, htP⟩ := mem_support.mp ht
  exact isGeneric_skeletonSweepExceptions_iff.mp hx P hP v hv t (subset_affineSpan ℝ P htP)

end TauCeti.FinitePolyhedralComplex
