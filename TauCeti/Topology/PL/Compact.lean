/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map
public import TauCeti.Analysis.Convex.Polyhedron.Pi
import Mathlib.Topology.Compactness.Compact

/-!
# Finite PL decompositions on compact sets

A PL map on a compact subset of a finite real coordinate space admits a finite
piecewise-affine decomposition. Compactness thus lets one use finitely many
affine pieces to describe a map given by local PL data.

In particular, coning a PL map with compact base can use a finite decomposition
at the apex, even though `IsPLOn` is defined using local decompositions.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*,
Springer (1972), Example 1.5(4), p. 5, and Corollary 2.3, p. 12.
-/

public section

open Set Filter Topology Metric

namespace TauCeti

variable {ι : Type*} [Finite ι]
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {s : Set (ι → ℝ)} {f : (ι → ℝ) → F}

/-- A PL map on a compact subset of a finite real coordinate space admits a finite
piecewise-affine decomposition on that set. -/
theorem IsPLOn.isPiecewiseAffineOn_of_isCompact (hf : IsPLOn f s) (hs : IsCompact s) :
    IsPiecewiseAffineOn f s := by
  classical
  let _ := Fintype.ofFinite ι
  have hlocal (x : s) : ∃ (r : ℝ), 0 < r ∧ IsPiecewiseAffineOn f (s ∩ closedBall x.1 r) := by
    obtain ⟨V, hV, hpiece⟩ := isPLOn_iff.mp hf x.1 x.2
    obtain ⟨U, hU, hUV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hV
    obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp hU
    exact ⟨r, hr, hpiece.mono (fun y hy => hUV ⟨hball hy.2, hy.1⟩)⟩
  choose r hr hpiece using hlocal
  -- Restrict the cells to polyhedral closed balls before taking a finite subcover,
  -- ensuring that each selected formula remains valid wherever its cell meets the base.
  obtain ⟨t, ht⟩ := hs.elim_nhdsWithin_subcover'
    (fun x _ => closedBall x (r ⟨x, ‹x ∈ s›⟩))
    (fun x hx => nhdsWithin_le_nhds (closedBall_mem_nhds x (hr ⟨x, hx⟩)))
  choose n C A hC hcover heq using
    fun x : t => isPiecewiseAffineOn_iff.mp (hpiece x.1)
  refine isPiecewiseAffineOn_of_finite (ι := Σ x : t, Fin (n x))
    (C := fun p => C p.1 p.2 ∩ closedBall p.1.1.1 (r p.1.1))
    (A := fun p => A p.1 p.2)
    (fun p => (hC p.1 p.2).inter (isConvexPolyhedron_closedBall_pi _ (hr _).le)) ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (ht hy)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ⟨x, hx⟩ ⟨hy, hxy⟩)
    exact mem_iUnion.mpr ⟨⟨⟨x, hx⟩, j⟩, hj, hxy⟩
  · rintro ⟨x, j⟩ y ⟨hy, hyC, hyball⟩
    exact heq x j ⟨⟨hy, hyball⟩, hyC⟩

end TauCeti
