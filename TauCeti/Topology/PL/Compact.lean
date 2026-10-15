/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map
public import TauCeti.Analysis.Convex.Polyhedron.Pi.Neighborhood
import Mathlib.Topology.Compactness.Compact

/-!
# Finite PL decompositions on compact sets

A PL map on a compact subset of a real coordinate product admits a finite
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

variable {ι : Type*}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {s : Set (ι → ℝ)} {f : (ι → ℝ) → F}

/-- A PL map on a compact subset of a real coordinate product admits a finite
piecewise-affine decomposition on that set. -/
theorem IsPLOn.isPiecewiseAffineOn_of_isCompact (hf : IsPLOn f s) (hs : IsCompact s) :
    IsPiecewiseAffineOn f s := by
  classical
  have hlocal (x : s) : ∃ C ∈ 𝓝 x.1, IsConvexPolyhedron C ∧
      IsPiecewiseAffineOn f (s ∩ C) := by
    obtain ⟨V, hV, hpiece⟩ := isPLOn_iff.mp hf x.1 x.2
    obtain ⟨U, hU, hUV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hV
    obtain ⟨C, hC, hpoly, hCU⟩ := exists_isConvexPolyhedron_mem_nhds_pi hU
    exact ⟨C, hC, hpoly, hpiece.mono (fun y hy => hUV ⟨hCU hy.2, hy.1⟩)⟩
  choose C hC hpoly hpiece using hlocal
  -- Cutting each local decomposition by a polyhedral neighbourhood keeps its affine
  -- formulas valid on the whole selected cell, including overlaps in the finite subcover.
  obtain ⟨t, ht⟩ := hs.elim_nhdsWithin_subcover'
    (fun x hx => C ⟨x, hx⟩) (fun x hx => nhdsWithin_le_nhds (hC ⟨x, hx⟩))
  choose n D A hD hcover heq using
    fun x : t => isPiecewiseAffineOn_iff.mp (hpiece x.1)
  refine isPiecewiseAffineOn_of_finite (ι := Σ x : t, Fin (n x))
    (C := fun p => D p.1 p.2 ∩ C p.1.1)
    (A := fun p => A p.1 p.2)
    (fun p => (hD p.1 p.2).inter (hpoly p.1.1)) ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (ht hy)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ⟨x, hx⟩ ⟨hy, hxy⟩)
    exact mem_iUnion.mpr ⟨⟨⟨x, hx⟩, j⟩, hj, hxy⟩
  · rintro ⟨x, j⟩ y ⟨hy, hyC, hyCneigh⟩
    exact heq x j ⟨⟨hy, hyCneigh⟩, hyC⟩

end TauCeti
