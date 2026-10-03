/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Between
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Segments in affine spaces

Two sides of a nondegenerate triangle meet only at their common vertex. This is the affine-space
form of Mathlib's `segment_inter_eq_endpoint_of_linearIndependent_sub`, with affine independence
of the three vertices in place of linear independence of the two edge vectors.
-/

public section

variable {R V P : Type*} [Field R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup V]
  [Module R V] [AddTorsor V P]

/-- Two sides of a nondegenerate triangle meet only at their common vertex. -/
theorem AffineIndependent.affineSegment_inter_eq_endpoint {a b c : P}
    (h : AffineIndependent R ![a, b, c]) : affineSegment R a b ∩ affineSegment R b c = {b} := by
  refine Set.Subset.antisymm (fun x ⟨hab, hbc⟩ => ?_) (Set.singleton_subset_iff.2
    ⟨right_mem_affineSegment R a b, left_mem_affineSegment R b c⟩)
  by_contra hxb
  -- `x ≠ b` lies on both lines `ab` and `bc`, so both are the line `xb`, which then contains
  -- all three vertices.
  have hxab : line[R, x, b] = line[R, a, b] :=
    affineSpan_pair_eq_of_left_mem_of_ne (Wbtw.mem_affineSpan hab) hxb
  have hxbc : line[R, b, x] = line[R, b, c] :=
    affineSpan_pair_eq_of_right_mem_of_ne (Wbtw.mem_affineSpan hbc) hxb
  rw [Set.pair_comm] at hxbc
  have ha : a ∈ line[R, x, b] := hxab ▸ left_mem_affineSpan_pair R a b
  have hc : c ∈ line[R, x, b] := hxbc ▸ right_mem_affineSpan_pair R b c
  exact (affineIndependent_iff_not_collinear_set.1 h)
    (collinear_triple_of_mem_affineSpan_pair ha (right_mem_affineSpan_pair R x b) hc)
