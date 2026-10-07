/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Between

/-!
# Segments in affine spaces

Two sides of a nondegenerate triangle meet only at their common vertex. This is the affine-space
form of Mathlib's `segment_inter_eq_endpoint_of_linearIndependent_sub`, with affine independence
of the three vertices in place of linear independence of the two edge vectors.

Conversely, over a linearly ordered field, if the segments from `z` to `a` and to `b` meet only at
`z`, then the directions `a -ᵥ z` and `b -ᵥ z` are nonzero and do not lie on a common ray from the
origin: `0 ∉ [-(a -ᵥ z), b -ᵥ z]`. This is the form in which a separating functional can be
found for the two directions (`TauCeti.exists_strongDual_neg_pos_ne_zero`).

## Main results

* `AffineIndependent.affineSegment_inter_eq_endpoint`: two sides of a nondegenerate triangle meet
  only at their common vertex.
* `TauCeti.zero_notMem_segment_of_affineSegment_inter_eq`: two segments from `z` meeting only at
  `z` point in directions not on a common ray.
-/

public section

variable {R V P : Type*} [Ring R] [PartialOrder R] [ZeroLEOneClass R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- Two sides of a nondegenerate triangle meet only at their common vertex. -/
theorem AffineIndependent.affineSegment_inter_eq_endpoint {a b c : P}
    (h : AffineIndependent R ![a, b, c]) : affineSegment R a b ∩ affineSegment R b c = {b} := by
  have hli : LinearIndependent R ![a -ᵥ b, c -ᵥ b] := by
    convert ((affineIndependent_iff_linearIndependent_vsub R _ 1).1 h).comp
      ![⟨0, by decide⟩, ⟨2, by decide⟩] (by decide) using 1
    ext i
    fin_cases i <;> simp
  -- Mathlib's `segment_inter_eq_endpoint_of_linearIndependent_sub` would need `AddRightMono R` to
  -- identify `segment` with `affineSegment`, so we argue with the line-map parameters directly.
  refine Set.Subset.antisymm ?_ <| Set.singleton_subset_iff.2
    ⟨⟨1, ⟨zero_le_one, le_rfl⟩, AffineMap.lineMap_apply_one a b⟩,
      ⟨0, ⟨le_rfl, zero_le_one⟩, AffineMap.lineMap_apply_zero b c⟩⟩
  rintro x ⟨⟨s, -, rfl⟩, ⟨t, -, ht⟩⟩
  -- Measured from `b`, the point is `(1 - s) • (a -ᵥ b) = t • (c -ᵥ b)`, so `t = 0`.
  have hst := congrArg (· -ᵥ b) ht
  simp only [AffineMap.lineMap_vsub_right, AffineMap.lineMap_vsub_left] at hst
  obtain ⟨-, h0⟩ := LinearIndependent.pair_iff.1 hli (1 - s) (-t) (by
    rw [neg_smul, ← sub_eq_add_neg, hst, sub_self])
  rw [← ht, neg_eq_zero.1 h0, AffineMap.lineMap_apply_zero]
  rfl

namespace TauCeti

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [Module k V]

/-- If the segments from `z` to `a` and to `b` meet only at `z`, then `a -ᵥ z` and `b -ᵥ z` are
nonzero and do not lie on a common ray from `0`: `0 ∉ [-(a -ᵥ z), b -ᵥ z]`. -/
theorem zero_notMem_segment_of_affineSegment_inter_eq {a b z : P} (ha : a ≠ z) (hb : b ≠ z)
    (hab : affineSegment k z a ∩ affineSegment k z b = {z}) :
    (0 : V) ∉ segment k (-(a -ᵥ z)) (b -ᵥ z) := by
  rintro ⟨s, t, hs, ht, hst, he⟩
  rw [smul_neg, neg_add_eq_zero] at he
  have hm : t • (b -ᵥ z) +ᵥ z ∈ affineSegment k z a ∩ affineSegment k z b :=
    ⟨⟨s, ⟨hs, by linarith⟩, by rw [AffineMap.lineMap_apply, he]⟩,
      ⟨t, ⟨ht, by linarith⟩, by rw [AffineMap.lineMap_apply]⟩⟩
  rw [hab, Set.mem_singleton_iff, ← vsub_eq_zero_iff_eq, vadd_vsub, smul_eq_zero] at hm
  rcases hm with rfl | hm
  · rw [zero_smul, smul_eq_zero] at he
    rcases he with rfl | he
    · linarith
    · exact ha (vsub_eq_zero_iff_eq.1 he)
  · exact hb (vsub_eq_zero_iff_eq.1 hm)

end TauCeti
