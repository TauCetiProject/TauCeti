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
-/

public section

variable {R V P : Type*} [Ring R] [PartialOrder R] [AddRightMono R] [ZeroLEOneClass R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- Two sides of a nondegenerate triangle meet only at their common vertex. -/
theorem AffineIndependent.affineSegment_inter_eq_endpoint {a b c : P}
    (h : AffineIndependent R ![a, b, c]) : affineSegment R a b ∩ affineSegment R b c = {b} := by
  -- Translate by `-b` and apply Mathlib's vector-space form, whose segments both start at `0`.
  have hli : LinearIndependent R ![a -ᵥ b - 0, c -ᵥ b - 0] := by
    convert ((affineIndependent_iff_linearIndependent_vsub R _ 1).1 h).comp
      ![⟨0, by decide⟩, ⟨2, by decide⟩] (by decide) using 1
    ext i
    fin_cases i <;> simp
  have hseg := segment_inter_eq_endpoint_of_linearIndependent_sub R hli
  rw [segment_symm, segment_eq_image_lineMap, segment_eq_image_lineMap] at hseg
  apply (vsub_left_injective b).image_injective
  rw [Set.image_inter (vsub_left_injective b), affineSegment_vsub_const_image,
    affineSegment_vsub_const_image, Set.image_singleton, vsub_self]
  exact hseg
