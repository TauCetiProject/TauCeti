/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Proper affine spans from dimension bounds

Adding one or two points to an affine subspace preserves properness when its
codimension exceeds the number of added points. The ambient affine space is over
an arbitrary division ring; no topology is needed.

Adapted from `Mei/Geometry/Affine/Generic.lean` at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
Source: https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/Geometry/Affine/Generic.lean
-/

public section

open Set
open scoped Affine

namespace AffineSubspace

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- Adding one point to a subspace of codimension at least two still gives a
proper affine subspace. -/
theorem affineSpan_insert_ne_top_of_finrank (S : AffineSubspace k P)
    (hS : Module.finrank k S.direction + 1 < Module.finrank k V) (x : P) :
    affineSpan k (insert x (S : Set P)) ≠ ⊤ := by
  intro htop
  have hle := finrank_vectorSpan_insert_le S x
  rw [← direction_affineSpan, htop, direction_top, finrank_top] at hle
  exact (not_le_of_gt hS) hle

/-- Adjoining two points to a subspace of codimension at least three leaves
a proper affine subspace. The two points need not be distinct. -/
theorem affineSpan_pair_union_ne_top_of_finrank (S : AffineSubspace k P)
    (hS : Module.finrank k S.direction + 2 < Module.finrank k V) (x y : P) :
    affineSpan k ({x, y} ∪ (S : Set P)) ≠ ⊤ := by
  have hfirst := finrank_vectorSpan_insert_le S y
  have hsecond := finrank_vectorSpan_insert_le_set k (insert y (S : Set P)) x
  intro he
  have he' : affineSpan k (insert x (insert y (S : Set P))) = ⊤ := by
    simpa only [insert_union, singleton_union] using he
  rw [← direction_affineSpan, he', direction_top, finrank_top] at hsecond
  omega

end AffineSubspace
