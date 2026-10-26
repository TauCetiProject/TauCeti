/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.BallSphere

/-!
# Antipodal covers of spheres

On a sphere of nonzero radius in a torsion-free seminormed additive group, a point and its
antipode are distinct. Their complements therefore cover the sphere. This cover is useful for
decomposing spheres into punctured spheres.
-/

public section

open Metric

namespace TauCeti

/-- The complements of two antipodal points cover any sphere of nonzero radius in a torsion-free
seminormed additive group. -/
lemma compl_singleton_union_compl_singleton_neg {E : Type*} [SeminormedAddCommGroup E]
    [IsAddTorsionFree E] {r : ℝ} (hr : r ≠ 0) (p : sphere (0 : E) r) :
    ({p}ᶜ ∪ {-p}ᶜ : Set (sphere (0 : E) r)) = Set.univ := by
  rw [← Set.compl_inter, Set.singleton_inter_of_notMem]
  · exact Set.compl_empty
  · intro h
    apply ne_zero_of_mem_sphere hr p
    apply self_eq_neg.mp
    simpa only [coe_neg_sphere] using congrArg Subtype.val h

end TauCeti
