/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.BallSphere

/-!
# Spheres and open subsets of closed balls

On a sphere of nonzero radius in a torsion-free seminormed additive group, a point and its
antipode are distinct. Their complements therefore cover the sphere. This cover is useful for
decomposing spheres into punctured spheres.

An open subset of a closed ball contained in the corresponding open ball embeds openly into the
ambient space.
-/

public section

open Metric Set Topology

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

/-- An open subset of a closed ball centered at zero whose points have norm strictly less than
the radius embeds openly into the ambient space. -/
theorem _root_.IsOpen.isOpenEmbedding_coe_openSubset_closedBall
    {E : Type*} [SeminormedAddCommGroup E]
    {r : ℝ} {U : Set (closedBall (0 : E) r)} (hU : IsOpen U)
    (h : ∀ z ∈ U, ‖(z : E)‖ < r) :
    IsOpenEmbedding fun z : U => ((z : closedBall (0 : E) r) : E) := by
  refine ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal, ?_⟩
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hU
  have hrange : range (fun z : (Subtype.val ⁻¹' O : Set (closedBall (0 : E) r)) =>
      ((z : closedBall (0 : E) r) : E)) = O ∩ ball 0 r := by
    ext v
    refine ⟨?_, fun hv => ⟨⟨⟨v, ball_subset_closedBall hv.2⟩, hv.1⟩, rfl⟩⟩
    rintro ⟨z, rfl⟩
    exact ⟨z.2, mem_ball_zero_iff.2 (h z z.2)⟩
  rw [hrange]
  exact hO.inter isOpen_ball

end TauCeti
