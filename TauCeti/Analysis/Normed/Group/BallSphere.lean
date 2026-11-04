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

A map lifting every vector of norm less than `r` to a vector of norm less than `r` lifts each `y`
to a vector of norm less than `‖y‖ + ε` (`TauCeti.exists_apply_eq_norm_lt_add`).

Under an injective map, the image of `v` lies outside the image of the closed ball of radius `r`
centred at zero exactly when `r < ‖v‖`
(`Function.Injective.apply_notMem_image_closedBall_zero_iff`).
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

/-- If `f` lifts every vector of norm less than `r` to a vector of norm less than `r`, then every
`y` is `f x` for some `x` with `‖x‖ < ‖y‖ + ε`, for each `ε > 0`. -/
theorem exists_apply_eq_norm_lt_add {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] {f : E → F} (hf : ∀ r, ball (0 : F) r ⊆ f '' ball 0 r) (y : F)
    {ε : ℝ} (hε : 0 < ε) : ∃ x, f x = y ∧ ‖x‖ < ‖y‖ + ε := by
  obtain ⟨x, hx, rfl⟩ := hf _ (mem_ball_zero_iff.2 (lt_add_of_pos_right ‖y‖ hε))
  exact ⟨x, rfl, mem_ball_zero_iff.1 hx⟩

/-- Under an injective map `e`, the image of `v` lies outside the image of the closed ball of
radius `r` centred at zero exactly when `r < ‖v‖`. -/
theorem _root_.Function.Injective.apply_notMem_image_closedBall_zero_iff {E X : Type*}
    [SeminormedAddGroup E] {e : E → X} (he : Function.Injective e) {r : ℝ} {v : E} :
    e v ∉ e '' closedBall 0 r ↔ r < ‖v‖ := by
  rw [he.mem_set_image, mem_closedBall_zero_iff, not_le]

end TauCeti
