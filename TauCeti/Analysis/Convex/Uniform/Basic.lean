/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Module.Dual.Goldstine

/-!
# The Milman–Pettis theorem

The **Milman–Pettis theorem** says that every uniformly convex Banach space is reflexive: the
canonical map `NormedSpace.inclusionInDoubleDual ℝ E` into the continuous bidual is surjective.

Without any completeness assumption, every point `φ` of the bidual of a uniformly convex space
lies within any prescribed `ε > 0` of the canonical image of a point of norm at most `‖φ‖`, so
the canonical image is norm dense in the bidual. For a Banach space this image is also norm
closed, because the canonical map is an isometry, and so the canonical map is onto.

Uniform convexity passes to every subspace with the induced norm, so the Milman–Pettis theorem
applies to every closed subspace of a uniformly convex Banach space.

## Main results

* `StrongDual.exists_norm_le_norm_sub_inclusionInDoubleDual_le_of_uniformConvexSpace`: the
  quantitative approximation of a bidual point by the canonical image.
* `TauCeti.denseRange_inclusionInDoubleDual_of_uniformConvexSpace`: the canonical image of a
  uniformly convex space is norm dense in its bidual.
* `TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace`: the Milman–Pettis theorem.
* `Submodule.uniformConvexSpace`: a subspace of a uniformly convex space is uniformly convex.

## Implementation notes

The density statement follows Ringrose's argument from Goldstine's theorem
(`NormedSpace.closure_image_inclusionInDoubleDualWeak_closedBall`): on a weak-star open slice
where `φ` is large on a nearly norming functional, uniform convexity confines the canonical image
of a ball to a norm ball of radius `ε`, which is weak-star closed.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, Theorem 5.2.15.
* J. R. Ringrose, *A note on uniformly convex spaces*, J. London Math. Soc. 34 (1959), 92.
-/

public section

open Function Metric NormedSpace Set

namespace Submodule

variable {R E : Type*} [Ring R] [SeminormedAddCommGroup E] [Module R E] [UniformConvexSpace E]

/-- A subspace of a uniformly convex space, with the induced norm, is uniformly convex. -/
instance uniformConvexSpace (s : Submodule R E) : UniformConvexSpace s where
  uniform_convex ε hε := by
    obtain ⟨δ, hδ, h⟩ := exists_forall_sphere_dist_add_le_two_sub E hε
    refine ⟨δ, hδ, fun x hx y hy hxy ↦ ?_⟩
    rw [← norm_coe] at hx hy hxy ⊢
    push_cast at hxy ⊢
    exact h hx hy hxy

end Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

namespace StrongDual

/-- In a uniformly convex space, every point `φ` of the bidual lies within any prescribed `ε > 0`
of the canonical image of a point of norm at most `‖φ‖`. No completeness is assumed. -/
theorem exists_norm_le_norm_sub_inclusionInDoubleDual_le_of_uniformConvexSpace
    (φ : StrongDual ℝ (StrongDual ℝ E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ ≤ ‖φ‖ ∧ ‖φ - inclusionInDoubleDual ℝ E x‖ ≤ ε := by
  set r := ‖φ‖
  obtain ⟨δ, hδ, hconv⟩ := exists_forall_closed_ball_dist_add_le_two_mul_sub E hε r
  -- A functional of norm at most one on which `φ` is larger than `r - δ / 2`.
  obtain ⟨f, hf, hφf⟩ : ∃ f : StrongDual ℝ E, ‖f‖ ≤ 1 ∧ r - δ / 2 < φ f := by
    obtain ⟨f, hf, hφf⟩ := ContinuousLinearMap.exists_lt_apply_of_lt_opNorm φ
      (sub_lt_self r (half_pos hδ))
    rcases lt_abs.1 hφf with h | h
    · exact ⟨f, hf.le, h⟩
    · exact ⟨-f, by rw [norm_neg]; exact hf.le, by rwa [map_neg]⟩
  -- Any two points of `closedBall 0 r` on which `f` exceeds `r - δ / 2` are `ε`-close.
  have hclose : ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      r - δ / 2 < f x → r - δ / 2 < f y → ‖y - x‖ < ε := by
    intro x hx y hy hfx hfy
    rw [mem_closedBall_zero_iff] at hx hy
    rw [norm_sub_rev]
    by_contra! hxy
    have hsum : f (x + y) ≤ ‖x + y‖ :=
      (Real.le_norm_self _).trans ((f.le_of_opNorm_le hf _).trans_eq (one_mul _))
    rw [map_add] at hsum
    linarith [hconv hx hy hxy]
  -- The weak-star open slice of the bidual where evaluation at `f` exceeds `r - δ / 2`.
  have heval (y : E) : inclusionInDoubleDualWeak ℝ E (toWeakSpace ℝ E y) f = f y := by
    rw [inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
      StrongDual.toWeakDual_apply, dual_def]
  set U : Set (WeakDual ℝ (StrongDual ℝ E)) := {ψ | r - δ / 2 < ψ f}
  have hU : IsOpen U := isOpen_lt continuous_const (WeakDual.eval_continuous f)
  set B := inclusionInDoubleDualWeak ℝ E '' (toWeakSpace ℝ E '' closedBall 0 r)
  have hφB : StrongDual.toWeakDual φ ∈ U ∩ closure B := by
    refine ⟨hφf, ?_⟩
    rw [closure_image_inclusionInDoubleDualWeak_closedBall, map_zero, mem_preimage,
      StrongDual.toStrongDual_toWeakDual]
    exact (mem_closedBall_zero_iff (E := StrongDual ℝ (StrongDual ℝ E))).2 le_rfl
  -- By Goldstine's theorem the slice meets the image of the ball, say at the image of `x`.
  obtain ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, hxU⟩ :=
    (closure_inter_open_nonempty_iff (s := B) hU).1 ⟨_, hφB.2, hφB.1⟩
  have hfx : r - δ / 2 < f x := heval x ▸ hxU
  refine ⟨x, mem_closedBall_zero_iff.1 hx, ?_⟩
  -- The slice of the image lies in the weak-star closed ball of radius `ε` about the image of `x`.
  have hsub : U ∩ B ⊆ WeakDual.toStrongDual ⁻¹' closedBall (inclusionInDoubleDual ℝ E x) ε := by
    rintro _ ⟨hyU, _, ⟨y, hy, rfl⟩, rfl⟩
    have hfy : r - δ / 2 < f y := heval y ▸ hyU
    -- The bidual's metric is not reducibly the one of its normed group, so name the type.
    rw [mem_preimage, inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
      StrongDual.toStrongDual_toWeakDual,
      mem_closedBall_iff_norm (E := StrongDual ℝ (StrongDual ℝ E)),
      ← map_sub (inclusionInDoubleDual ℝ E) y x]
    exact ((double_dual_bound ℝ E _).trans_lt (hclose x hx y hy hfx hfy)).le
  have hφ := closure_minimal hsub (WeakDual.isClosed_closedBall _ _) (hU.inter_closure hφB)
  rwa [mem_preimage, StrongDual.toStrongDual_toWeakDual,
    mem_closedBall_iff_norm (E := StrongDual ℝ (StrongDual ℝ E))] at hφ

end StrongDual

namespace TauCeti

/-- The canonical image of a uniformly convex space is norm dense in its bidual. -/
theorem denseRange_inclusionInDoubleDual_of_uniformConvexSpace :
    DenseRange (inclusionInDoubleDual ℝ E) := by
  refine Metric.denseRange_iff (f := inclusionInDoubleDual ℝ E) |>.2 fun φ ε hε ↦ ?_
  obtain ⟨x, -, hx⟩ :=
    φ.exists_norm_le_norm_sub_inclusionInDoubleDual_le_of_uniformConvexSpace (half_pos hε)
  exact ⟨x, by rw [dist_eq_norm (E := StrongDual ℝ (StrongDual ℝ E))]; linarith⟩

/-- **Milman–Pettis theorem.** A uniformly convex Banach space is reflexive: its canonical map
into the continuous bidual is surjective. -/
theorem surjective_inclusionInDoubleDual_of_uniformConvexSpace [CompleteSpace E] :
    Surjective (inclusionInDoubleDual ℝ E) := by
  have hclosed : IsClosed (range (inclusionInDoubleDual ℝ E)) :=
    (inclusionInDoubleDualLi ℝ (E := E)).isometry.isUniformInducing.isComplete_range.isClosed
  rw [← range_eq_univ, ← hclosed.closure_eq]
  exact denseRange_inclusionInDoubleDual_of_uniformConvexSpace.closure_range

end TauCeti
