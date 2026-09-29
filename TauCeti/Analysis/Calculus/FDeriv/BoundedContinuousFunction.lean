/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Topology.ContinuousMap.Bounded.Basic
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Differentiability of superposition operators on bounded continuous functions

Let `G : X → Y` be a Lipschitz map between normed spaces over `ℝ` or `ℂ`. Postcomposition with
`G` is the *superposition* (or *Nemytskii*) operator `f ↦ G ∘ f` on bounded continuous functions,
`BoundedContinuousFunction.comp G hG : (α →ᵇ X) → (α →ᵇ Y)`, for the sup norm. This file shows
that it is continuously differentiable wherever `G` is, in the following uniform sense.

Suppose that `G` has derivative `G' x` at every point `x` of a set `s`, that the derivative is a
bounded continuous function `G' : X →ᵇ (X →L[𝕜] Y)`, uniformly continuous on `s`, and that the
values of `f₀` stay a fixed distance `δ > 0` inside `s`. Then the superposition operator is
differentiable at `f₀`, and its derivative is pointwise application of the family of derivatives,
`h ↦ (t ↦ G' (f₀ t) (h t))`, that is `applyCLM (G'.compContinuous f₀.toContinuousMap)`. The
derivative is moreover strict, and the operator is `C¹` near `f₀`.

Uniform continuity of `G'` is what makes the remainder estimate hold with one constant at all
the points `f₀ t` at once; nothing makes the range of `f₀` compact, for instance for curves on
`[0, ∞)`. The distance `δ` allows `G` to be differentiable only on part of its domain, as when a
smooth map is cut off outside a ball by a merely Lipschitz retraction.

This is the differentiability input to the Lyapunov--Perron construction of stable manifolds.
Its integral operator acts on bounded continuous curves through the superposition by the
nonlinearity of the differential equation, and the implicit function theorem turns a `C¹`
operator into `C¹` dependence of its fixed points on parameters.

## Main declarations

* `BoundedContinuousFunction.hasFDerivAt_comp`: the superposition operator is differentiable at
  `f₀`, with derivative `h ↦ (t ↦ G' (f₀ t) (h t))`.
* `BoundedContinuousFunction.hasStrictFDerivAt_comp`: the derivative is strict.
* `BoundedContinuousFunction.contDiffAt_comp`: the superposition operator is `C¹` near `f₀`.
* `BoundedContinuousFunction.contDiff_comp`: when `G` is differentiable everywhere with a
  derivative uniformly continuous on bounded sets, the superposition operator is `C¹`.

## References

* J. Appell and P. P. Zabrejko, *Nonlinear Superposition Operators*, Cambridge Tracts in
  Mathematics **95**, Cambridge University Press, 1990.
-/

public section

open Filter Metric Set Topology
open scoped NNReal BoundedContinuousFunction

namespace BoundedContinuousFunction

variable {α 𝕜 X Y : Type*} [TopologicalSpace α] [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {G : X → Y} {C : ℝ≥0} {G' : X →ᵇ (X →L[𝕜] Y)} {s : Set X} {f₀ : α →ᵇ X} {δ : ℝ}

/-- If the values of `f₀` stay `δ > 0` inside `s`, then so do the values of every function
uniformly within `δ / 2` of `f₀`, with the margin `δ / 2`. -/
private theorem ball_half_subset_of_mem_ball {f : α →ᵇ X} (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hf : f ∈ ball f₀ (δ / 2)) (t : α) : ball (f t) (δ / 2) ⊆ s :=
  (ball_subset_ball' (by linarith [dist_coe_le_dist (f := f) (g := f₀) t, mem_ball.1 hf])).trans
    (hf₀ t)

/-- The derivative `f ↦ (h ↦ (t ↦ G' (f t) (h t)))` of the superposition operator is continuous at
every function whose values stay a positive distance inside a set where `G'` is uniformly
continuous. -/
private theorem continuousAt_applyCLM_compContinuous (hG' : UniformContinuousOn G' s)
    (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) :
    ContinuousAt (fun f : α →ᵇ X ↦ applyCLM (G'.compContinuous f.toContinuousMap)) f₀ :=
  applyCLM.continuous.continuousAt.comp <|
    (uniformContinuousOn_compContinuous_left G' hG').continuousOn.continuousAt <|
      mem_of_superset (ball_mem_nhds f₀ hδ) fun _ hf t ↦
        hf₀ t <| mem_ball.2 <| (dist_coe_le_dist t).trans_lt hf

/-- **The derivative of a superposition operator.** Let `G` be Lipschitz, with derivative `G' x`
at every point `x` of `s`, where `G'` is bounded continuous and uniformly continuous on `s`. If the
values of `f₀` stay a distance `δ > 0` inside `s`, then `f ↦ G ∘ f` is differentiable at `f₀` for
the sup norm, with derivative `h ↦ (t ↦ G' (f₀ t) (h t))`. -/
theorem hasFDerivAt_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) :
    HasFDerivAt (comp G hG) (applyCLM (G'.compContinuous f₀.toContinuousMap)) f₀ := by
  let _ : NormedSpace ℝ X := .restrictScalars ℝ 𝕜 X
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- A modulus of continuity `η` for `G'` at the tolerance `c` controls the remainder of `G` at
  -- every point `f₀ t` simultaneously, on the ball of radius `min δ η`.
  obtain ⟨η, hη, hG'η⟩ := Metric.uniformContinuousOn_iff_le.1 hG' c hc
  have hρ : 0 < min δ η := lt_min hδ hη
  filter_upwards [ball_mem_nhds (0 : α →ᵇ X) hρ] with h hh
  rw [mem_ball_zero_iff] at hh
  refine (norm_le (by positivity)).2 fun t ↦ ?_
  have hball : ball (f₀ t) (min δ η) ⊆ s := (ball_subset_ball (min_le_left _ _)).trans (hf₀ t)
  have hmem : f₀ t + h t ∈ ball (f₀ t) (min δ η) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (norm_coe_le_norm h t).trans_lt hh
  have key := (convex_ball (f₀ t) (min δ η)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx ↦ (hGs x (hball hx)).hasFDerivWithinAt)
    (fun x hx ↦ by
      rw [← dist_eq_norm]
      exact hG'η x (hball hx) (f₀ t) (hf₀ t (mem_ball_self hδ))
        ((mem_ball.1 hx).le.trans (min_le_right _ _)))
    (mem_ball_self hρ) hmem
  rw [add_sub_cancel_left] at key
  simpa using key.trans (mul_le_mul_of_nonneg_left (norm_coe_le_norm h t) hc.le)

/-- **Strict differentiability of a superposition operator.** Under the hypotheses of
`BoundedContinuousFunction.hasFDerivAt_comp`, the derivative
`h ↦ (t ↦ G' (f₀ t) (h t))` of `f ↦ G ∘ f` at `f₀` is strict. -/
theorem hasStrictFDerivAt_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) :
    HasStrictFDerivAt (comp G hG) (applyCLM (G'.compContinuous f₀.toContinuousMap)) f₀ :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (f' := fun f : α →ᵇ X ↦ applyCLM (G'.compContinuous f.toContinuousMap))
    (mem_of_superset (ball_mem_nhds f₀ (half_pos hδ)) fun _ hf ↦
      hasFDerivAt_comp hG hGs hG' (half_pos hδ) (ball_half_subset_of_mem_ball hf₀ hf))
    (continuousAt_applyCLM_compContinuous hG' hδ hf₀)

/-- **A superposition operator is `C¹`.** Under the hypotheses of
`BoundedContinuousFunction.hasFDerivAt_comp`, the map `f ↦ G ∘ f` is continuously differentiable
at `f₀`. -/
theorem contDiffAt_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) :
    ContDiffAt 𝕜 1 (comp G hG) f₀ := by
  refine contDiffAt_one_iff.2 ⟨fun f : α →ᵇ X ↦ applyCLM (G'.compContinuous f.toContinuousMap),
    ball f₀ (δ / 2), ball_mem_nhds f₀ (half_pos hδ), fun f hf ↦ ?_, fun f hf ↦ ?_⟩
  · exact (continuousAt_applyCLM_compContinuous hG' (half_pos hδ)
      (ball_half_subset_of_mem_ball hf₀ hf)).continuousWithinAt
  · exact hasFDerivAt_comp hG hGs hG' (half_pos hδ) (ball_half_subset_of_mem_ball hf₀ hf)

/-- **A superposition operator is `C¹`, global form.** If `G` is Lipschitz and differentiable
everywhere, with a bounded continuous derivative `G'` that is uniformly continuous on every ball
about `0`, then `f ↦ G ∘ f` is continuously differentiable on the bounded continuous functions.
Since each bounded continuous `f₀` takes values in a ball, uniform continuity of `G'` on bounded
sets suffices; it holds for instance when `X` is finite-dimensional. -/
theorem contDiff_comp (hG : LipschitzWith C G) (hGs : ∀ x, HasFDerivAt G (G' x) x)
    (hG' : ∀ r, UniformContinuousOn G' (ball 0 r)) :
    ContDiff 𝕜 1 (comp G hG : (α →ᵇ X) → α →ᵇ Y) :=
  contDiff_iff_contDiffAt.2 fun f₀ ↦
    contDiffAt_comp hG (fun x _ ↦ hGs x) (hG' (‖f₀‖ + 1)) one_pos fun t ↦
      ball_subset_ball' <| by rw [dist_zero_right]; linarith [norm_coe_le_norm f₀ t]

end BoundedContinuousFunction
