/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Differentiability of superposition operators on bounded continuous functions

Let `G : X → Y` be a Lipschitz map between normed spaces over `ℝ` or `ℂ`. Postcomposition with
`G` is the *superposition* (or *Nemytskii*) operator `f ↦ G ∘ f` on bounded continuous functions,
`BoundedContinuousFunction.comp G hG : (α →ᵇ X) → (α →ᵇ Y)`, for the sup norm. This file shows
that it is continuously differentiable wherever `G` is, in the following uniform sense.

Suppose that `G` has derivative `G' x` at every point `x` of a set `s`, that
`G' : X → (X →L[𝕜] Y)` is uniformly continuous on `s`, and that the values of `f₀` stay a fixed
distance `δ > 0` inside `s`. Nothing is assumed about `G'` off `s`. Then the superposition
operator is differentiable at `f₀`, and its derivative is pointwise application of the family of
derivatives, `h ↦ (t ↦ G' (f₀ t) (h t))`, that is `applyCLM Φ` for the bounded continuous family
`Φ t = G' (f₀ t)`; the Lipschitz constant of `G` bounds `G'` on `s`, so this family is bounded.
The derivative is moreover strict, and the operator is `C¹` near `f₀`.

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
  {G : X → Y} {C : ℝ≥0} {G' : X → X →L[𝕜] Y} {s : Set X} {f₀ : α →ᵇ X} {δ : ℝ}
  {Φ : α →ᵇ (X →L[𝕜] Y)}

/-- If the values of `f₀` stay `δ > 0` inside `s`, then so do the values of every function
uniformly within `δ / 2` of `f₀`, with the margin `δ / 2`. -/
private theorem ball_half_subset_of_mem_ball {f : α →ᵇ X} (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hf : f ∈ ball f₀ (δ / 2)) (t : α) : ball (f t) (δ / 2) ⊆ s :=
  (ball_subset_ball' (by linarith [dist_coe_le_dist (f := f) (g := f₀) t, mem_ball.1 hf])).trans
    (hf₀ t)

/-- Along a function `f` with values in `s`, the derivatives `t ↦ G' (f t)` form a bounded
continuous family: they are bounded by the Lipschitz constant of `G`. -/
private theorem exists_eq_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) {f : α →ᵇ X} (hf : ∀ t, f t ∈ s) :
    ∃ Φ : α →ᵇ (X →L[𝕜] Y), ∀ t, Φ t = G' (f t) :=
  ⟨ofNormedAddCommGroup (fun t ↦ G' (f t)) (hG'.continuousOn.comp_continuous f.continuous hf) C
    fun t ↦ (hGs _ (hf t)).le_of_lipschitz hG, fun _ ↦ rfl⟩

/-- **The derivative of a superposition operator.** Let `G` be Lipschitz, with derivative `G' x`
at every point `x` of `s`, where `G'` is uniformly continuous on `s`. If the values of `f₀` stay a
distance `δ > 0` inside `s`, then `f ↦ G ∘ f` is differentiable at `f₀` for the sup norm, with
derivative `h ↦ (t ↦ G' (f₀ t) (h t))`, that is `applyCLM Φ` for the bounded continuous family
`Φ t = G' (f₀ t)`. -/
theorem hasFDerivAt_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hΦ : ∀ t, Φ t = G' (f₀ t)) : HasFDerivAt (comp G hG) (applyCLM Φ) f₀ := by
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
  simpa [hΦ] using key.trans (mul_le_mul_of_nonneg_left (norm_coe_le_norm h t) hc.le)

/-- The superposition operator is differentiable at every function whose values stay a positive
distance inside `s`. -/
private theorem hasFDerivAt_fderiv_comp (hG : LipschitzWith C G)
    (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x) (hG' : UniformContinuousOn G' s) (hδ : 0 < δ)
    (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) : HasFDerivAt (comp G hG) (fderiv 𝕜 (comp G hG) f₀) f₀ :=
  have ⟨_, hΦ⟩ := exists_eq_comp hG hGs hG' fun t ↦ hf₀ t (mem_ball_self hδ)
  (hasFDerivAt_comp hG hGs hG' hδ hf₀ hΦ).differentiableAt.hasFDerivAt

/-- The derivative of the superposition operator is continuous at every function whose values
stay a positive distance inside a set where `G'` is uniformly continuous. -/
private theorem continuousAt_fderiv_comp (hG : LipschitzWith C G)
    (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x) (hG' : UniformContinuousOn G' s) (hδ : 0 < δ)
    (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) : ContinuousAt (fderiv 𝕜 (comp G hG)) f₀ := by
  refine Metric.continuousAt_iff (β := (α →ᵇ X) →L[𝕜] α →ᵇ Y) |>.2 fun ε hε ↦ ?_
  obtain ⟨η, hη, hG'η⟩ := Metric.uniformContinuousOn_iff_le.1 hG' (ε / 2) (half_pos hε)
  refine ⟨min (δ / 2) η, lt_min (half_pos hδ) hη, fun f hf ↦ ?_⟩
  have hfδ : f ∈ ball f₀ (δ / 2) := mem_ball.2 (hf.trans_le (min_le_left _ _))
  have hfs := ball_half_subset_of_mem_ball hf₀ hfδ
  obtain ⟨Φ, hΦ⟩ := exists_eq_comp hG hGs hG' fun t ↦ hfs t (mem_ball_self (half_pos hδ))
  obtain ⟨Φ₀, hΦ₀⟩ := exists_eq_comp hG hGs hG' fun t ↦ hf₀ t (mem_ball_self hδ)
  rw [(hasFDerivAt_comp hG hGs hG' (half_pos hδ) hfs hΦ).fderiv,
    (hasFDerivAt_comp hG hGs hG' hδ hf₀ hΦ₀).fderiv, dist_eq_norm, ← map_sub]
  refine ((norm_applyCLM_apply_le _).trans ?_).trans_lt (half_lt_self hε)
  refine (norm_le (half_pos hε).le).2 fun t ↦ ?_
  rw [coe_sub, Pi.sub_apply, hΦ, hΦ₀, ← dist_eq_norm]
  exact hG'η _ (hfs t (mem_ball_self (half_pos hδ))) _ (hf₀ t (mem_ball_self hδ))
    ((dist_coe_le_dist t).trans (hf.le.trans (min_le_right _ _)))

/-- **Strict differentiability of a superposition operator.** Under the hypotheses of
`BoundedContinuousFunction.hasFDerivAt_comp`, the derivative
`h ↦ (t ↦ G' (f₀ t) (h t))` of `f ↦ G ∘ f` at `f₀` is strict. -/
theorem hasStrictFDerivAt_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hΦ : ∀ t, Φ t = G' (f₀ t)) : HasStrictFDerivAt (comp G hG) (applyCLM Φ) f₀ := by
  rw [← (hasFDerivAt_comp hG hGs hG' hδ hf₀ hΦ).fderiv]
  exact hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (mem_of_superset (ball_mem_nhds f₀ (half_pos hδ)) fun _ hf ↦
      hasFDerivAt_fderiv_comp hG hGs hG' (half_pos hδ) (ball_half_subset_of_mem_ball hf₀ hf))
    (continuousAt_fderiv_comp hG hGs hG' hδ hf₀)

/-- **A superposition operator is `C¹`.** Let `G` be Lipschitz, with derivative `G' x` at every
point `x` of `s`, where `G'` is uniformly continuous on `s`. If the values of `f₀` stay a distance
`δ > 0` inside `s`, then the map `f ↦ G ∘ f` is continuously differentiable at `f₀`. -/
theorem contDiffAt_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) :
    ContDiffAt 𝕜 1 (comp G hG) f₀ := by
  refine contDiffAt_one_iff.2 ⟨fderiv 𝕜 (comp G hG), ball f₀ (δ / 2),
    ball_mem_nhds f₀ (half_pos hδ), fun f hf ↦ ?_, fun f hf ↦ ?_⟩
  · exact (continuousAt_fderiv_comp hG hGs hG' (half_pos hδ)
      (ball_half_subset_of_mem_ball hf₀ hf)).continuousWithinAt
  · exact hasFDerivAt_fderiv_comp hG hGs hG' (half_pos hδ) (ball_half_subset_of_mem_ball hf₀ hf)

/-- **A superposition operator is `C¹`, global form.** If `G` is Lipschitz and differentiable
everywhere, with a derivative `G'` that is uniformly continuous on every ball about `0`, then
`f ↦ G ∘ f` is continuously differentiable on the bounded continuous functions. Since each
bounded continuous `f₀` takes values in a ball, uniform continuity of `G'` on bounded sets
suffices; it holds for instance when `X` is finite-dimensional and `G'` is continuous. -/
theorem contDiff_comp (hG : LipschitzWith C G) (hGs : ∀ x, HasFDerivAt G (G' x) x)
    (hG' : ∀ r, UniformContinuousOn G' (ball 0 r)) :
    ContDiff 𝕜 1 (comp G hG : (α →ᵇ X) → α →ᵇ Y) :=
  contDiff_iff_contDiffAt.2 fun f₀ ↦
    contDiffAt_comp hG (fun x _ ↦ hGs x) (hG' (‖f₀‖ + 1)) one_pos fun t ↦
      ball_subset_ball' <| by rw [dist_zero_right]; linarith [norm_coe_le_norm f₀ t]

end BoundedContinuousFunction
