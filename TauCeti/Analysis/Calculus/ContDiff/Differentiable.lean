/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Differentiability of `C^n` maps

Because `ContDiffWithinAt 𝕜 1 f s x` propagates to a `𝓝[insert x s] x`-neighborhood
(`ContDiffWithinAt.eventually`) and implies `DifferentiableWithinAt`, any map that is `C^n` at (or
within `s` at) `x` with `1 ≤ n` is differentiable near `x`. Lowering to order `1` first avoids the
`n ≠ ∞` restriction of `ContDiffAt.eventually`, so both `n = ∞` and `n = ω` are covered. On an
open set, the iterated derivatives of order `m < n` of a `C^n` map are differentiable.

Conversely, strict differentiability everywhere gives `C¹`: if `f` has strict derivative `f' x₀`
at `x₀`, then `f - f' x₀` is `ε`-Lipschitz near `x₀` for every `ε > 0`, so its derivative
`f' x - f' x₀` at every nearby point `x` has norm at most `ε`. Over `ℝ` or `ℂ`, a `C¹` map is
strictly differentiable everywhere (`ContDiffAt.hasStrictFDerivAt`), so for these fields the two
notions agree.

## Main declarations

* `ContDiffWithinAt.eventually_differentiableWithinAt`: `C^n` within `s` at `x` (`1 ≤ n`) implies
  `DifferentiableWithinAt` eventually in `𝓝[insert x s] x`.
* `ContDiffAt.eventually_differentiableAt`: `C^n` at `x` (`1 ≤ n`) implies `DifferentiableAt`
  eventually in `𝓝 x`.
* `ContDiffAt.differentiableAt_deriv_two`: the derivative of a function of one variable that is
  `C²` at `x` is differentiable at `x`.
* `ContDiffOn.differentiableOn_iteratedFDeriv_of_isOpen`: a map `C^n` on an open set has
  differentiable iterated derivatives of order `m < n` there.
* `ContDiffOn.continuousOn_fderivWithin_of_inter`: the derivative within a set of unique
  differentiability `s` of a `C¹` map on `s ∩ O`, for `O` open, is continuous on `s ∩ O`.
* `ContDiffOn.exists_eventually_norm_fderiv_le`: a `C¹` map on a set of unique differentiability
  `s` has a locally bounded derivative at the interior points of `s`.
* `HasStrictFDerivAt.continuousAt_of_eventually_hasFDerivAt`: a derivative field that is the
  strict derivative at `x` is continuous at `x`.
* `contDiff_one_of_forall_hasStrictFDerivAt`: a map that is strictly differentiable at every point
  is `C¹`.
-/

public section

open scoped ContDiff Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} {f : E → F} {s : Set E} {x : E}

/-- If `f` is `C^n` within `s` at `x` with `1 ≤ n`, then `f` is differentiable within `s` at all
points in a `𝓝[insert x s] x`-neighborhood of `x`. -/
theorem ContDiffWithinAt.eventually_differentiableWithinAt
    (hf : ContDiffWithinAt 𝕜 n f s x) (hn : 1 ≤ n) :
    ∀ᶠ y in 𝓝[insert x s] x, DifferentiableWithinAt 𝕜 f s y :=
  ((hf.of_le hn).eventually (by simp)).mono fun _ hy ↦ hy.differentiableWithinAt one_ne_zero

/-- If `f` is `C^n` at `x` with `1 ≤ n`, then `f` is differentiable on a neighborhood of `x`. -/
theorem ContDiffAt.eventually_differentiableAt (hf : ContDiffAt 𝕜 n f x) (hn : 1 ≤ n) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y :=
  ((hf.of_le hn).eventually (by simp)).mono fun _ hy ↦ hy.differentiableAt_one

/-- The derivative of a function of one variable that is `C²` at `x` is differentiable at `x`. -/
theorem ContDiffAt.differentiableAt_deriv_two {f : 𝕜 → F} {x : 𝕜} (hf : ContDiffAt 𝕜 2 f x) :
    DifferentiableAt 𝕜 (deriv f) x :=
  (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- A map that is `C^n` on an open set has differentiable iterated derivatives of every order
`m < n` there. -/
theorem ContDiffOn.differentiableOn_iteratedFDeriv_of_isOpen {m : ℕ} (hf : ContDiffOn 𝕜 n f s)
    (hmn : m < n) (hs : IsOpen s) : DifferentiableOn 𝕜 (iteratedFDeriv 𝕜 m f) s :=
  (hf.differentiableOn_iteratedFDerivWithin hmn hs.uniqueDiffOn).congr fun _ hx ↦
    (iteratedFDerivWithin_of_isOpen m hs hx).symm

/-- If `f` is `C¹` on the part `s ∩ O` of a set of unique differentiability `s` in an open set `O`,
its derivative within `s` is continuous on `s ∩ O`. -/
theorem ContDiffOn.continuousOn_fderivWithin_of_inter {O : Set E} (hf : ContDiffOn 𝕜 n f (s ∩ O))
    (hs : UniqueDiffOn 𝕜 s) (hO : IsOpen O) (hn : 1 ≤ n) :
    ContinuousOn (fderivWithin 𝕜 f s) (s ∩ O) :=
  (hf.continuousOn_fderivWithin (hs.inter hO) hn).congr
    fun _ hz ↦ (fderivWithin_inter (hO.mem_nhds hz.2)).symm

/-- A map `C^n` (`1 ≤ n`) on a set of unique differentiability `s` is, near each point of `s`,
differentiable with a uniformly bounded derivative at the interior points of `s`. -/
theorem ContDiffOn.exists_eventually_norm_fderiv_le (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (hn : 1 ≤ n) (hx : x ∈ s) :
    ∃ B, 0 ≤ B ∧ ∀ᶠ y in 𝓝[s] x, y ∈ interior s →
      DifferentiableAt 𝕜 f y ∧ ‖fderiv 𝕜 f y‖ ≤ B := by
  refine ⟨‖fderivWithin 𝕜 f s x‖ + 1, by positivity, ?_⟩
  filter_upwards [(hf.continuousOn_fderivWithin hs hn x hx).norm.eventually
    (gt_mem_nhds (lt_add_one _))] with y hy hys
  -- at an interior point, `fderivWithin` is `fderiv`
  have hsy := mem_interior_iff_mem_nhds.1 hys
  refine ⟨((hf.contDiffAt hsy).of_le hn).differentiableAt_one, ?_⟩
  rw [← fderivWithin_of_mem_nhds hsy]
  exact hy.le

/-- **A strict derivative is continuous at its point.** If `f` has derivative `f' x` at every `x`
near `x₀`, and `f' x₀` is its strict derivative at `x₀`, then `f'` is continuous at `x₀`. -/
theorem HasStrictFDerivAt.continuousAt_of_eventually_hasFDerivAt {f' : E → E →L[𝕜] F}
    (hf : HasStrictFDerivAt f (f' x) x) (hf' : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) :
    ContinuousAt f' x := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  -- `f - f' x` has strict derivative `0` at `x`, so it is `ε / 2`-Lipschitz near `x`
  obtain ⟨s, hs, hlip⟩ := (hf.sub (f' x).hasStrictFDerivAt).exists_lipschitzOnWith_of_nnNorm_lt
    ⟨ε / 2, by positivity⟩ (by rw [sub_self, nnNorm_zero]; exact NNReal.coe_pos.1 (half_pos hε))
  filter_upwards [hf', eventually_mem_nhds_iff.2 hs] with y hy hsy
  rw [dist_eq_norm]
  exact ((hy.sub (f' x).hasFDerivAt).le_of_lipschitzOn hsy hlip).trans_lt (half_lt_self hε)

/-- **Strict differentiability everywhere gives `C¹`.** A map with strict derivative `f' x` at
every point `x` is `C¹`. -/
theorem contDiff_one_of_forall_hasStrictFDerivAt {f' : E → E →L[𝕜] F}
    (hf : ∀ x, HasStrictFDerivAt f (f' x) x) : ContDiff 𝕜 1 f :=
  contDiff_one_iff_hasFDerivAt.2 ⟨f', continuous_iff_continuousAt.2 fun x ↦
    (hf x).continuousAt_of_eventually_hasFDerivAt
      (Filter.Eventually.of_forall fun y ↦ (hf y).hasFDerivAt), fun x ↦ (hf x).hasFDerivAt⟩

end
