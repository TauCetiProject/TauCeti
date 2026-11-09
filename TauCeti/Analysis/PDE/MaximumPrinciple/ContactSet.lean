/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.Analysis.Calculus.Morse.Linearization
public import Mathlib.Analysis.InnerProductSpace.Positive
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Convex.SubgradientImage
import Mathlib.Topology.MetricSpace.Sequences

/-!
# The upper contact set and its gradient image

For a function `u : E → ℝ` on a subset `Ω` of a real inner product space, the *upper contact set*
`TauCeti.PDE.upperContactSet u Ω` is the set of points `y ∈ Ω` at which an affine function touches
`u` from above on all of `Ω`: `u x ≤ u y + ⟪p, x - y⟫` for every `x ∈ Ω` and some slope `p`.

This file proves the geometric half of the Aleksandrov–Bakelman–Pucci maximum principle
(Gilbarg–Trudinger, Lemma 9.2). Let `Ω` be bounded and open in a finite-dimensional space, let `u`
be continuous on `closure Ω` and `C²` in `Ω`, let `m` bound `u` on `frontier Ω`, and let `x ∈ Ω`.
Every vector `p` with `‖p‖ diam Ω < u x - m` is the gradient of `u` at a point of the upper
contact set: on the frontier `u` lies below the affine function through `(x, u x)` with slope
`p`, so `p` supports `u` from above at some point of `Ω`
(`TauCeti.exists_forall_add_inner_add_le_of_forall_frontier_le`, applied to `-u`), where the
gradient is `p`. The gradient is `C¹` with derivative the Hessian operator, so the
change-of-variables inequality bounds the measure of the gradient image, and

`μ (ball 0 ((u x - m) / diam Ω)) ≤ ∫⁻ y in upperContactSet u Ω, |det D²u(y)| ∂μ`

for every additive Haar measure `μ`. On the upper contact set the Hessian is negative
semidefinite, which is what turns this measure estimate into a bound on `u` in terms of an
elliptic operator applied to it, in
`TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Basic`.

## Main declarations

* `TauCeti.PDE.upperContactSet`: the upper contact set of `u` on `Ω`.
* `TauCeti.PDE.mem_upperContactSet_iff_gradient`: on an open set where `u` is differentiable,
  the supporting slope at a contact point is the gradient.
* `TauCeti.PDE.measurableSet_upperContactSet`: for `u` of class `C¹` on an open set, the upper
  contact set is relatively closed, hence measurable.
* `TauCeti.PDE.fderiv_fderiv_self_nonpos_of_mem_upperContactSet`: the second derivative of a `C²`
  function is nonpositive on the diagonal at a point of the upper contact set.
* `TauCeti.PDE.isPositive_neg_hessianOperator_of_mem_upperContactSet`: there the negated Hessian
  operator is positive.
* `TauCeti.PDE.mem_upperContactSet_of_frequently`: a point in the upper contact sets of infinitely
  many uniform approximants of `u` lies in the upper contact set of `u`.
* `TauCeti.PDE.ball_subset_image_gradient_upperContactSet`: the ball of radius
  `(u x - m) / diam Ω` lies in the gradient image of the upper contact set.
* `TauCeti.PDE.addHaar_image_gradient_upperContactSet_le`: the measure of that gradient image is
  at most the integral of `|det D²u|` over the upper contact set.
* `TauCeti.PDE.addHaar_ball_le_lintegral_abs_det_hessianOperator`: the two combined.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.1 (Lemma 9.2).
-/

public section

noncomputable section

open Filter InnerProductSpace Metric MeasureTheory Set Topology
open scoped Gradient RealInnerProductSpace

namespace TauCeti

namespace PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u : E → ℝ} {Ω : Set E}
  {x y p : E}

/-- The *upper contact set* of `u` on `Ω`: the points `y ∈ Ω` at which an affine function touches
`u` from above on all of `Ω`, that is, `u x ≤ u y + ⟪p, x - y⟫` for every `x ∈ Ω` and some slope
`p`. -/
def upperContactSet (u : E → ℝ) (Ω : Set E) : Set E :=
  {y | y ∈ Ω ∧ ∃ p : E, ∀ x ∈ Ω, u x ≤ u y + ⟪p, x - y⟫}

@[simp]
theorem mem_upperContactSet :
    y ∈ upperContactSet u Ω ↔ y ∈ Ω ∧ ∃ p : E, ∀ x ∈ Ω, u x ≤ u y + ⟪p, x - y⟫ :=
  Iff.rfl

theorem upperContactSet_subset : upperContactSet u Ω ⊆ Ω := fun _ hy => hy.1

/-- **The Hessian on the upper contact set.** At a point of the upper contact set of a function
that is `C²` on an open set, the second derivative is nonpositive on the diagonal:
`D²u(y)(w, w) ≤ 0`. -/
theorem fderiv_fderiv_self_nonpos_of_mem_upperContactSet (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hy : y ∈ upperContactSet u Ω) (w : E) :
    fderiv ℝ (fderiv ℝ u) y w w ≤ 0 := by
  obtain ⟨hyΩ, p, hp⟩ := hy
  have hyΩ' := hΩ.mem_nhds hyΩ
  have hu' := hu.contDiffAt hyΩ'
  have hmax : IsLocalMax (fun x => u x - innerSL ℝ p x) y := by
    simpa only [innerSL_apply_apply] using isLocalMax_sub_inner_of_forall_le hyΩ' hp
  have h := fderiv_fderiv_self_nonpos_of_isLocalMax
    (hu'.sub (innerSL ℝ p).contDiff.contDiffAt) hmax w
  rwa [fderiv_fderiv_sub_clm (g := u) ?_ (innerSL ℝ p)] at h
  filter_upwards [hyΩ'] with z hz
  exact (hu.contDiffAt (hΩ.mem_nhds hz)).differentiableAt two_ne_zero

variable [CompleteSpace E]

/-- On an open set where `u` is differentiable, the supporting slope at a point of the upper
contact set is the gradient of `u`. -/
theorem mem_upperContactSet_iff_gradient (hΩ : IsOpen Ω) (hu : DifferentiableOn ℝ u Ω) :
    y ∈ upperContactSet u Ω ↔ y ∈ Ω ∧ ∀ x ∈ Ω, u x ≤ u y + ⟪∇ u y, x - y⟫ := by
  refine ⟨fun ⟨hy, p, hp⟩ => ⟨hy, ?_⟩, fun ⟨hy, h⟩ => ⟨hy, _, h⟩⟩
  rwa [← eq_gradient_of_forall_le (hΩ.mem_nhds hy) (hu.differentiableAt (hΩ.mem_nhds hy)) hp]

/-- For `u` of class `C¹` on an open set `Ω`, the upper contact set is relatively closed in `Ω`,
hence measurable. -/
theorem measurableSet_upperContactSet [MeasurableSpace E] [OpensMeasurableSpace E]
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) : MeasurableSet (upperContactSet u Ω) := by
  have hdiff : DifferentiableOn ℝ u Ω := hu.differentiableOn one_ne_zero
  suffices h : Ω ∩ closure (upperContactSet u Ω) ⊆ upperContactSet u Ω by
    rw [Subset.antisymm (subset_inter upperContactSet_subset subset_closure) h]
    exact hΩ.measurableSet.inter isClosed_closure.measurableSet
  rintro y ⟨hy, hcl⟩
  rw [mem_upperContactSet_iff_gradient hΩ hdiff]
  refine ⟨hy, fun x hx => ?_⟩
  have hyΩ := hΩ.mem_nhds hy
  have hgrad : ContinuousAt (∇ u) y :=
    ((hu.contDiffAt hyΩ).gradient_right (m := 0) (by simp)).continuousAt
  have hcont : ContinuousAt (fun z => u z + ⟪∇ u z, x - z⟫) y :=
    (hu.continuousOn.continuousAt hyΩ).add (hgrad.inner (continuousAt_const.sub continuousAt_id))
  have : (𝓝[upperContactSet u Ω] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  refine ge_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := upperContactSet u Ω)))
    ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact ((mem_upperContactSet_iff_gradient hΩ hdiff).1 hz).2 x hx

/-- At a point of the upper contact set of a function that is `C²` on an open set, the negated
Hessian operator is positive. -/
theorem isPositive_neg_hessianOperator_of_mem_upperContactSet (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hy : y ∈ upperContactSet u Ω) :
    (-hessianOperator u y).IsPositive := by
  have hu' := hu.contDiffAt (hΩ.mem_nhds (upperContactSet_subset hy))
  refine (ContinuousLinearMap.isPositive_iff _).2 ⟨fun w w' => ?_, fun w => ?_⟩
  · simp only [ContinuousLinearMap.coe_coe, neg_apply, inner_neg_left,
      inner_neg_right, inner_hessianOperator_left]
    rw [real_inner_comm, inner_hessianOperator_left]
    exact congrArg Neg.neg (hu'.isSymmSndFDerivAt (by simp) w w')
  · rw [neg_apply, inner_neg_left, inner_hessianOperator_left, neg_nonneg]
    exact fderiv_fderiv_self_nonpos_of_mem_upperContactSet hΩ hu hy w

variable [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Uniform convergence on sets `U k` which eventually contain a ball around each point of `Ω`
gives pointwise convergence on `Ω`. -/
private theorem tendsto_of_eventually_abs_sub_le {U : ℕ → Set E} {v : ℕ → E → ℝ}
    (hUball : ∀ z ∈ Ω, ∃ r > 0, ∀ᶠ k in atTop, closedBall z r ⊆ U k)
    (hvu : ∀ ε > 0, ∀ᶠ k in atTop, ∀ z ∈ U k, |v k z - u z| ≤ ε) {z : E} (hz : z ∈ Ω) :
    Tendsto (fun k => v k z) atTop (𝓝 (u z)) := by
  obtain ⟨s, hs, hsb⟩ := hUball z hz
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [hsb, hvu (ε / 2) (half_pos hε)] with k hk hk'
  rw [Real.dist_eq]
  exact (hk' z (hk (mem_closedBall_self hs.le))).trans_lt (half_lt_self hε)

omit [CompleteSpace E] in
/-- **Contact points pass to the limit.** Let `v k` converge to `u` uniformly on sets `U k ⊆ Ω`
which eventually contain a ball around each point of `Ω`. If `y` lies in the upper contact set of
`v k` on `U k` for infinitely many `k`, then `y` lies in the upper contact set of `u` on `Ω`. -/
theorem mem_upperContactSet_of_frequently {U : ℕ → Set E} {v : ℕ → E → ℝ}
    (hu : ContinuousOn u Ω) (hUΩ : ∀ k, U k ⊆ Ω)
    (hUball : ∀ z ∈ Ω, ∃ r > 0, ∀ᶠ k in atTop, closedBall z r ⊆ U k)
    (hvu : ∀ ε > 0, ∀ᶠ k in atTop, ∀ z ∈ U k, |v k z - u z| ≤ ε)
    (hfreq : ∃ᶠ k in atTop, y ∈ upperContactSet (v k) (U k)) :
    y ∈ upperContactSet u Ω := by
  obtain ⟨k₀, hk₀⟩ := hfreq.exists
  have hyΩ : y ∈ Ω := hUΩ k₀ (upperContactSet_subset hk₀)
  obtain ⟨r, hr, hball⟩ := hUball y hyΩ
  obtain ⟨k₁, hk₁⟩ := hball.exists
  -- `u` is bounded on the ball around `y`.
  obtain ⟨M, hM⟩ := (isCompact_closedBall y r).exists_bound_of_continuousOn
    (hu.mono (hk₁.trans (hUΩ k₁)))
  -- Along a subsequence, `y` is a contact point and `v k` is uniformly close to `u`, so the
  -- supporting slopes are bounded and a further subsequence of them converges.
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop
    ((hfreq.and_eventually hball).and_eventually (hvu 1 one_pos))
  choose p hp using fun j => (mem_upperContactSet.1 (hP j).1.1).2
  have hpb (j : ℕ) : p j ∈ closedBall (0 : E) (2 * (M + 1) / r) := by
    rw [mem_closedBall_zero_iff, le_div_iff₀ hr, mul_comm, ← norm_neg]
    refine mul_norm_le_of_forall_add_inner_le (u := fun z => -v (φ j) z) hr.le (hP j).1.2
      (fun z hz => ?_) fun z hz => ?_
    · have h := abs_le.1 ((hP j).2 z ((hP j).1.2 hz))
      have h' := abs_le.1 (Real.norm_eq_abs _ ▸ hM z hz)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · rw [inner_neg_right, real_inner_comm]
      linarith [hp j z hz]
  obtain ⟨q, -, ψ, hψ, hq⟩ := tendsto_subseq_of_bounded isBounded_closedBall hpb
  -- Pass to the limit in the supporting inequalities.
  have hφψ : Tendsto (fun j => φ (ψ j)) atTop atTop := hφ.tendsto_atTop.comp hψ.tendsto_atTop
  have hlim {z : E} (hz : z ∈ Ω) : Tendsto (fun j => v (φ (ψ j)) z) atTop (𝓝 (u z)) :=
    (tendsto_of_eventually_abs_sub_le hUball hvu hz).comp hφψ
  refine mem_upperContactSet.2 ⟨hyΩ, q, fun z hz => le_of_tendsto_of_tendsto (hlim hz)
    ((hlim hyΩ).add (hq.inner tendsto_const_nhds)) ?_⟩
  obtain ⟨s, hs, hsb⟩ := hUball z hz
  filter_upwards [hφψ.eventually hsb] with j hj
  exact hp (ψ j) z (hj (mem_closedBall_self hs.le))

/-- **The gradient image of the upper contact set** (Gilbarg–Trudinger, Lemma 9.2). Let `Ω` be
bounded and open, let `u` be continuous on `closure Ω` and differentiable in `Ω`, and let `m`
bound `u` on `frontier Ω`. For `x ∈ Ω`, every vector of norm less than `(u x - m) / diam Ω` is the
gradient of `u` at a point of the upper contact set. The ball is empty unless `u x > m`. -/
theorem ball_subset_image_gradient_upperContactSet {m : ℝ} (hΩb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω)) (hdiff : DifferentiableOn ℝ u Ω)
    (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω) :
    ball 0 ((u x - m) / diam Ω) ⊆ ∇ u '' upperContactSet u Ω := by
  intro p hp
  rw [mem_ball_zero_iff] at hp
  have hd : 0 < diam Ω := by
    rcases div_pos_iff.1 ((norm_nonneg p).trans_lt hp) with h | h
    · exact h.2
    · exact absurd h.2 (not_lt.2 diam_nonneg)
  have hpd : ‖p‖ * diam Ω < u x - m := (lt_div_iff₀ hd).1 hp
  -- On the frontier, `u` lies below the affine function through `(x, u x)` with slope `p`, so
  -- `p` supports `u` from above at some point of `Ω`.
  obtain ⟨y, hyΩ, hy⟩ := exists_forall_add_inner_add_le_of_forall_frontier_le
    (u := fun z => -u z) (w := fun _ => -m) hΩb.isCompact_closure hcont.neg continuousOn_const
    (fun z hz => neg_le_neg (hm z hz)) hx (p := 0) (q := -p) (by simp)
    (by rw [norm_neg]; linarith)
  have hsupp (z : E) (hz : z ∈ Ω) : u z ≤ u y + ⟪p, z - y⟫ := by
    have := hy z hz
    rw [zero_add, inner_neg_right, real_inner_comm] at this
    linarith
  exact ⟨y, ⟨hyΩ, p, hsupp⟩, (eq_gradient_of_forall_le (hΩ.mem_nhds hyΩ)
    (hdiff.differentiableAt (hΩ.mem_nhds hyΩ)) hsupp).symm⟩

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The measure of the gradient image of the upper contact set of a function `C²` on an open set
is at most the integral of the absolute Hessian determinant over the upper contact set. -/
theorem addHaar_image_gradient_upperContactSet_le (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) :
    μ (∇ u '' upperContactSet u Ω) ≤
      ∫⁻ y in upperContactSet u Ω, ENNReal.ofReal |(hessianOperator u y).det| ∂μ :=
  addHaar_image_le_lintegral_abs_det_fderiv μ
    (measurableSet_upperContactSet hΩ (hu.of_le (by norm_num))) fun _ hy =>
      (hu.contDiffAt (hΩ.mem_nhds
        (upperContactSet_subset hy))).hasFDerivAt_gradient.hasFDerivWithinAt

/-- **The Aleksandrov measure estimate** (Gilbarg–Trudinger, Lemma 9.2). Let `Ω` be bounded and
open, let `u` be continuous on `closure Ω` and `C²` in `Ω`, and let `m` bound `u` on
`frontier Ω`. For `x ∈ Ω` and every additive Haar measure `μ`,
`μ (ball 0 ((u x - m) / diam Ω)) ≤ ∫⁻ y in upperContactSet u Ω, |det D²u(y)| ∂μ`. -/
theorem addHaar_ball_le_lintegral_abs_det_hessianOperator {m : ℝ}
    (hΩb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω))
    (hu : ContDiffOn ℝ 2 u Ω) (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω) :
    μ (ball 0 ((u x - m) / diam Ω)) ≤
      ∫⁻ y in upperContactSet u Ω, ENNReal.ofReal |(hessianOperator u y).det| ∂μ :=
  (measure_mono (ball_subset_image_gradient_upperContactSet hΩb hΩ hcont
    (hu.differentiableOn two_ne_zero) hm hx)).trans
    (addHaar_image_gradient_upperContactSet_le μ hΩ hu)

end PDE

end TauCeti
