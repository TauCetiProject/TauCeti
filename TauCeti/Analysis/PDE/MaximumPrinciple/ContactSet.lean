/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.Analysis.Calculus.Morse.Linearization
import Mathlib.Topology.MetricSpace.Sequences
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Convex.SubgradientImage

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
* `TauCeti.PDE.norm_le_of_forall_le_add_inner`: supporting slopes of a bounded function at a
  point with a ball around it are bounded.
* `TauCeti.PDE.norm_mul_le_sub_of_forall_le_add_inner`: a supporting slope small enough for the
  affine function to stay above `m` on `Ω` is at most the height of `u` above `m` divided by the
  distance to the complement of `Ω`.
* `TauCeti.PDE.mem_upperContactSet_of_frequently`: upper contact sets are upper semicontinuous
  along pointwise convergent sequences of functions uniformly bounded on growing sets `Vₖ`,
  which is how the estimate passes from smooth approximations to their limit.
* `TauCeti.PDE.mem_upperContactSet_iff_gradient`: on an open set where `u` is differentiable,
  the supporting slope at a contact point is the gradient.
* `TauCeti.PDE.measurableSet_upperContactSet`: for `u` of class `C¹` on an open set, the upper
  contact set is relatively closed, hence measurable.
* `TauCeti.PDE.measurableSet_upperContactSet_inter_setOf_norm_gradient_lt`: so is its part where
  `‖∇u‖ < r`.
* `TauCeti.PDE.fderiv_fderiv_self_nonpos_of_mem_upperContactSet`: the second derivative of a `C²`
  function is nonpositive on the diagonal at a point of the upper contact set.
* `TauCeti.PDE.ball_subset_image_gradient_upperContactSet`: the ball of radius
  `(u x - m) / diam Ω` lies in the gradient image of the upper contact set.
* `TauCeti.PDE.addHaar_image_gradient_le_lintegral_abs_det_hessianOperator`: the measure of the
  gradient image of a measurable `S ⊆ Ω` is at most the integral of `|det D²u|` over `S`.
* `TauCeti.PDE.addHaar_ball_le_lintegral_abs_det_hessianOperator`: the two combined.
* `TauCeti.PDE.ball_subset_image_gradient_upperContactSet_inter`,
  `TauCeti.PDE.addHaar_ball_le_lintegral_abs_det_hessianOperator_inter`: the same with the contact
  set restricted to the points where `‖∇u‖ < (u x - m) / diam Ω`, on which the supporting affine
  functions stay above `m`.

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

/-- **Supporting slopes are bounded.** If an affine function with slope `p` touches `u` from above
at `x` on a set `Ω` containing `ball x r`, and `|u| ≤ M` on `Ω`, then `‖p‖ ≤ 4 M / r`. -/
theorem norm_le_of_forall_le_add_inner {r M : ℝ} (hr : 0 < r) (hball : ball x r ⊆ Ω)
    (hM : ∀ y ∈ Ω, |u y| ≤ M) (hp : ∀ y ∈ Ω, u y ≤ u x + ⟪p, y - x⟫) : ‖p‖ ≤ 4 * M / r := by
  rw [le_div_iff₀ hr]
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa using (abs_nonneg _).trans (hM x (hball (mem_ball_self hr)))
  -- Test the supporting inequality at the point at distance `r / 2` from `x` against `p`.
  have hnp : 0 < ‖p‖ := norm_pos_iff.2 hp0
  set t := r / 2 / ‖p‖
  have ht : 0 < t := by positivity
  have htp : t * ‖p‖ = r / 2 := div_mul_cancel₀ _ hnp.ne'
  set y := x - t • p
  have hyx : y - x = -(t • p) := by simp [y]
  have hdist : dist y x = r / 2 := by
    rw [dist_eq_norm, hyx, norm_neg, norm_smul, Real.norm_of_nonneg ht.le, htp]
  have hinner : ⟪p, y - x⟫ = -(r / 2 * ‖p‖) := by
    rw [hyx, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    linear_combination (-‖p‖) * htp
  have hy : y ∈ Ω := hball (by rw [mem_ball, hdist]; linarith)
  have h := hinner ▸ hp y hy
  have h1 := le_abs_self (u x) |>.trans (hM x (hball (mem_ball_self hr)))
  have h2 := neg_abs_le (u y) |>.trans' (neg_le_neg (hM y hy))
  linarith

/-- **Supporting slopes below the height of `u`.** Let `Ω` be bounded and let an affine function
with slope `p` touch `u` from above on `Ω` at `y`. If `‖p‖ diam Ω ≤ u x₀ - m` for some `x₀ ∈ Ω`,
then the affine function is at least `m` on `Ω`, so its slope is at most the height of `u y`
above `m` divided by the distance to the complement: `‖p‖ r ≤ u y - m` whenever
`ball y r ⊆ Ω`. -/
theorem norm_mul_le_sub_of_forall_le_add_inner {r m : ℝ} {x₀ : E} (hΩb : Bornology.IsBounded Ω)
    (hx₀ : x₀ ∈ Ω) (hp : ∀ x ∈ Ω, u x ≤ u y + ⟪p, x - y⟫) (hpd : ‖p‖ * diam Ω ≤ u x₀ - m)
    (hr : 0 < r) (hball : ball y r ⊆ Ω) : ‖p‖ * r ≤ u y - m := by
  -- The affine function through `(y, u y)` with slope `p` is at least `m` on `Ω`.
  have hℓ (z : E) (hz : z ∈ Ω) : m ≤ u y + ⟪p, z - y⟫ := by
    have hd : ‖z - x₀‖ ≤ diam Ω := by
      rw [← dist_eq_norm]
      exact dist_le_diam_of_mem hΩb hz hx₀
    have hzx := neg_le_of_abs_le ((abs_real_inner_le_norm p (z - x₀)).trans
      (mul_le_mul_of_nonneg_left hd (norm_nonneg p)))
    have hsplit : ⟪p, z - y⟫ = ⟪p, x₀ - y⟫ + ⟪p, z - x₀⟫ := by
      rw [← inner_add_right, sub_add_sub_cancel']
    linarith [hp x₀ hx₀]
  have hy := hℓ y (hball (mem_ball_self hr))
  rw [sub_self, inner_zero_right, add_zero] at hy
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa using hy
  have hnp : 0 < ‖p‖ := norm_pos_iff.2 hp0
  -- Test the affine function at `y - t (p / ‖p‖)` for `t < r`.
  rw [mul_comm, ← le_div_iff₀ hnp]
  refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
  rcases lt_or_ge t 0 with ht0 | ht0
  · exact ht0.le.trans (div_nonneg (sub_nonneg.2 hy) hnp.le)
  set z := y - (t / ‖p‖) • p
  have hzy : z - y = -((t / ‖p‖) • p) := by simp [z]
  have hz : z ∈ Ω := hball <| by
    rw [mem_ball, dist_eq_norm, hzy, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ hnp.ne']
    exact ht
  have h := hℓ z hz
  rw [hzy, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  rw [le_div_iff₀ hnp]
  have : t / ‖p‖ * ‖p‖ ^ 2 = t * ‖p‖ := by field_simp
  linarith

/-- **Upper semicontinuity of upper contact sets.** Let `uₖ` converge pointwise to `u` on `Ω`, and
let `Vₖ` be sets such that every point of `Ω` lies in `Vₖ` for all large `k`, a fixed ball around
`x ∈ Ω` lies in `Vₖ` for all large `k`, and the `uₖ` are eventually bounded on `Vₖ` uniformly in
`k`. If `x` lies in the upper contact set of `uₖ` on `Vₖ` for infinitely many `k`, then `x` lies in
the upper contact set of `u` on `Ω`. -/
theorem mem_upperContactSet_of_frequently [ProperSpace E] {us : ℕ → E → ℝ} {V : ℕ → Set E}
    {r M : ℝ} (hr : 0 < r) (hball : ∀ᶠ k in atTop, ball x r ⊆ V k)
    (hmem : ∀ y ∈ Ω, ∀ᶠ k in atTop, y ∈ V k) (hM : ∀ᶠ k in atTop, ∀ y ∈ V k, |us k y| ≤ M)
    (hconv : ∀ y ∈ Ω, Tendsto (fun k => us k y) atTop (𝓝 (u y))) (hx : x ∈ Ω)
    (hfreq : ∃ᶠ k in atTop, x ∈ upperContactSet (us k) (V k)) :
    x ∈ upperContactSet u Ω := by
  obtain ⟨φ, hφ, hφx⟩ := extraction_of_frequently_atTop hfreq
  choose P hP using fun j => (hφx j).2
  -- Along the extracted subsequence the slopes are eventually bounded, so a further
  -- subsequence of them converges.
  have hPb : ∀ᶠ j in atTop, P j ∈ closedBall (0 : E) (4 * M / r) := by
    filter_upwards [hφ.tendsto_atTop.eventually (hball.and hM)] with j ⟨hb, hMj⟩
    exact mem_closedBall_zero_iff.2 (norm_le_of_forall_le_add_inner hr hb hMj (hP j))
  obtain ⟨p, -, ψ, hψ, hPψ⟩ :=
    tendsto_subseq_of_frequently_bounded isBounded_closedBall hPb.frequently
  have hk : Tendsto (φ ∘ ψ) atTop atTop := hφ.tendsto_atTop.comp hψ.tendsto_atTop
  refine ⟨hx, p, fun y hy => le_of_tendsto_of_tendsto ((hconv y hy).comp hk)
    (((hconv x hx).comp hk).add (hPψ.inner tendsto_const_nhds)) ?_⟩
  filter_upwards [hk.eventually (hmem y hy)] with j hj
  exact hP (ψ j) y hj

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

/-- For `u` of class `C¹` on an open set `Ω`, the part of the upper contact set where `‖∇u‖ < r`
is measurable. -/
theorem measurableSet_upperContactSet_inter_setOf_norm_gradient_lt [MeasurableSpace E]
    [BorelSpace E] (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (r : ℝ) :
    MeasurableSet (upperContactSet u Ω ∩ {y | ‖∇ u y‖ < r}) :=
  (measurableSet_upperContactSet hΩ hu).inter
    (measurableSet_lt (measurable_gradient u).norm measurable_const)

variable [FiniteDimensional ℝ E]

/-- **The gradient image of the upper contact set** (Gilbarg–Trudinger, Lemma 9.2). Let `Ω` be
bounded and open, let `u` be continuous on `closure Ω` and differentiable in `Ω`, and let `m`
bound `u` on `frontier Ω`. For `x ∈ Ω` and `r = (u x - m) / diam Ω`, every vector of norm less
than `r` is the gradient of `u` at a point of the upper contact set where the gradient has norm
less than `r`. On that part of the contact set the supporting affine functions are at least `m`
on `Ω` (`TauCeti.PDE.norm_mul_le_sub_of_forall_le_add_inner`). The ball is empty unless
`u x > m`. -/
theorem ball_subset_image_gradient_upperContactSet_inter {m : ℝ} (hΩb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω)) (hdiff : DifferentiableOn ℝ u Ω)
    (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω) :
    ball 0 ((u x - m) / diam Ω) ⊆
      ∇ u '' (upperContactSet u Ω ∩ {y | ‖∇ u y‖ < (u x - m) / diam Ω}) := by
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
  have hgrad : ∇ u y = p := (eq_gradient_of_forall_le (hΩ.mem_nhds hyΩ)
    (hdiff.differentiableAt (hΩ.mem_nhds hyΩ)) hsupp).symm
  exact ⟨y, ⟨⟨hyΩ, p, hsupp⟩, show ‖∇ u y‖ < _ by rw [hgrad]; exact hp⟩, hgrad⟩

/-- **The gradient image of the upper contact set** (Gilbarg–Trudinger, Lemma 9.2). Under the
hypotheses of `TauCeti.PDE.ball_subset_image_gradient_upperContactSet_inter`, every vector of
norm less than `(u x - m) / diam Ω` is the gradient of `u` at a point of the upper contact set. -/
theorem ball_subset_image_gradient_upperContactSet {m : ℝ} (hΩb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω)) (hdiff : DifferentiableOn ℝ u Ω)
    (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω) :
    ball 0 ((u x - m) / diam Ω) ⊆ ∇ u '' upperContactSet u Ω :=
  (ball_subset_image_gradient_upperContactSet_inter hΩb hΩ hcont hdiff hm hx).trans
    (image_mono inter_subset_left)

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The measure of the gradient image of a measurable subset `S` of an open set `Ω` on which `u`
is `C²` is at most the integral of the absolute Hessian determinant over `S`. -/
theorem addHaar_image_gradient_le_lintegral_abs_det_hessianOperator {S : Set E} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) :
    μ (∇ u '' S) ≤ ∫⁻ y in S, ENNReal.ofReal |(hessianOperator u y).det| ∂μ :=
  addHaar_image_le_lintegral_abs_det_fderiv μ hS fun _ hy =>
    (hu.contDiffAt (hΩ.mem_nhds (hSΩ hy))).hasFDerivAt_gradient.hasFDerivWithinAt

/-- **The Aleksandrov measure estimate** (Gilbarg–Trudinger, Lemma 9.2). Let `Ω` be bounded and
open, let `u` be continuous on `closure Ω` and `C²` in `Ω`, and let `m` bound `u` on
`frontier Ω`. For `x ∈ Ω`, every additive Haar measure `μ` and `r = (u x - m) / diam Ω`, the
integral may be restricted to the points of the upper contact set where `‖∇u‖ < r`:
`μ (ball 0 r) ≤ ∫⁻ y in upperContactSet u Ω ∩ {‖∇u‖ < r}, |det D²u(y)| ∂μ`. -/
theorem addHaar_ball_le_lintegral_abs_det_hessianOperator_inter {m : ℝ}
    (hΩb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω))
    (hu : ContDiffOn ℝ 2 u Ω) (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω) :
    μ (ball 0 ((u x - m) / diam Ω)) ≤
      ∫⁻ y in upperContactSet u Ω ∩ {y | ‖∇ u y‖ < (u x - m) / diam Ω},
        ENNReal.ofReal |(hessianOperator u y).det| ∂μ :=
  (measure_mono (ball_subset_image_gradient_upperContactSet_inter hΩb hΩ hcont
    (hu.differentiableOn two_ne_zero) hm hx)).trans
    (addHaar_image_gradient_le_lintegral_abs_det_hessianOperator μ hΩ hu
      (measurableSet_upperContactSet_inter_setOf_norm_gradient_lt hΩ (hu.of_le (by norm_num)) _)
      (inter_subset_left.trans upperContactSet_subset))

/-- **The Aleksandrov measure estimate** (Gilbarg–Trudinger, Lemma 9.2). Let `Ω` be bounded and
open, let `u` be continuous on `closure Ω` and `C²` in `Ω`, and let `m` bound `u` on
`frontier Ω`. For `x ∈ Ω` and every additive Haar measure `μ`,
`μ (ball 0 ((u x - m) / diam Ω)) ≤ ∫⁻ y in upperContactSet u Ω, |det D²u(y)| ∂μ`. -/
theorem addHaar_ball_le_lintegral_abs_det_hessianOperator {m : ℝ}
    (hΩb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω))
    (hu : ContDiffOn ℝ 2 u Ω) (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω) :
    μ (ball 0 ((u x - m) / diam Ω)) ≤
      ∫⁻ y in upperContactSet u Ω, ENNReal.ofReal |(hessianOperator u y).det| ∂μ :=
  (addHaar_ball_le_lintegral_abs_det_hessianOperator_inter μ hΩb hΩ hcont hu hm hx).trans
    (lintegral_mono_set inter_subset_left)

end PDE

end TauCeti
