/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.Analysis.Calculus.Morse.Linearization
public import Mathlib.Analysis.InnerProductSpace.Positive
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
* `TauCeti.PDE.mem_upperContactSet_of_forall_le_add_inner`: on a superlevel set `S ⊆ Ω`, contact
  points with small slopes are contact points on `Ω`.
* `TauCeti.PDE.norm_le_of_forall_le_add_inner`: supporting slopes of a bounded function at a
  point with a ball around it are bounded.
* `TauCeti.PDE.exists_mem_forall_le_add_inner_of_frequently`: supporting slopes in a closed set
  persist along pointwise convergent sequences of functions uniformly bounded on growing sets
  `Vₖ`, which is how the estimate passes from smooth approximations to their limit.
* `TauCeti.PDE.mem_upperContactSet_of_frequently`: hence upper contact sets are upper
  semicontinuous along such sequences.
* `TauCeti.PDE.mem_upperContactSet_iff_gradient`: on an open set where `u` is differentiable,
  the supporting slope at a contact point is the gradient.
* `TauCeti.PDE.measurableSet_upperContactSet`: for `u` of class `C¹` on an open set, the upper
  contact set is relatively closed, hence measurable.
* `TauCeti.PDE.fderiv_fderiv_self_nonpos_of_mem_upperContactSet`: the second derivative of a `C²`
  function is nonpositive on the diagonal at a point of the upper contact set.
* `TauCeti.PDE.isPositive_neg_hessianOperator_of_mem_upperContactSet`: there the negated Hessian
  operator is positive.
* `TauCeti.PDE.ball_subset_image_gradient_upperContactSet`: the ball of radius
  `(u x - m) / diam Ω` lies in the gradient image of the upper contact set.
* `TauCeti.PDE.addHaar_image_gradient_le_lintegral_abs_det_hessianOperator`: the measure of the
  gradient image of a measurable subset of `Ω` is at most the integral of `|det D²u|` over it.
* `TauCeti.PDE.addHaar_ball_le_lintegral_inter_preimage_abs_det_hessianOperator`: the two
  combined, for the slopes in a ball of radius `r ≤ (u x - m) / diam Ω`: `μ (ball 0 r)` is at most
  the integral of `|det D²u|` over the contact points where `‖∇ u‖ < r`.
* `TauCeti.PDE.addHaar_ball_le_lintegral_abs_det_hessianOperator`: the case
  `r = (u x - m) / diam Ω`, over the whole upper contact set.

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

/-- **Contact points on a subset.** Let `x ∈ S ⊆ Ω` with `Ω` bounded, and let `u ≤ c` on `Ω \ S`.
If the affine function with slope `p` through `(y, u y)` lies above `u` on `S`, and
`‖p‖ diam Ω ≤ u x - c`, then it lies above `u` on all of `Ω`, so `y` is in the upper contact set
of `u` on `Ω`. Applied to a superlevel set `S = {u > c}`, this says that contact points on `S` with
small slopes are contact points on `Ω`. -/
theorem mem_upperContactSet_of_forall_le_add_inner {S : Set E} {c : ℝ}
    (hΩb : Bornology.IsBounded Ω) (hSΩ : S ⊆ Ω) (hc : ∀ z ∈ Ω, z ∉ S → u z ≤ c) (hxS : x ∈ S)
    (hyS : y ∈ S) (hpc : ‖p‖ * diam Ω ≤ u x - c) (hsupp : ∀ z ∈ S, u z ≤ u y + ⟪p, z - y⟫) :
    y ∈ upperContactSet u Ω := by
  refine ⟨hSΩ hyS, p, fun z hz => ?_⟩
  by_cases hzS : z ∈ S
  · exact hsupp z hzS
  -- Off `S`, `u ≤ c`, while the affine function is at least `u x - ‖p‖ diam Ω ≥ c` on `Ω`.
  have hpzx : -(‖p‖ * diam Ω) ≤ ⟪p, z - x⟫ := neg_le_of_abs_le ((abs_real_inner_le_norm p
    (z - x)).trans (mul_le_mul_of_nonneg_left ((dist_eq_norm z x).symm.trans_le
      (dist_le_diam_of_mem hΩb hz (hSΩ hxS))) (norm_nonneg p)))
  have hxy := hsupp x hxS
  rw [inner_sub_right] at hpzx hxy ⊢
  linarith [hc z hz hzS]

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

/-- **Limits of supporting slopes.** Let `uₖ` converge pointwise to `u` on `Ω`, and let `Vₖ` be
sets such that every point of `Ω` lies in `Vₖ` for all large `k`, a fixed ball around `x ∈ Ω` lies
in `Vₖ` for all large `k`, and the `uₖ` are eventually bounded on `Vₖ` uniformly in `k`. If for
infinitely many `k` an affine function with slope in a closed set `K` touches `uₖ` from above at
`x` on `Vₖ`, then an affine function with slope in `K` touches `u` from above at `x` on `Ω`. -/
theorem exists_mem_forall_le_add_inner_of_frequently [ProperSpace E] {us : ℕ → E → ℝ}
    {V : ℕ → Set E} {K : Set E} {r M : ℝ} (hK : IsClosed K) (hr : 0 < r)
    (hball : ∀ᶠ k in atTop, ball x r ⊆ V k) (hmem : ∀ y ∈ Ω, ∀ᶠ k in atTop, y ∈ V k)
    (hM : ∀ᶠ k in atTop, ∀ y ∈ V k, |us k y| ≤ M)
    (hconv : ∀ y ∈ Ω, Tendsto (fun k => us k y) atTop (𝓝 (u y))) (hx : x ∈ Ω)
    (hfreq : ∃ᶠ k in atTop, ∃ p ∈ K, ∀ y ∈ V k, us k y ≤ us k x + ⟪p, y - x⟫) :
    ∃ p ∈ K, ∀ y ∈ Ω, u y ≤ u x + ⟪p, y - x⟫ := by
  obtain ⟨φ, hφ, hφx⟩ := extraction_of_frequently_atTop hfreq
  choose P hPK hP using hφx
  -- Along the extracted subsequence the slopes are eventually bounded, so a further
  -- subsequence of them converges, and its limit lies in the closed set `K`.
  have hPb : ∀ᶠ j in atTop, P j ∈ closedBall (0 : E) (4 * M / r) := by
    filter_upwards [hφ.tendsto_atTop.eventually (hball.and hM)] with j ⟨hb, hMj⟩
    exact mem_closedBall_zero_iff.2 (norm_le_of_forall_le_add_inner hr hb hMj (hP j))
  obtain ⟨p, -, ψ, hψ, hPψ⟩ :=
    tendsto_subseq_of_frequently_bounded isBounded_closedBall hPb.frequently
  have hk : Tendsto (φ ∘ ψ) atTop atTop := hφ.tendsto_atTop.comp hψ.tendsto_atTop
  refine ⟨p, hK.mem_of_tendsto hPψ (Eventually.of_forall fun j => hPK (ψ j)), fun y hy =>
    le_of_tendsto_of_tendsto ((hconv y hy).comp hk)
      (((hconv x hx).comp hk).add (hPψ.inner tendsto_const_nhds)) ?_⟩
  filter_upwards [hk.eventually (hmem y hy)] with j hj
  exact hP (ψ j) y hj

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
    x ∈ upperContactSet u Ω :=
  ⟨hx, (exists_mem_forall_le_add_inner_of_frequently isClosed_univ hr hball hmem hM hconv hx
    (hfreq.mono fun _ h => h.2.imp fun p hp => ⟨mem_univ p, hp⟩)).imp fun _ h => h.2⟩

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
  refine (ContinuousLinearMap.isPositive_iff' _).2
    ⟨hu'.isSelfAdjoint_hessianOperator.neg, fun w => ?_⟩
  rw [neg_apply, inner_neg_left, inner_hessianOperator_left, neg_nonneg]
  exact fderiv_fderiv_self_nonpos_of_mem_upperContactSet hΩ hu hy w

variable [FiniteDimensional ℝ E]

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

/-- For a function `C²` on an open set `Ω`, the measure of the gradient image of a measurable
`s ⊆ Ω` is at most the integral of the absolute Hessian determinant over `s`. -/
theorem addHaar_image_gradient_le_lintegral_abs_det_hessianOperator {s : Set E} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hs : MeasurableSet s) (hsΩ : s ⊆ Ω) :
    μ (∇ u '' s) ≤ ∫⁻ y in s, ENNReal.ofReal |(hessianOperator u y).det| ∂μ :=
  addHaar_image_le_lintegral_abs_det_fderiv μ hs fun _ hy =>
    (hu.contDiffAt (hΩ.mem_nhds (hsΩ hy))).hasFDerivAt_gradient.hasFDerivWithinAt

/-- **The Aleksandrov measure estimate for bounded slopes.** Let `Ω` be bounded and open, let `u`
be continuous on `closure Ω` and `C²` in `Ω`, and let `m` bound `u` on `frontier Ω`. For `x ∈ Ω`,
`r ≤ (u x - m) / diam Ω` and every additive Haar measure `μ`, `μ (ball 0 r)` is at most the
integral of `|det D²u|` over the points of the upper contact set at which `‖∇ u‖ < r`. -/
theorem addHaar_ball_le_lintegral_inter_preimage_abs_det_hessianOperator {m r : ℝ}
    (hΩb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω))
    (hu : ContDiffOn ℝ 2 u Ω) (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω)
    (hr : r ≤ (u x - m) / diam Ω) :
    μ (ball 0 r) ≤
      ∫⁻ y in upperContactSet u Ω ∩ ∇ u ⁻¹' ball 0 r,
        ENNReal.ofReal |(hessianOperator u y).det| ∂μ := by
  have hs : MeasurableSet (upperContactSet u Ω ∩ ∇ u ⁻¹' ball 0 r) :=
    (measurableSet_upperContactSet hΩ (hu.of_le (by norm_num))).inter
      (measurable_gradient u measurableSet_ball)
  calc μ (ball 0 r) ≤ μ (∇ u '' (upperContactSet u Ω ∩ ∇ u ⁻¹' ball 0 r)) := by
        rw [image_inter_preimage]
        exact measure_mono (subset_inter ((ball_subset_ball hr).trans
          (ball_subset_image_gradient_upperContactSet hΩb hΩ hcont
            (hu.differentiableOn two_ne_zero) hm hx)) subset_rfl)
    _ ≤ _ := addHaar_image_gradient_le_lintegral_abs_det_hessianOperator μ hΩ hu hs
        (inter_subset_left.trans upperContactSet_subset)

/-- **The Aleksandrov measure estimate** (Gilbarg–Trudinger, Lemma 9.2). Let `Ω` be bounded and
open, let `u` be continuous on `closure Ω` and `C²` in `Ω`, and let `m` bound `u` on
`frontier Ω`. For `x ∈ Ω` and every additive Haar measure `μ`,
`μ (ball 0 ((u x - m) / diam Ω)) ≤ ∫⁻ y in upperContactSet u Ω, |det D²u(y)| ∂μ`. -/
theorem addHaar_ball_le_lintegral_abs_det_hessianOperator {m : ℝ}
    (hΩb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω))
    (hu : ContDiffOn ℝ 2 u Ω) (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω) :
    μ (ball 0 ((u x - m) / diam Ω)) ≤
      ∫⁻ y in upperContactSet u Ω, ENNReal.ofReal |(hessianOperator u y).det| ∂μ :=
  (addHaar_ball_le_lintegral_inter_preimage_abs_det_hessianOperator μ hΩb hΩ hcont hu hm hx
    le_rfl).trans (lintegral_mono_set inter_subset_left)

end PDE

end TauCeti
