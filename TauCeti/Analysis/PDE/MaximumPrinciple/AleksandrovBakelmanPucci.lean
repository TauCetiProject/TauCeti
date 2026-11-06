/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Convex.SubgradientImage
import TauCeti.Analysis.Matrix.PosSemidef.Determinant

/-!
# The Aleksandrov–Bakelman–Pucci estimate for classical solutions

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space `E` of
dimension `n`, and let `u` be continuous on the closure of `Ω` and `C²` in `Ω`. The
**upper contact set** of `u` is the set `Γ⁺` of points `y ∈ Ω` at which some affine function
`x ↦ u y + ⟪p, x - y⟫` lies above `u` on all of `Ω` (`TauCeti.PDE.upperContactSet`). There the
slope `p` is the gradient `∇u(y)` and the Hessian of `u` is negative semidefinite.

The Aleksandrov–Bakelman–Pucci estimate bounds `u` by its boundary values and by an integral of
the Hessian over `Γ⁺` only. It is the maximum-principle input of the Krylov–Safonov theory of
non-divergence-form equations with measurable coefficients, where no continuity of the
coefficients is available and the classical maximum principle gives no quantitative control.

* If `u ≤ m` on the frontier of `Ω` and `x₀ ∈ Ω`, every `p` with `‖p‖ diam Ω ≤ u x₀ - m` is the
  gradient of `u` at a point of `Γ⁺`: lower the hyperplanes of slope `p` onto the graph of `u`
  over the compact closure of `Ω`; they first touch it over a point of `Ω`
  (`TauCeti.PDE.closedBall_subset_image_gradient_upperContactSet`, through
  `TauCeti.exists_forall_add_inner_le_of_forall_frontier` applied to `-u`).
* The gradient map is `C¹` on `Γ⁺`, so the measure of `∇u(Γ⁺)` is at most `∫_{Γ⁺} |det D²u|`
  (`TauCeti.PDE.addHaar_image_gradient_upperContactSet_le`, an application of
  `MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv`).
* Together, for every additive Haar measure `μ` (`TauCeti.PDE.ofReal_sub_pow_mul_addHaar_ball_le`):

  `(u x₀ - m)⁺ ^ n μ(B₁) ≤ (diam Ω) ^ n ∫_{Γ⁺} |det D²u| dμ`.

For the operator `L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu` on `ℝⁿ = EuclideanSpace ℝ ι` with positive-definite
coefficient matrices `a(y)`, the determinant-trace inequality
`det a · det (-D²u) ≤ (tr (a (-D²u)) / n) ^ n`
(`Matrix.PosSemidef.det_mul_det_le_trace_mul_div_card_pow`) bounds `|det D²u|` on `Γ⁺` by
`(f⁻) ^ n / (nⁿ det a)` whenever `f ≤ L u`. This gives the
Aleksandrov–Bakelman–Pucci estimate for classical subsolutions
(`TauCeti.PDE.ofReal_sub_pow_mul_addHaar_ball_le_of_le_sum_mul_fderiv_fderiv`):

`(u x₀ - m)⁺ ^ n μ(B₁) ≤ (diam Ω) ^ n ∫_{Γ⁺} (f⁻) ^ n / (nⁿ det a) dμ`,

that is, for `n ≥ 1`,
`sup_Ω u ≤ sup_{∂Ω} u + diam Ω / (n μ(B₁)^{1/n}) ‖f⁻ / (det a)^{1/n}‖_{Lⁿ(Γ⁺)}`. Neither `a` nor `f`
needs any regularity or measurability, and both enter only through their values on `Γ⁺`.

## Main declarations

* `TauCeti.PDE.upperContactSet`: the upper contact set `Γ⁺` of `u` on `Ω`.
* `TauCeti.PDE.gradient_eq_of_forall_le`: the slope of a touching affine function is the gradient.
* `TauCeti.PDE.mem_upperContactSet_iff_of_differentiableAt`: membership in `Γ⁺` through the
  tangent hyperplane.
* `TauCeti.PDE.measurableSet_upperContactSet`: `Γ⁺` is measurable for `C¹` functions.
* `TauCeti.PDE.fderiv_fderiv_self_nonpos_of_mem_upperContactSet`: the Hessian is negative
  semidefinite on `Γ⁺`.
* `TauCeti.PDE.closedBall_subset_image_gradient_upperContactSet`: the gradient image of `Γ⁺`
  contains the closed ball of radius `(u x₀ - m) / diam Ω`.
* `TauCeti.PDE.addHaar_image_gradient_upperContactSet_le`: the Jacobian bound for `∇u(Γ⁺)`.
* `TauCeti.PDE.ofReal_sub_pow_mul_addHaar_ball_le`: the geometric form of the estimate.
* `TauCeti.PDE.ofReal_sub_pow_mul_addHaar_ball_le_of_le_sum_mul_fderiv_fderiv`: **the
  Aleksandrov–Bakelman–Pucci estimate** for classical subsolutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.1, Lemma 9.2 and Theorem 9.1.
-/

public section

noncomputable section

namespace TauCeti.PDE

open MeasureTheory Set Filter Metric Module InnerProductSpace
open scoped Topology ENNReal Gradient RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Set E} {u : E → ℝ}
  {x₀ y p : E} {m : ℝ}

/-! ### The upper contact set -/

/-- The **upper contact set** `Γ⁺` of `u` on `Ω`: the points `y ∈ Ω` at which some affine function
`x ↦ u y + ⟪p, x - y⟫` lies above `u` on all of `Ω`, touching it at `y`. Where `u` is
differentiable the slope `p` is the gradient of `u`
(`TauCeti.PDE.mem_upperContactSet_iff_of_differentiableAt`); where `u` is `C²` the Hessian is
negative semidefinite (`TauCeti.PDE.fderiv_fderiv_self_nonpos_of_mem_upperContactSet`). -/
def upperContactSet (Ω : Set E) (u : E → ℝ) : Set E :=
  {y | y ∈ Ω ∧ ∃ p : E, ∀ x ∈ Ω, u x ≤ u y + ⟪p, x - y⟫}

@[simp]
theorem mem_upperContactSet :
    y ∈ upperContactSet Ω u ↔ y ∈ Ω ∧ ∃ p : E, ∀ x ∈ Ω, u x ≤ u y + ⟪p, x - y⟫ :=
  Iff.rfl

theorem upperContactSet_subset (Ω : Set E) (u : E → ℝ) : upperContactSet Ω u ⊆ Ω :=
  fun _ hy => hy.1

/-- If the affine function `x ↦ u y + ⟪p, x - y⟫` lies above `u` on a neighbourhood of `y`, then
`u` minus its linear part `⟪p, ·⟫` has a local maximum at `y`. -/
private theorem isLocalMax_sub_innerSL (hΩ : Ω ∈ 𝓝 y) (hp : ∀ x ∈ Ω, u x ≤ u y + ⟪p, x - y⟫) :
    IsLocalMax (fun x => u x - innerSL ℝ p x) y :=
  mem_of_superset hΩ fun x hx => by
    have := hp x hx
    simp only [mem_ofPred_eq, innerSL_apply_apply, inner_sub_right] at this ⊢
    linarith

/-- If the affine function `x ↦ u y + ⟪p, x - y⟫` lies above `u` on a neighbourhood `Ω` of `y`
and `u` is differentiable at `y`, then `p` is the gradient of `u` at `y`. -/
theorem gradient_eq_of_forall_le [CompleteSpace E] (hΩ : Ω ∈ 𝓝 y) (hu : DifferentiableAt ℝ u y)
    (hp : ∀ x ∈ Ω, u x ≤ u y + ⟪p, x - y⟫) : ∇ u y = p := by
  have h0 : fderiv ℝ u y = innerSL ℝ p := sub_eq_zero.1 <|
    (isLocalMax_sub_innerSL hΩ hp).hasFDerivAt_eq_zero
      (hu.hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt)
  refine (hasGradientAt_iff_hasFDerivAt.2 (hu.hasFDerivAt.congr_fderiv ?_)).gradient
  rw [h0]
  ext x
  simp

/-- Where `u` is differentiable, a point of `Ω` is in the upper contact set exactly when the
tangent hyperplane of `u` there lies above `u` on `Ω`. -/
theorem mem_upperContactSet_iff_of_differentiableAt [CompleteSpace E] (hΩ : IsOpen Ω)
    (hu : DifferentiableAt ℝ u y) :
    y ∈ upperContactSet Ω u ↔ y ∈ Ω ∧ ∀ x ∈ Ω, u x ≤ u y + ⟪∇ u y, x - y⟫ := by
  refine ⟨fun ⟨hy, p, hp⟩ => ⟨hy, ?_⟩, fun ⟨hy, h⟩ => ⟨hy, _, h⟩⟩
  rwa [gradient_eq_of_forall_le (hΩ.mem_nhds hy) hu hp]

/-- The upper contact set of a `C¹` function on an open set is measurable: it is relatively closed
in `Ω`. -/
theorem measurableSet_upperContactSet [CompleteSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) :
    MeasurableSet (upperContactSet Ω u) := by
  have hg : ContinuousOn (∇ u) Ω :=
    (toDual ℝ E).symm.continuous.comp_continuousOn (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl)
  have hd (y) (hy : y ∈ Ω) : DifferentiableAt ℝ u y :=
    (hu.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)
  -- The complement of `Γ⁺` in `Ω` is the open set of points whose tangent hyperplane passes
  -- strictly below the graph of `u` somewhere in `Ω`.
  set U := ⋃ x ∈ Ω, Ω ∩ (fun y => u y + ⟪∇ u y, x - y⟫ - u x) ⁻¹' Iio 0
  have hU : IsOpen U := isOpen_biUnion fun x _ =>
    ((hu.continuousOn.add (hg.inner (continuousOn_const.sub continuousOn_id))).sub
      continuousOn_const).isOpen_inter_preimage hΩ isOpen_Iio
  have hΓ : upperContactSet Ω u = Ω \ U := by
    ext y
    simp only [U, Set.mem_sdiff, mem_iUnion, mem_inter_iff, mem_preimage, mem_Iio, sub_neg,
      exists_prop, not_exists, not_and, not_lt]
    refine ⟨fun hy => ⟨hy.1, fun x hx _ => ?_⟩, fun ⟨hy, h⟩ => ?_⟩
    · exact ((mem_upperContactSet_iff_of_differentiableAt hΩ (hd y hy.1)).1 hy).2 x hx
    · exact (mem_upperContactSet_iff_of_differentiableAt hΩ (hd y hy)).2
        ⟨hy, fun x hx => h x hx hy⟩
  rw [hΓ]
  exact hΩ.measurableSet.diff hU.measurableSet

/-- **On the upper contact set the Hessian is negative semidefinite**: if `u` is `C²` at a point
`y` of the upper contact set of `u` on an open set, then `D²u(y) v v ≤ 0` for every `v`. -/
theorem fderiv_fderiv_self_nonpos_of_mem_upperContactSet (hΩ : IsOpen Ω)
    (hu : ContDiffAt ℝ 2 u y) (hy : y ∈ upperContactSet Ω u) (v : E) :
    fderiv ℝ (fderiv ℝ u) y v v ≤ 0 := by
  obtain ⟨hyΩ, p, hp⟩ := hy
  -- `u` minus the touching affine function has a local maximum at `y`, and the same Hessian.
  have hmax := isLocalMax_sub_innerSL (hΩ.mem_nhds hyΩ) hp
  have h := fderiv_fderiv_self_nonpos_of_isLocalMax (hu.sub (innerSL ℝ p).contDiff.contDiffAt)
    hmax v
  have heq : fderiv ℝ (fun x => u x - innerSL ℝ p x) =ᶠ[𝓝 y]
      fun x => fderiv ℝ u x - innerSL ℝ p := by
    have hev : ∀ᶠ x in 𝓝 y, ContDiffAt ℝ 2 u x := hu.eventually (by simp)
    filter_upwards [hev] with x hx
    exact ((hx.differentiableAt (by simp)).hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt).fderiv
  rwa [heq.fderiv_eq, fderiv_sub_const] at h

/-! ### The gradient image of the upper contact set -/

/-- **The gradient image of the upper contact set contains a ball.** Let `Ω` be bounded and open,
`u` continuous on its closure and differentiable in `Ω`, with `u ≤ m` on the frontier of `Ω`. If
`x₀ ∈ Ω` and `r diam Ω ≤ u x₀ - m`, then every `p` with `‖p‖ ≤ r` is the gradient of `u` at a
point of the upper contact set. -/
theorem closedBall_subset_image_gradient_upperContactSet [FiniteDimensional ℝ E] (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContinuousOn u (closure Ω)) (hd : DifferentiableOn ℝ u Ω)
    (hm : ∀ y ∈ frontier Ω, u y ≤ m) (hx₀ : x₀ ∈ Ω) {r : ℝ} (hr : r * diam Ω ≤ u x₀ - m) :
    closedBall 0 r ⊆ ∇ u '' upperContactSet Ω u := by
  intro p hp
  rw [mem_closedBall_zero_iff] at hp
  -- On the frontier, `u` lies below the affine function through `(x₀, u x₀)` of slope `p`, so
  -- `-p` is a subgradient of `-u` relative to `Ω` at some point `y ∈ Ω`.
  have hfr (x) (hx : x ∈ frontier Ω) : -u x₀ + ⟪x - x₀, -p⟫ ≤ -u x := by
    have hdist : ‖x - x₀‖ ≤ diam Ω := by
      rw [← dist_eq_norm, ← diam_closure]
      exact dist_le_diam_of_mem hb.closure (frontier_subset_closure hx) (subset_closure hx₀)
    have h₁ : -⟪x - x₀, p⟫ ≤ r * diam Ω :=
      calc -⟪x - x₀, p⟫ ≤ ‖x - x₀‖ * ‖p‖ := (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
        _ ≤ diam Ω * r := mul_le_mul hdist hp (norm_nonneg p) diam_nonneg
        _ = r * diam Ω := mul_comm _ _
    rw [inner_neg_right]
    linarith [hm x hx]
  obtain ⟨y, hyΩ, hy⟩ := exists_forall_add_inner_le_of_forall_frontier hb.isCompact_closure
    hu.neg hx₀ hfr
  have hsupp (x) (hx : x ∈ Ω) : u x ≤ u y + ⟪p, x - y⟫ := by
    have := hy x hx
    simp only [Pi.neg_apply, inner_neg_right] at this
    linarith [real_inner_comm p (x - y)]
  exact ⟨y, ⟨hyΩ, p, hsupp⟩,
    gradient_eq_of_forall_le (hΩ.mem_nhds hyΩ) (hd.differentiableAt (hΩ.mem_nhds hyΩ)) hsupp⟩

section Haar

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- **The Jacobian bound for the gradient image of the upper contact set.** For `u` of class `C²`
on an open set `Ω`, the measure of `∇u(Γ⁺)` is at most the integral of `|det D(∇u)|` over `Γ⁺`. -/
theorem addHaar_image_gradient_upperContactSet_le (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) :
    μ (∇ u '' upperContactSet Ω u) ≤
      ∫⁻ y in upperContactSet Ω u, ENNReal.ofReal |(fderiv ℝ (∇ u) y).det| ∂μ := by
  refine addHaar_image_le_lintegral_abs_det_fderiv μ
    (measurableSet_upperContactSet hΩ (hu.of_le (by norm_num))) fun y hy => ?_
  have hy' : ContDiffAt ℝ 2 u y := hu.contDiffAt (hΩ.mem_nhds hy.1)
  exact ((hy'.gradient_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
    |>.hasFDerivWithinAt

/-- **The Aleksandrov–Bakelman–Pucci estimate, geometric form.** Let `Ω` be bounded and open in
a space of dimension `n`, and `u` continuous on the closure of `Ω`, `C²` in `Ω`, with `u ≤ m` on
the frontier. For `x₀ ∈ Ω`,

`(u x₀ - m)⁺ ^ n μ(B₁) ≤ (diam Ω) ^ n ∫_{Γ⁺} |det D(∇u)| dμ`,

where `Γ⁺` is the upper contact set of `u` on `Ω` and `B₁` the unit ball. -/
theorem ofReal_sub_pow_mul_addHaar_ball_le (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hu : ContinuousOn u (closure Ω)) (hu₂ : ContDiffOn ℝ 2 u Ω)
    (hm : ∀ y ∈ frontier Ω, u y ≤ m) (hx₀ : x₀ ∈ Ω) :
    ENNReal.ofReal (u x₀ - m) ^ finrank ℝ E * μ (ball 0 1) ≤
      ENNReal.ofReal (diam Ω) ^ finrank ℝ E *
        ∫⁻ y in upperContactSet Ω u, ENNReal.ofReal |(fderiv ℝ (∇ u) y).det| ∂μ := by
  have hJ := addHaar_image_gradient_upperContactSet_le μ hΩ hu₂
  have hd : DifferentiableOn ℝ u Ω := hu₂.differentiableOn (by norm_num)
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In dimension zero the gradient image of the nonempty set `Γ⁺ ∋ x₀` is everything.
    have hx₀Γ : x₀ ∈ upperContactSet Ω u :=
      ⟨hx₀, 0, fun x _ => by rw [Subsingleton.elim x x₀]; simp⟩
    have hball : ball (0 : E) 1 ⊆ ∇ u '' upperContactSet Ω u := fun p _ =>
      ⟨x₀, hx₀Γ, Subsingleton.elim _ _⟩
    simp only [finrank_zero_of_subsingleton, pow_zero, one_mul]
    exact (measure_mono hball).trans hJ
  by_cases hux : u x₀ ≤ m
  · rw [ENNReal.ofReal_of_nonpos (sub_nonpos.2 hux), zero_pow finrank_pos.ne', zero_mul]
    positivity
  -- Otherwise the gradient image contains the ball of radius `r = (u x₀ - m) / diam Ω`.
  have hdiam : 0 < diam Ω := diam_pos (infinite_of_mem_nhds x₀ (hΩ.mem_nhds hx₀)).nontrivial hb
  set r := (u x₀ - m) / diam Ω
  have hr : 0 < r := div_pos (by linarith) hdiam
  have hball := ball_subset_closedBall.trans <|
    closedBall_subset_image_gradient_upperContactSet hΩ hb hu hd hm hx₀ (r := r)
      (by rw [div_mul_cancel₀ _ hdiam.ne'])
  have hsplit : ENNReal.ofReal (u x₀ - m) ^ finrank ℝ E =
      ENNReal.ofReal (diam Ω) ^ finrank ℝ E * ENNReal.ofReal (r ^ finrank ℝ E) := by
    rw [ENNReal.ofReal_pow hr.le, ← mul_pow, ← ENNReal.ofReal_mul hdiam.le,
      mul_div_cancel₀ _ hdiam.ne']
  calc ENNReal.ofReal (u x₀ - m) ^ finrank ℝ E * μ (ball 0 1)
      = ENNReal.ofReal (diam Ω) ^ finrank ℝ E * μ (ball 0 r) := by
        rw [hsplit, Measure.addHaar_ball_of_pos μ 0 hr, mul_assoc]
    _ ≤ _ := mul_le_mul_right ((measure_mono hball).trans hJ) _

end Haar

/-! ### Non-divergence-form operators -/

section NonDivergence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (μ : Measure (EuclideanSpace ℝ ι)) [μ.IsAddHaarMeasure]
  {Ω : Set (EuclideanSpace ℝ ι)} {u f : EuclideanSpace ℝ ι → ℝ}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {x₀ y : EuclideanSpace ℝ ι} {m : ℝ}

/-- The pointwise bound behind the Aleksandrov–Bakelman–Pucci estimate: at a point of the upper
contact set where `f ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu` with `a` positive definite,
`|det D(∇u)| ≤ (f⁻) ^ n / (nⁿ det a)`. -/
private theorem abs_det_fderiv_gradient_le (hΩ : IsOpen Ω) (hu : ContDiffAt ℝ 2 u y)
    (hy : y ∈ upperContactSet Ω u) (ha : (a y).PosDef)
    (hf : f y ≤ ∑ i, ∑ j, a y i j *
      fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) :
    |(fderiv ℝ (∇ u) y).det| ≤
      max (-f y) 0 ^ Fintype.card ι / (Fintype.card ι ^ Fintype.card ι * (a y).det) := by
  set T := fderiv ℝ (∇ u) y
  set b := EuclideanSpace.basisFun ι ℝ
  set H := LinearMap.toMatrix b.toBasis b.toBasis (T : EuclideanSpace ℝ ι →ₗ[ℝ] _)
  set N := Fintype.card ι
  -- The matrix of `T` is the Hessian matrix, transposed.
  have hH (i j : ι) : H i j =
      fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
    simpa [H, b, T, fderiv_gradient] using b.toMatrix_hessianOperator_apply u y i j
  -- The negated Hessian `B = -H` is positive semidefinite.
  have hsymm : (T : EuclideanSpace ℝ ι →ₗ[ℝ] _).IsSymmetric := by
    simpa [T, fderiv_gradient] using hu.isSelfAdjoint_hessianOperator.isSymmetric
  have hB : (-H).PosSemidef := by
    have hpos : (-(T : EuclideanSpace ℝ ι →ₗ[ℝ] _)).IsPositive := by
      refine ⟨fun v w => ?_, fun v => ?_⟩
      · simp only [LinearMap.neg_apply, inner_neg_left, inner_neg_right, neg_inj]
        exact hsymm v w
      · simpa [fderiv_gradient, T] using
          fderiv_fderiv_self_nonpos_of_mem_upperContactSet hΩ hu hy v
    simpa [H, map_neg] using (LinearMap.posSemidef_toMatrix_iff b).2 hpos
  -- `tr (a B) = -L u ≤ f⁻`.
  have htr : (a y * -H).trace ≤ max (-f y) 0 := by
    have : (a y * -H).trace = -∑ i, ∑ j, a y i j *
        fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
      simp [Matrix.trace, Matrix.mul_apply, hH, Finset.sum_neg_distrib]
    rw [this]
    exact (neg_le_neg hf).trans (le_max_left _ _)
  -- `|det T| = det B ≤ (tr (a B) / n) ^ n / det a ≤ (f⁻ / n) ^ n / det a`.
  have hdet : |T.det| = (-H).det := by
    have hTH : T.det = H.det := (LinearMap.det_toMatrix b.toBasis _).symm
    rw [hTH, ← abs_of_nonneg hB.det_nonneg, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul]
  rw [hdet, ← div_div, ← div_pow, le_div_iff₀ ha.det_pos, mul_comm]
  calc (a y).det * (-H).det ≤ ((a y * -H).trace / N) ^ N :=
        ha.posSemidef.det_mul_det_le_trace_mul_div_card_pow hB
    _ ≤ (max (-f y) 0 / N) ^ N :=
        pow_le_pow_left₀ (div_nonneg (ha.posSemidef.trace_mul_nonneg hB) (Nat.cast_nonneg _))
          (div_le_div_of_nonneg_right htr (Nat.cast_nonneg _)) N

/-- **The Aleksandrov–Bakelman–Pucci estimate** for classical subsolutions of a non-divergence-form
operator. Let `Ω ⊆ ℝⁿ` be bounded and open, `u` continuous on the closure of `Ω` and `C²` in `Ω`,
with `u ≤ m` on the frontier, and let `Γ⁺` be the upper contact set of `u` on `Ω`. If at every
point of `Γ⁺` (in particular, if at every point of `Ω`) the matrix `a(y)` is positive definite and
`f ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu`, then for `x₀ ∈ Ω` and every additive Haar measure `μ`,

`(u x₀ - m)⁺ ^ n μ(B₁) ≤ (diam Ω) ^ n ∫_{Γ⁺} (f⁻) ^ n / (nⁿ det a) dμ`,

where `B₁` is the unit ball and `f⁻ = max (-f) 0`. For `n ≥ 1` this is
`u x₀ ≤ m + diam Ω / (n μ(B₁)^{1/n}) ‖f⁻ / (det a)^{1/n}‖_{Lⁿ(Γ⁺)}`. Neither `a` nor `f` needs
any regularity. -/
theorem ofReal_sub_pow_mul_addHaar_ball_le_of_le_sum_mul_fderiv_fderiv (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContinuousOn u (closure Ω)) (hu₂ : ContDiffOn ℝ 2 u Ω)
    (ha : ∀ y ∈ upperContactSet Ω u, (a y).PosDef)
    (hf : ∀ y ∈ upperContactSet Ω u, f y ≤ ∑ i, ∑ j, a y i j *
      fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (hm : ∀ y ∈ frontier Ω, u y ≤ m) (hx₀ : x₀ ∈ Ω) :
    ENNReal.ofReal (u x₀ - m) ^ Fintype.card ι * μ (ball 0 1) ≤
      ENNReal.ofReal (diam Ω) ^ Fintype.card ι * ∫⁻ y in upperContactSet Ω u,
        ENNReal.ofReal (max (-f y) 0 ^ Fintype.card ι /
          (Fintype.card ι ^ Fintype.card ι * (a y).det)) ∂μ := by
  have h := ofReal_sub_pow_mul_addHaar_ball_le μ hΩ hb hu hu₂ hm hx₀
  rw [finrank_euclideanSpace] at h
  refine h.trans (mul_le_mul_right (setLIntegral_mono'
    (measurableSet_upperContactSet hΩ (hu₂.of_le (by norm_num))) fun y hy =>
      ENNReal.ofReal_le_ofReal ?_) _)
  exact abs_det_fderiv_gradient_le hΩ (hu₂.contDiffAt (hΩ.mem_nhds hy.1)) hy (ha y hy) (hf y hy)

end NonDivergence

end TauCeti.PDE
