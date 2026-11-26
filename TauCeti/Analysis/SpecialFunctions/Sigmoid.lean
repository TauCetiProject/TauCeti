/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Topology.MetricSpace.Holder

/-!
# The logit function inverts the sigmoid; derivatives of the sigmoid

Mathlib's `Real.sigmoid` maps `ℝ` increasingly onto `Set.Ioo 0 1`. Its inverse on that interval is
the logit `u ↦ log (u / (1 - u))`. This file records the facts about the pair that are used to
transport the uniform law on the unit interval along the logit: the logit is a two-sided inverse
of the sigmoid, and the logit of a level lies below a point exactly when the level lies below the
sigmoid of that point. It also writes the derivative `σ (1 - σ)` of the sigmoid in terms of the
exponential.

The sigmoid is also the derivative of `x ↦ log (1 + exp x)`, the logarithm of the weight
`1 + exp x`. Since `sigmoid' = sigmoid (1 - sigmoid)`, every derivative of the sigmoid is a
polynomial in the sigmoid, hence bounded, and so Hölder continuous of every exponent `α ≤ 1`.
Thus the logarithm of `1 + exp x` has bounded, Hölder continuous derivatives of every positive
order, although it is itself unbounded. This is the hypothesis under which a parabolic equation
for a function growing like `1 + exp x` can be conjugated by that weight into one with bounded
coefficients, as for option prices of linear growth in the spot `exp x`.

## Main results

* `Real.sigmoid_log_div_one_sub` — `sigmoid (log (u / (1 - u))) = u` for `0 < u < 1`;
* `Real.log_sigmoid_div_one_sub` — `log (sigmoid x / (1 - sigmoid x)) = x`;
* `Real.log_div_one_sub_le_iff` — `log (u / (1 - u)) ≤ y ↔ u ≤ sigmoid y` for `0 < u < 1`;
* `Real.measurable_logit_affine` — affine transformations of the logit are measurable;
* `Real.continuousOn_log_div_one_sub`, `Real.tendsto_log_div_one_sub_nhdsGT_zero`,
  `Real.tendsto_log_div_one_sub_nhdsLT_one` — the logit is continuous on the open unit interval
  and tends to `-∞` and `+∞` at its two ends, so a curve `ℝ → X` with limits at `±∞`, read along
  it, extends to a path on the closed unit interval;
* `Real.sigmoid_mul_one_sub_sigmoid` — the derivative of the sigmoid is
  `sigmoid y * (1 - sigmoid y) = exp (-y) / (1 + exp (-y)) ^ 2`;
* `Real.exists_iteratedDeriv_sigmoid_eq_eval` — every derivative of the sigmoid is a polynomial
  in the sigmoid;
* `Real.exists_abs_iteratedDeriv_sigmoid_le`, `Real.memHolder_iteratedDeriv_sigmoid` — every
  derivative of the sigmoid is bounded, and Hölder continuous of every exponent `α ≤ 1`;
* `Real.hasDerivAt_log_one_add_exp`, `Real.iteratedDeriv_succ_log_one_add_exp` — the derivatives
  of `x ↦ log (1 + exp x)` of positive order are those of the sigmoid;
* `Real.four_mul_sigmoid_mul_one_sub_sigmoid_le_one`,
  `Real.abs_four_mul_sigmoid_mul_one_sub_sigmoid_le_one`,
  `Real.hasDerivAt_two_mul_sigmoid_two_mul`, and
  `Real.abs_sqrt_two_mul_sigmoid_two_mul_sub_one_le` — the sharp upper bound
  `4 * sigmoid x * (1 - sigmoid x) ≤ 1`, the derivative of `x ↦ 2 * sigmoid (2 * x)`, and the
  global bound `|√(2 * sigmoid (2 * u)) - 1| ≤ |u|`.
-/

public section

namespace Real

/-- The logit `u ↦ log (u / (1 - u))` is a right inverse of the sigmoid on the open unit
interval. -/
@[simp]
theorem sigmoid_log_div_one_sub {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    sigmoid (log (u / (1 - u))) = u := by
  rw [sigmoid_def, exp_neg, exp_log (div_pos h0 (sub_pos.2 h1))]
  field

/-- The logit is a left inverse of the sigmoid. -/
@[simp]
theorem log_sigmoid_div_one_sub (x : ℝ) :
    log (sigmoid x / (1 - sigmoid x)) = x :=
  sigmoid_injective <| sigmoid_log_div_one_sub (sigmoid_pos x) (sigmoid_lt_one x)

/-- On the open unit interval, the logit of `u` lies below `y` exactly when `u` lies below the
sigmoid of `y`. -/
theorem log_div_one_sub_le_iff {u y : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    log (u / (1 - u)) ≤ y ↔ u ≤ sigmoid y := by
  rw [← sigmoid_le_iff, sigmoid_log_div_one_sub h0 h1]

/-- An affine transformation of the logit is measurable. -/
@[fun_prop]
theorem measurable_logit_affine (m s : ℝ) :
    Measurable fun u : ℝ => m + s * log (u / (1 - u)) := by
  fun_prop

open Filter Set Topology in
/-- The logit `u ↦ log (u / (1 - u))` is continuous on the open unit interval. -/
theorem continuousOn_log_div_one_sub :
    ContinuousOn (fun u : ℝ ↦ log (u / (1 - u))) (Ioo 0 1) :=
  ((continuousOn_id (s := Ioo (0 : ℝ) 1)).div (continuousOn_const.sub continuousOn_id) fun _ hu ↦
    (sub_pos.2 hu.2).ne').log fun _ hu ↦ (div_pos hu.1 (sub_pos.2 hu.2)).ne'

open Filter Set Topology in
/-- The logit `u ↦ log (u / (1 - u))` tends to `-∞` at the left end of the unit interval. -/
theorem tendsto_log_div_one_sub_nhdsGT_zero :
    Tendsto (fun u : ℝ ↦ log (u / (1 - u))) (𝓝[>] 0) atBot := by
  have h : Tendsto (fun u : ℝ ↦ u / (1 - u)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : ContinuousAt (fun u : ℝ ↦ u / (1 - u)) 0 := by fun_prop (disch := norm_num)
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu using div_pos hu.1 (sub_pos.2 hu.2)
  exact tendsto_log_nhdsGT_zero.comp h

open Filter Set Topology in
/-- The logit `u ↦ log (u / (1 - u))` tends to `+∞` at the right end of the unit interval. -/
theorem tendsto_log_div_one_sub_nhdsLT_one :
    Tendsto (fun u : ℝ ↦ log (u / (1 - u))) (𝓝[<] 1) atTop := by
  have h₁ : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝 1) (𝓝 0) := by
        simpa using (continuous_sub_left (1 : ℝ)).tendsto 1
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu using sub_pos.2 hu
  have h₂ : Tendsto (fun u : ℝ ↦ u / (1 - u)) (𝓝[<] 1) atTop :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).pos_mul_atTop one_pos
      (tendsto_inv_nhdsGT_zero.comp h₁)
  exact tendsto_log_atTop.comp h₂

/-- The derivative `sigmoid y * (1 - sigmoid y)` of the sigmoid, written through the
exponential. -/
theorem sigmoid_mul_one_sub_sigmoid (y : ℝ) :
    sigmoid y * (1 - sigmoid y) = exp (-y) / (1 + exp (-y)) ^ 2 := by
  rw [← sigmoid_neg, ← sigmoid_mul_rexp_neg, sigmoid_def]
  field

/-! ### Derivatives of every order -/

open _root_.Polynomial in
/-- Every derivative of the sigmoid is a polynomial in the sigmoid. -/
theorem exists_iteratedDeriv_sigmoid_eq_eval (n : ℕ) :
    ∃ p : ℝ[X], ∀ x, iteratedDeriv n sigmoid x = p.eval (sigmoid x) := by
  induction n with
  | zero => exact ⟨X, fun x => by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨derivative p * (X * (1 - X)), fun x => ?_⟩
    rw [iteratedDeriv_succ, funext hp]
    exact ((p.hasDerivAt (sigmoid x)).comp x (hasDerivAt_sigmoid x)).deriv.trans (by simp)

/-- Every derivative of the sigmoid is bounded. -/
theorem exists_abs_iteratedDeriv_sigmoid_le (n : ℕ) :
    ∃ C, ∀ x, |iteratedDeriv n sigmoid x| ≤ C := by
  obtain ⟨p, hp⟩ := exists_iteratedDeriv_sigmoid_eq_eval n
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (p.differentiable.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  exact ⟨C, fun x => by
    simpa [hp, Real.norm_eq_abs] using hC (sigmoid x) ⟨sigmoid_nonneg x, sigmoid_le_one x⟩⟩

/-- Every derivative of the sigmoid is Hölder continuous of every exponent `α ≤ 1`. -/
theorem memHolder_iteratedDeriv_sigmoid (n : ℕ) {α : NNReal} (hα : α ≤ 1) :
    MemHolder α (iteratedDeriv n sigmoid) := by
  obtain ⟨C₀, hC₀⟩ := exists_abs_iteratedDeriv_sigmoid_le n
  obtain ⟨C₁, hC₁⟩ := exists_abs_iteratedDeriv_sigmoid_le (n + 1)
  have hL : LipschitzWith C₁.toNNReal (iteratedDeriv n sigmoid) := by
    refine lipschitzWith_of_nnNorm_deriv_le
      (contDiff_sigmoid.differentiable_iteratedDeriv n (WithTop.coe_lt_top _)) fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs, ← iteratedDeriv_succ]
    exact (hC₁ x).trans (Real.le_coe_toNNReal C₁)
  refine ⟨_, holderOnWith_univ.1 (hL.lipschitzOnWith.holderOnWith_of_norm_le
    (M := C₀.toNNReal) (fun x _ => ?_) hα)⟩
  rw [Real.norm_eq_abs]
  exact (hC₀ x).trans (Real.le_coe_toNNReal C₀)

/-- The sigmoid is the derivative of `x ↦ log (1 + exp x)`. -/
theorem hasDerivAt_log_one_add_exp (x : ℝ) :
    HasDerivAt (fun x => log (1 + exp x)) (sigmoid x) x := by
  convert ((hasDerivAt_exp x).const_add 1).log (by positivity) using 1
  rw [sigmoid_def, exp_neg]
  field

/-- The sigmoid is the derivative of `x ↦ log (1 + exp x)`. -/
theorem deriv_log_one_add_exp : deriv (fun x => log (1 + exp x)) = sigmoid :=
  funext fun x => (hasDerivAt_log_one_add_exp x).deriv

/-- The derivatives of positive order of `x ↦ log (1 + exp x)` are the derivatives of the
sigmoid. In particular they are bounded and Hölder continuous
(`Real.exists_abs_iteratedDeriv_sigmoid_le`, `Real.memHolder_iteratedDeriv_sigmoid`). -/
theorem iteratedDeriv_succ_log_one_add_exp (n : ℕ) :
    iteratedDeriv (n + 1) (fun x => log (1 + exp x)) = iteratedDeriv n sigmoid := by
  rw [iteratedDeriv_succ', deriv_log_one_add_exp]

/-- Four times the sigmoid derivative `4 * sigmoid x * (1 - sigmoid x)` is at most `1` (attaining
`1` at `x = 0`). -/
theorem four_mul_sigmoid_mul_one_sub_sigmoid_le_one (x : ℝ) :
    4 * sigmoid x * (1 - sigmoid x) ≤ 1 := by
  nlinarith [sq_nonneg (1 - 2 * sigmoid x)]

/-- Four times the sigmoid derivative `4 * sigmoid x * (1 - sigmoid x)` has absolute value at most
`1`. -/
theorem abs_four_mul_sigmoid_mul_one_sub_sigmoid_le_one (x : ℝ) :
    |4 * sigmoid x * (1 - sigmoid x)| ≤ 1 := by
  have h0 : 0 ≤ 4 * sigmoid x * (1 - sigmoid x) :=
    mul_nonneg (mul_nonneg (by norm_num) (sigmoid_nonneg x)) (sub_nonneg.mpr (sigmoid_le_one x))
  rw [abs_of_nonneg h0]
  exact four_mul_sigmoid_mul_one_sub_sigmoid_le_one x

/-- The derivative of `x ↦ 2 * sigmoid (2 * x)` at `u` is
`4 * sigmoid (2 * u) * (1 - sigmoid (2 * u))`, taking value `1` at `u = 0`. -/
theorem hasDerivAt_two_mul_sigmoid_two_mul (u : ℝ) :
    HasDerivAt (fun x ↦ 2 * sigmoid (2 * x))
      (4 * sigmoid (2 * u) * (1 - sigmoid (2 * u))) u :=
  (((hasDerivAt_sigmoid (2 * u)).comp u ((hasDerivAt_id u).const_mul 2)).const_mul
    2).congr_deriv (by ring)

/-- For every real `u`, `|√(2 * sigmoid (2 * u)) - 1| ≤ |u|`. -/
theorem abs_sqrt_two_mul_sigmoid_two_mul_sub_one_le (u : ℝ) :
    |sqrt (2 * sigmoid (2 * u)) - 1| ≤ |u| := by
  refine (abs_sqrt_sub_one_le_abs_sub_one _).trans ?_
  have hd : ∀ y ∈ Set.univ, DifferentiableAt ℝ (fun x ↦ 2 * sigmoid (2 * x)) y :=
    fun y _ ↦ (hasDerivAt_two_mul_sigmoid_two_mul y).differentiableAt
  have hb : ∀ y ∈ Set.univ, ‖deriv (fun x ↦ 2 * sigmoid (2 * x)) y‖ ≤ 1 := fun y _ ↦ by
    rw [(hasDerivAt_two_mul_sigmoid_two_mul y).deriv, norm_eq_abs]
    exact abs_four_mul_sigmoid_mul_one_sub_sigmoid_le_one (2 * y)
  simpa [norm_eq_abs] using
    convex_univ.norm_image_sub_le_of_norm_deriv_le hd hb (Set.mem_univ 0) (Set.mem_univ u)

end Real
