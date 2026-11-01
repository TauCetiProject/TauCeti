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
import TauCeti.Topology.MetricSpace.Holder

/-!
# The logit function inverts the sigmoid; derivatives of the sigmoid

Mathlib's `Real.sigmoid` maps `ℝ` increasingly onto `Set.Ioo 0 1`. Its inverse on that interval is
the logit `u ↦ log (u / (1 - u))`. This file records the facts about the pair that are used to
transport the uniform law on the unit interval along the logit: the logit is a right inverse of
the sigmoid, and the logit of a level lies below a point exactly when the level lies below the
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
* `Real.log_div_one_sub_le_iff` — `log (u / (1 - u)) ≤ y ↔ u ≤ sigmoid y` for `0 < u < 1`;
* `Real.measurable_logit_affine` — affine transformations of the logit are measurable;
* `Real.sigmoid_mul_one_sub_sigmoid` — the derivative of the sigmoid is
  `sigmoid y * (1 - sigmoid y) = exp (-y) / (1 + exp (-y)) ^ 2`;
* `Real.exists_iteratedDeriv_sigmoid_eq_eval` — every derivative of the sigmoid is a polynomial
  in the sigmoid;
* `Real.exists_abs_iteratedDeriv_sigmoid_le`, `Real.memHolder_iteratedDeriv_sigmoid` — every
  derivative of the sigmoid is bounded, and Hölder continuous of every exponent `α ≤ 1`;
* `Real.hasDerivAt_log_one_add_exp`, `Real.iteratedDeriv_succ_log_one_add_exp` — the derivatives
  of `x ↦ log (1 + exp x)` of positive order are those of the sigmoid.
-/

public section

namespace Real

/-- The logit `u ↦ log (u / (1 - u))` is a right inverse of the sigmoid on the open unit
interval. -/
@[simp]
theorem sigmoid_log_div_one_sub {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    sigmoid (log (u / (1 - u))) = u := by
  have h1' : 0 < 1 - u := sub_pos.mpr h1
  rw [sigmoid_def, exp_neg, exp_log (div_pos h0 h1'), inv_div]
  field_simp
  ring

/-- The logit is a left inverse of the sigmoid. -/
@[simp]
theorem log_sigmoid_div_one_sub (x : ℝ) :
    log (sigmoid x / (1 - sigmoid x)) = x := by
  apply sigmoid_injective
  exact sigmoid_log_div_one_sub (sigmoid_pos x) (sigmoid_lt_one x)

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
    refine lipschitzWith_of_nnnorm_deriv_le
      (contDiff_sigmoid.differentiable_iteratedDeriv n (WithTop.coe_lt_top _)) fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, ← iteratedDeriv_succ]
    exact (hC₁ x).trans (Real.le_coe_toNNReal C₁)
  have hD (x : ℝ) (_ : x ∈ Set.univ) (y : ℝ) (_ : y ∈ Set.univ) :
      dist (iteratedDeriv n sigmoid x) (iteratedDeriv n sigmoid y) ≤ (2 * C₀).toNNReal := by
    rw [Real.dist_eq]
    linarith [abs_sub (iteratedDeriv n sigmoid x) (iteratedDeriv n sigmoid y), hC₀ x, hC₀ y,
      Real.le_coe_toNNReal (2 * C₀)]
  exact ⟨_, holderOnWith_univ.1
    (((holderWith_one.2 hL).holderOnWith Set.univ).of_le_of_dist_le hD hα one_pos)⟩

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

end Real
