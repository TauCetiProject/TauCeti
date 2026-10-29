/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Exponential multipliers and positive inverses of real bounded continuous functions

For a real bounded continuous function `m`, `m.expNegMul t` is the exponential multiplier
`x ↦ exp (-(t * m x))`. Its norm for nonnegative `t` is controlled by the negative part of `m`.
The same lower bound gives a bounded continuous inverse `m.addInv c hc` of `x ↦ c + m x`
when `hc : ‖m⁻‖ < c`, together with its explicit norm estimate.

These constructions provide pointwise multipliers without importing operator semigroup theory.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction
open NormedSpace

namespace BoundedContinuousFunction

variable {α : Type*} [TopologicalSpace α]

/-- Evaluation of the Banach-algebra exponential of a bounded continuous real function. -/
@[simp]
theorem exp_apply (g : α →ᵇ ℝ) (x : α) : (exp g) x = Real.exp (g x) := by
  let +nondep : NormedAlgebra ℚ (α →ᵇ ℝ) := .restrictScalars ℚ ℝ _
  let ev :=
    (ContinuousMap.evalAlgHom (S := ℝ) (R := ℝ) x).comp
      (BoundedContinuousFunction.toContinuousMapₐ ℝ)
  rw [Real.exp_eq_exp_ℝ]
  -- The algebra homomorphism `ev` and `evalCLM x` have definitionally equal coercions.
  exact map_exp ev (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) x).continuous g

/-- The exponential multiplier `x ↦ exp (-(t * m x))` as a bounded continuous function. -/
def expNegMul (m : α →ᵇ ℝ) (t : ℝ) : α →ᵇ ℝ :=
  exp (t • (-m))

/-- The exponential multiplier is the Banach-algebra exponential of `t • (-m)`. -/
theorem expNegMul_def (m : α →ᵇ ℝ) (t : ℝ) :
    m.expNegMul t = exp (t • (-m)) :=
  (rfl)

/-- The coercion of `m.expNegMul t` is `x ↦ exp (-(t * m x))`. -/
@[simp]
theorem coe_expNegMul (m : α →ᵇ ℝ) (t : ℝ) :
    ⇑(m.expNegMul t) = fun x => Real.exp (-(t * m x)) := by
  ext x
  simp [expNegMul_def, smul_eq_mul]

/-- A real bounded continuous function is bounded below by the negative of the norm of
its negative part. -/
theorem neg_norm_negPart_le_apply (m : α →ᵇ ℝ) (x : α) :
    -‖m⁻‖ ≤ m x := by
  have h : (m x)⁻ ≤ ‖m⁻‖ := by simpa using (m⁻).apply_le_norm x
  linarith [neg_le_negPart (m x)]

/-- For `t ≥ 0`, the exponential multiplier has norm at most `exp (t * ‖m⁻‖)`. -/
theorem norm_expNegMul_le (m : α →ᵇ ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖m.expNegMul t‖ ≤ Real.exp (t * ‖m⁻‖) := by
  refine (norm_le (by positivity)).mpr fun x => ?_
  simp only [coe_expNegMul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  have hx := m.neg_norm_negPart_le_apply x
  nlinarith

/-- A positive scalar perturbation of `m` is pointwise positive whenever `‖m⁻‖ < c`. -/
theorem add_pos_of_norm_negPart_lt (m : α →ᵇ ℝ) {c : ℝ} (hc : ‖m⁻‖ < c) (x : α) :
    0 < c + m x := by
  linarith [m.neg_norm_negPart_le_apply x]

/-- The pointwise inverse `(c + m)⁻¹` of a positive perturbation of a bounded continuous
multiplier, as bounded continuous function.  The hypothesis `‖m⁻‖ < c` guarantees
`c + m x ≥ c - ‖m⁻‖ > 0` for every `x`. -/
def addInv (m : α →ᵇ ℝ) (c : ℝ) (hc : ‖m⁻‖ < c) : α →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (c + m x)⁻¹)
    (by
      refine Continuous.inv₀ (continuous_const.add m.continuous) fun x => ?_
      exact ne_of_gt (m.add_pos_of_norm_negPart_lt hc x))
    (1 / (c - ‖m⁻‖)) fun x => by
      have hge : c - ‖m⁻‖ ≤ c + m x := by linarith [m.neg_norm_negPart_le_apply x]
      have hpos : (0 : ℝ) < c - ‖m⁻‖ := by linarith
      have hxpos : (0 : ℝ) < c + m x := m.add_pos_of_norm_negPart_lt hc x
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos hxpos, inv_eq_one_div]
      exact one_div_le_one_div_of_le hpos hge

/-- The coercion of `addInv m c hc` is the function `x ↦ (c + m x)⁻¹`. -/
@[simp]
theorem coe_addInv (m : α →ᵇ ℝ) (c : ℝ) (hc : ‖m⁻‖ < c) :
    ⇑(addInv m c hc) = fun x => (c + m x)⁻¹ :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _

/-- The pointwise inverse `(c + m)⁻¹` has norm at most `1 / (c - ‖m⁻‖)`. -/
theorem norm_addInv_le (m : α →ᵇ ℝ) (c : ℝ) (hc : ‖m⁻‖ < c) :
    ‖addInv m c hc‖ ≤ 1 / (c - ‖m⁻‖) :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

end BoundedContinuousFunction
