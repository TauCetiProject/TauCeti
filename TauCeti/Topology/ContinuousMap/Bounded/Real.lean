/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.Topology.ContinuousMap.Bounded.Exponential

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
  simp [expNegMul_def, Real.exp_eq_exp_ℝ]

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
  rw [coe_expNegMul, Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
  nlinarith [m.neg_norm_negPart_le_apply x]

/-- A positive scalar perturbation of `m` is pointwise positive whenever `‖m⁻‖ < c`. -/
theorem add_pos_of_norm_negPart_lt (m : α →ᵇ ℝ) {c : ℝ} (hc : ‖m⁻‖ < c) (x : α) :
    0 < c + m x := by
  linarith [m.neg_norm_negPart_le_apply x]

/-- The pointwise inverse `(c + m)⁻¹` of a positive perturbation of a bounded continuous
multiplier, as a bounded continuous function.  The hypothesis `‖m⁻‖ < c` guarantees
`c + m x ≥ c - ‖m⁻‖ > 0` for every `x`. -/
def addInv (m : α →ᵇ ℝ) (c : ℝ) (hc : ‖m⁻‖ < c) : α →ᵇ ℝ :=
  ofNormedAddCommGroup (fun x => (c + m x)⁻¹)
    ((continuous_const.add m.continuous).inv₀ fun x => (m.add_pos_of_norm_negPart_lt hc x).ne')
    (c - ‖m⁻‖)⁻¹ fun x => by
      rw [norm_inv, Real.norm_of_nonneg (m.add_pos_of_norm_negPart_lt hc x).le]
      exact inv_anti₀ (sub_pos.mpr hc) (by linarith [m.neg_norm_negPart_le_apply x])

/-- The coercion of `m.addInv c hc` is the function `x ↦ (c + m x)⁻¹`. -/
@[simp]
theorem coe_addInv (m : α →ᵇ ℝ) (c : ℝ) (hc : ‖m⁻‖ < c) :
    ⇑(m.addInv c hc) = fun x => (c + m x)⁻¹ :=
  coe_ofNormedAddCommGroup _ _ _ _

/-- The pointwise inverse `(c + m)⁻¹` has norm at most `(c - ‖m⁻‖)⁻¹`. -/
theorem norm_addInv_le (m : α →ᵇ ℝ) (c : ℝ) (hc : ‖m⁻‖ < c) :
    ‖m.addInv c hc‖ ≤ (c - ‖m⁻‖)⁻¹ :=
  norm_ofNormedAddCommGroup_le _ (inv_nonneg.mpr (sub_pos.mpr hc).le) _

end BoundedContinuousFunction
