/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Contractions of iterated gradients

An iterated gradient has continuous-linear direction slots outside a final vector. Partial
contraction evaluates a specified number of the outer slots at a repeated direction. Full
contraction evaluates all those slots and pairs the remaining vector with that direction.
These operations turn derivative fields into the directional expressions used in Taylor
polynomials, without choosing coordinates.

Both operations are continuous linear in the field. Partial contraction of `i` slots is
homogeneous of degree `i` in the direction and has norm at most `‖h‖ ^ i`; full contraction of
`IteratedGradient E j` has degree `j + 1` and norm at most `‖h‖ ^ (j + 1)`.
-/

public section

noncomputable section

namespace TauCeti.IteratedGradient

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluate the `i` outermost slots of an iterated gradient at `h`, leaving an iterated
gradient of index `j`. In particular, contracting zero slots is the identity. -/
def contractL (j : ℕ) : (i : ℕ) → E →
    IteratedGradient E (j + i) →L[ℝ] IteratedGradient E j
  | 0, _ => ContinuousLinearMap.id ℝ _
  | i + 1, h => (contractL j i h).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E (j + i)) h)

@[simp]
theorem contractL_zero (j : ℕ) (h : E) :
    contractL j 0 h = ContinuousLinearMap.id ℝ (IteratedGradient E j) :=
  (rfl)

@[simp]
theorem contractL_succ (j i : ℕ) (h : E) :
    contractL j (i + 1) h = (contractL j i h).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E (j + i)) h) :=
  (rfl)

/-- The pointwise bound for contraction, in the operator norms of the nested linear maps. -/
theorem norm_contractL_apply_le (j i : ℕ) (h : E) (G : IteratedGradient E (j + i)) :
    ‖contractL j i h G‖ ≤ ‖G‖ * ‖h‖ ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      calc
        ‖contractL j (i + 1) h G‖ ≤ ‖G h‖ * ‖h‖ ^ i := ih (G h)
        _ ≤ (‖G‖ * ‖h‖) * ‖h‖ ^ i :=
          mul_le_mul_of_nonneg_right (G.le_opNorm h) (by positivity)
        _ = ‖G‖ * ‖h‖ ^ (i + 1) := by rw [pow_succ]; ring

/-- Partial contraction has operator norm at most the corresponding power of the direction's
norm. -/
theorem norm_contractL_le (j i : ℕ) (h : E) :
    ‖contractL j i h‖ ≤ ‖h‖ ^ i := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro G
  exact (norm_contractL_apply_le j i h G).trans_eq (mul_comm _ _)

/-- Scaling the direction scales a contraction of `i` slots by the `i`th power. -/
theorem contractL_smul_direction (j i : ℕ) (a : ℝ) (h : E) :
    contractL j i (a • h) = a ^ i • contractL j i h := by
  induction i with
  | zero => simp
  | succ i ih =>
      ext G
      simp [ih, smul_smul, pow_succ, mul_comm]

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Contract every outer slot at `h` and pair the remaining vector with `h`. Since an
iterated gradient of index `j` has derivative order `j + 1`, this uses `j + 1` directions. -/
def fullContractL : (j : ℕ) → E → IteratedGradient E j →L[ℝ] ℝ
  | 0, h => innerSL ℝ h
  | j + 1, h => (fullContractL j h).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E j) h)

@[simp]
theorem fullContractL_zero (h : E) :
    fullContractL 0 h = innerSL ℝ h :=
  (rfl)

@[simp]
theorem fullContractL_succ (j : ℕ) (h : E) :
    fullContractL (j + 1) h = (fullContractL j h).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E j) h) :=
  (rfl)

/-- Full contraction factors through any number of partial contractions in the same direction. -/
theorem fullContractL_add_apply (j i : ℕ) (h : E) (G : IteratedGradient E (j + i)) :
    fullContractL (j + i) h G = fullContractL j h (contractL j i h G) := by
  induction i with
  | zero => simp
  | succ i ih =>
      -- The recursive equations avoid rewriting the dependent index j + (i + 1).
      calc
        fullContractL (j + (i + 1)) h G = fullContractL (j + i) h (G h) := (rfl)
        _ = fullContractL j h (contractL j i h (G h)) := ih (G h)
        _ = fullContractL j h (contractL j (i + 1) h G) := (rfl)

/-- Full contraction is homogeneous of degree equal to the derivative order, not the number
of outer linear-map slots. -/
theorem fullContractL_smul_direction (j : ℕ) (a : ℝ) (h : E) :
    fullContractL j (a • h) = a ^ (j + 1) • fullContractL j h := by
  induction j with
  | zero =>
      ext G
      simp
  | succ j ih =>
      ext G
      simp [ih, pow_succ, mul_assoc, mul_comm]

@[simp]
theorem fullContractL_zero_direction (j : ℕ) :
    fullContractL (E := E) j 0 = 0 := by
  simpa using fullContractL_smul_direction j 0 (0 : E)

/-- The absolute value of a full contraction is bounded by the field norm times the
`(j + 1)`st power of the direction's norm. -/
theorem norm_fullContractL_apply_le (j : ℕ) (h : E) (G : IteratedGradient E j) :
    ‖fullContractL j h G‖ ≤ ‖G‖ * ‖h‖ ^ (j + 1) := by
  induction j with
  | zero =>
      rw [fullContractL_zero]
      simpa [mul_comm] using (norm_inner_le_norm (𝕜 := ℝ) h G)
  | succ j ih =>
      calc
        ‖fullContractL (j + 1) h G‖ ≤ ‖G h‖ * ‖h‖ ^ (j + 1) := ih (G h)
        _ ≤ (‖G‖ * ‖h‖) * ‖h‖ ^ (j + 1) :=
          mul_le_mul_of_nonneg_right (G.le_opNorm h) (by positivity)
        _ = ‖G‖ * ‖h‖ ^ (j + 1 + 1) := by rw [pow_succ]; ring

/-- The operator norm of full contraction is bounded by `‖h‖ ^ (j + 1)`. -/
theorem norm_fullContractL_le (j : ℕ) (h : E) :
    ‖fullContractL j h‖ ≤ ‖h‖ ^ (j + 1) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro G
  exact (norm_fullContractL_apply_le j h G).trans_eq (mul_comm _ _)

end InnerProductSpace

-- The gradient and Hessian of the real function x ↦ x² give different degrees in the direction.
-- The numerical calculations below evaluate the contraction recursions directly.
example (x : ℝ) : fullContractL 0 (3 : ℝ) (2 * x) = 6 * x := by
  simp only [fullContractL_zero, innerSL_apply_apply, RCLike.inner_apply, conj_trivial]
  ring

example (x : ℝ) : fullContractL 0 (6 : ℝ) (2 * x) = 12 * x := by
  simp only [fullContractL_zero, innerSL_apply_apply, RCLike.inner_apply, conj_trivial]
  ring

example : contractL 0 1 (3 : ℝ) ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) = 6 := by
  rw [contractL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  norm_num

example : fullContractL 1 (3 : ℝ) ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) = 18 := by
  rw [fullContractL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  norm_num [RCLike.inner_apply]

example : fullContractL 1 (6 : ℝ) ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) = 72 := by
  rw [fullContractL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  norm_num [RCLike.inner_apply]

end TauCeti.IteratedGradient
