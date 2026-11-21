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
contraction evaluates a specified number of the outer slots at a repeated direction. Multilinear
evaluation (`TauCeti.IteratedGradient.evalL`) evaluates all direction slots and pairs the remaining
vector with the last direction; full contraction (`TauCeti.IteratedGradient.fullContractL`) is its
specialisation to a constant tuple of directions. These operations turn derivative fields into the
directional expressions used in Taylor polynomials, without choosing coordinates.

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

/-- Contracting a single outermost slot is evaluation at `h`. -/
theorem contractL_one (j : ℕ) (h : E) :
    contractL j 1 h = ContinuousLinearMap.apply ℝ (IteratedGradient E j) h := by
  rw [contractL_succ, contractL_zero]
  exact ContinuousLinearMap.id_comp _

-- Not `@[simp]`: `contractL_succ` and `contractL_zero` already reduce `contractL j 1 h`, so
-- `simpNF` rejects `@[simp]` on the left-hand side here.
/-- Pointwise form of `TauCeti.IteratedGradient.contractL_one`. -/
theorem contractL_one_apply (j : ℕ) (h : E) (G : IteratedGradient E (j + 1)) :
    contractL j 1 h G = G h :=
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

open scoped InnerProductSpace

/-- Evaluate an iterated gradient of index `j` along `j + 1` directions: the first `j` directions
feed the outer continuous-linear slots from outermost to innermost, and the last direction pairs
with the resulting vector in `E` via the inner product. -/
def evalL : (j : ℕ) → (Fin (j + 1) → E) → IteratedGradient E j →L[ℝ] ℝ
  | 0, m => innerSL ℝ (m 0)
  | j + 1, m => (evalL j (Fin.tail m)).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E j) (m 0))

theorem evalL_zero (m : Fin 1 → E) :
    evalL 0 m = innerSL ℝ (m 0) :=
  (rfl)

theorem evalL_succ (j : ℕ) (m : Fin (j + 1 + 1) → E) :
    evalL (j + 1) m = (evalL j (Fin.tail m)).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E j) (m 0)) :=
  (rfl)

theorem evalL_zero_apply (m : Fin 1 → E) (G : IteratedGradient E 0) :
    evalL 0 m G = ⟪m 0, G⟫_ℝ :=
  (rfl)

theorem evalL_succ_apply (j : ℕ) (m : Fin (j + 1 + 1) → E) (G : IteratedGradient E (j + 1)) :
    evalL (j + 1) m G = evalL j (Fin.tail m) (G (m 0)) :=
  (rfl)

/-- Pointwise operator-norm bound for multilinear evaluation of an iterated gradient. -/
theorem norm_evalL_apply_le (j : ℕ) (m : Fin (j + 1) → E) (G : IteratedGradient E j) :
    ‖evalL j m G‖ ≤ ‖G‖ * ∏ k, ‖m k‖ := by
  induction j with
  | zero =>
      rw [evalL_zero_apply, Fin.prod_univ_one]
      exact (norm_inner_le_norm (m 0) G).trans_eq (mul_comm _ _)
  | succ j ih =>
      rw [evalL_succ_apply, Fin.prod_univ_succ]
      calc
        ‖evalL j (Fin.tail m) (G (m 0))‖ ≤ ‖G (m 0)‖ * ∏ k, ‖Fin.tail m k‖ :=
          ih (Fin.tail m) (G (m 0))
        _ ≤ (‖G‖ * ‖m 0‖) * ∏ k, ‖Fin.tail m k‖ :=
          mul_le_mul_of_nonneg_right (G.le_opNorm (m 0))
            (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        _ = ‖G‖ * (‖m 0‖ * ∏ k : Fin (j + 1), ‖m k.succ‖) := by
          rw [mul_assoc, Fin.tail_def]

/-- Multilinear evaluation at `m` has operator norm at most `∏ k, ‖m k‖`. -/
theorem norm_evalL_le (j : ℕ) (m : Fin (j + 1) → E) :
    ‖evalL j m‖ ≤ ∏ k, ‖m k‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    fun G => ?_
  exact (norm_evalL_apply_le j m G).trans_eq (mul_comm _ _)

/-- Contract every outer slot at `h` and pair the remaining vector with `h`. Since an
iterated gradient of index `j` has derivative order `j + 1`, this uses `j + 1` directions. -/
def fullContractL (j : ℕ) (h : E) : IteratedGradient E j →L[ℝ] ℝ :=
  evalL j (fun _ => h)

/-- Evaluating an iterated gradient on a constant tuple of directions is `fullContractL`. -/
@[simp]
theorem evalL_const (j : ℕ) (h : E) :
    evalL j (fun _ => h) = fullContractL j h :=
  (rfl)

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
theorem fullContractL_add_eq_fullContractL_contractL (j i : ℕ) (h : E)
    (G : IteratedGradient E (j + i)) :
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
    ‖fullContractL j h G‖ ≤ ‖G‖ * ‖h‖ ^ (j + 1) :=
  (norm_evalL_apply_le j (fun _ => h) G).trans_eq (by simp)

/-- The operator norm of full contraction is bounded by `‖h‖ ^ (j + 1)`. -/
theorem norm_fullContractL_le (j : ℕ) (h : E) :
    ‖fullContractL j h‖ ≤ ‖h‖ ^ (j + 1) :=
  (norm_evalL_le j (fun _ => h)).trans_eq (by simp)

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
