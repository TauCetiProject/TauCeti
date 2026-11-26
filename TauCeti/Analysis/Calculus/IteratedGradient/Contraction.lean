/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.Calculus.IteratedGradient.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Contractions of iterated gradients

An iterated gradient has continuous-linear direction slots outside a final vector. Evaluating a
specified number of outer slots along a tuple `m : Fin i → E` is `TauCeti.IteratedGradient.applyL`,
and partial contraction `TauCeti.IteratedGradient.contractL` specializes this to a repeated
direction `h`. Multilinear evaluation (`TauCeti.IteratedGradient.evalL`) evaluates all direction
slots and pairs the remaining vector with the last direction, and
`TauCeti.IteratedGradient.toContinuousMultilinearMap` embeds `IteratedGradient E j` linearly and
isometrically into `E [×(j + 1)]→L[ℝ] ℝ` without assuming completeness of `E`. Full contraction
(`TauCeti.IteratedGradient.fullContractL`) is the specialisation of `evalL` to a constant tuple of
directions. These operations turn derivative fields into the directional expressions used in
Taylor polynomials, without choosing coordinates.

All of these operations are continuous linear in the field. Evaluating `i` outer slots along `m` has
operator norm at most `∏ r, ‖m r‖`; partial contraction of `i` slots is homogeneous of degree `i`
in the direction and has norm at most `‖h‖ ^ i`; full contraction of `IteratedGradient E j` has
degree `j + 1`, has norm at most `‖h‖ ^ (j + 1)`, depends smoothly on the direction
(`TauCeti.IteratedGradient.contDiff_fullContractL`), and on a Hilbert space evaluates
`TauCeti.iteratedGradientChain` to repeated directional derivatives
(`TauCeti.IteratedGradient.fullContractL_iteratedGradientChain_eq_iteratedFDerivAlong`).
Precomposing `evalL` with a single outer contraction `contractL j 1 h` prepends `h` to the
direction tuple (`TauCeti.IteratedGradient.evalL_comp_contractL_one`), `evalL` is multilinear in
each slot (`TauCeti.IteratedGradient.evalL_update_add`,
`TauCeti.IteratedGradient.evalL_update_smul`, `TauCeti.IteratedGradient.evalL_update_zero`), and two
iterated gradients agree when they have the same `evalL` values (`TauCeti.IteratedGradient.ext`).
-/

public section

noncomputable section

namespace TauCeti.IteratedGradient

open Filter Topology
open scoped ContDiff InnerProductSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluate the `i` outermost slots of an iterated gradient at the directions
`m 0, …, m (i - 1)`, leaving an iterated gradient of index `j`. In particular, evaluating zero
slots is the identity. -/
def applyL (j : ℕ) : (i : ℕ) → (Fin i → E) →
    IteratedGradient E (j + i) →L[ℝ] IteratedGradient E j
  | 0, _ => ContinuousLinearMap.id ℝ _
  | i + 1, m => (applyL j i (Fin.tail m)).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E (j + i)) (m 0))

@[simp]
theorem applyL_zero (j : ℕ) (m : Fin 0 → E) :
    applyL j 0 m = ContinuousLinearMap.id ℝ (IteratedGradient E j) :=
  (rfl)

theorem applyL_succ (j i : ℕ) (m : Fin (i + 1) → E) :
    applyL j (i + 1) m = (applyL j i (Fin.tail m)).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E (j + i)) (m 0)) :=
  (rfl)

@[simp]
theorem applyL_one (j : ℕ) (m : Fin 1 → E) :
    applyL j 1 m = ContinuousLinearMap.apply ℝ (IteratedGradient E j) (m 0) := by
  rw [applyL_succ, applyL_zero]
  exact ContinuousLinearMap.id_comp _

/-- The pointwise bound for outer-slot evaluation, in the operator norms of the nested linear
maps. -/
theorem norm_applyL_apply_le (j : ℕ) :
    ∀ (i : ℕ) (m : Fin i → E) (G : IteratedGradient E (j + i)),
      ‖applyL j i m G‖ ≤ ‖G‖ * ∏ r, ‖m r‖
  | 0, _, G => by simp
  | i + 1, m, G => by
      calc
        ‖applyL j (i + 1) m G‖ ≤ ‖G (m 0)‖ * ∏ r : Fin i, ‖Fin.tail m r‖ :=
          norm_applyL_apply_le j i (Fin.tail m) (G (m 0))
        _ ≤ (‖G‖ * ‖m 0‖) * ∏ r : Fin i, ‖Fin.tail m r‖ :=
          mul_le_mul_of_nonneg_right (G.le_opNorm (m 0))
            (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        _ = ‖G‖ * ∏ r : Fin (i + 1), ‖m r‖ := by
          rw [Fin.prod_univ_succ, Fin.tail_def, mul_assoc]

/-- Outer-slot evaluation at `m` has operator norm at most `∏ r, ‖m r‖`. -/
theorem norm_applyL_le (j i : ℕ) (m : Fin i → E) :
    ‖applyL j i m‖ ≤ ∏ r, ‖m r‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    fun G => (norm_applyL_apply_le j i m G).trans_eq (mul_comm _ _)

/-- Evaluate the `i` outermost slots of an iterated gradient at `h`, leaving an iterated
gradient of index `j`. In particular, contracting zero slots is the identity. -/
def contractL (j i : ℕ) (h : E) :
    IteratedGradient E (j + i) →L[ℝ] IteratedGradient E j :=
  applyL j i (fun _ => h)

/-- Evaluating the `i` outermost slots on a constant direction tuple is `contractL`. -/
@[simp]
theorem applyL_const (j i : ℕ) (h : E) :
    applyL j i (fun _ => h) = contractL j i h :=
  (rfl)

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

/-- The pointwise bound for contraction, in the operator norms of the nested linear maps. -/
theorem norm_contractL_apply_le (j i : ℕ) (h : E) (G : IteratedGradient E (j + i)) :
    ‖contractL j i h G‖ ≤ ‖G‖ * ‖h‖ ^ i :=
  (norm_applyL_apply_le j i (fun _ => h) G).trans_eq (by simp)

/-- Partial contraction has operator norm at most the corresponding power of the direction's
norm. -/
theorem norm_contractL_le (j i : ℕ) (h : E) :
    ‖contractL j i h‖ ≤ ‖h‖ ^ i :=
  (norm_applyL_le j i (fun _ => h)).trans_eq (by simp)

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

section
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Linear isometric embedding of `IteratedGradient E j` into `E [×(j + 1)]→L[ℝ] ℝ`, without
assuming completeness of `E`. -/
def toContinuousMultilinearMap :
    (j : ℕ) → IteratedGradient E j →ₗᵢ[ℝ] (E [×(j + 1)]→L[ℝ] ℝ)
  | 0 => (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toLinearIsometry.comp
      (InnerProductSpace.toDualMap ℝ E)
  | j + 1 =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1 + 1) => E)
        ℝ).symm.toLinearIsometry.comp ((toContinuousMultilinearMap j).postcomp (E := E))

end

/-- At index `0`, `toContinuousMultilinearMap` is the Riesz isometry composed with `Fin 1`
uncurrying. -/
theorem toContinuousMultilinearMap_zero :
    toContinuousMultilinearMap E 0 =
      (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toLinearIsometry.comp
        (InnerProductSpace.toDualMap ℝ E) :=
  (rfl)

/-- Unfolding `toContinuousMultilinearMap` at a successor index curries `m 0` into `G` and
applies `toContinuousMultilinearMap E j` to the remaining directions `Fin.tail m`. -/
theorem toContinuousMultilinearMap_succ_apply (j : ℕ) (G : IteratedGradient E (j + 1))
    (m : Fin (j + 1 + 1) → E) :
    toContinuousMultilinearMap E (j + 1) G m =
      toContinuousMultilinearMap E j (G (m 0)) (Fin.tail m) := by
  simp [toContinuousMultilinearMap, continuousMultilinearCurryLeftEquiv_symm_apply,
    LinearIsometry.postcomp]

/-- Evaluate an iterated gradient of index `j` along `j + 1` directions: the first `j` directions
feed the outer continuous-linear slots from outermost to innermost, and the last direction pairs
with the resulting vector in `E` via the inner product. -/
def evalL (j : ℕ) (m : Fin (j + 1) → E) : IteratedGradient E j →L[ℝ] ℝ :=
  ((toContinuousMultilinearMap E j).toContinuousLinearMap).flipMultilinear m

/-- Evaluating `toContinuousMultilinearMap E j G` at `m` agrees with `evalL j m G`. -/
@[simp]
theorem toContinuousMultilinearMap_apply (j : ℕ) (G : IteratedGradient E j)
    (m : Fin (j + 1) → E) :
    toContinuousMultilinearMap E j G m = evalL j m G :=
  (rfl)

theorem evalL_zero_apply (m : Fin 1 → E) (G : IteratedGradient E 0) :
    evalL 0 m G = ⟪m 0, G⟫_ℝ := by
  rw [← toContinuousMultilinearMap_apply, real_inner_comm]
  rfl

theorem evalL_succ_apply (j : ℕ) (m : Fin (j + 1 + 1) → E) (G : IteratedGradient E (j + 1)) :
    evalL (j + 1) m G = evalL j (Fin.tail m) (G (m 0)) :=
  toContinuousMultilinearMap_succ_apply j G m

theorem evalL_zero (m : Fin 1 → E) :
    evalL 0 m = innerSL ℝ (m 0) :=
  ContinuousLinearMap.ext (evalL_zero_apply m)

theorem evalL_succ (j : ℕ) (m : Fin (j + 1 + 1) → E) :
    evalL (j + 1) m = (evalL j (Fin.tail m)).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E j) (m 0)) :=
  ContinuousLinearMap.ext (evalL_succ_apply j m)

/-- Pointwise evaluation after contracting one outermost slot at `h` evaluates at `Fin.cons h m`. -/
theorem evalL_contractL_one_apply (j : ℕ) (h : E) (m : Fin (j + 1) → E)
    (G : IteratedGradient E (j + 1)) :
    evalL j m (contractL j 1 h G) = evalL (j + 1) (Fin.cons h m) G := by
  rw [contractL_one, ContinuousLinearMap.apply_apply, evalL_succ_apply, Fin.cons_zero,
    Fin.tail_cons]

/-- Contracting one outermost slot at `h` and evaluating at `m` evaluates at `Fin.cons h m`. -/
theorem evalL_comp_contractL_one (j : ℕ) (h : E) (m : Fin (j + 1) → E) :
    (evalL j m).comp (contractL j 1 h) = evalL (j + 1) (Fin.cons h m) := by
  ext G
  exact evalL_contractL_one_apply j h m G

/-- Two iterated gradients are equal when they agree on every tuple of directions. -/
@[ext]
theorem ext {j : ℕ} {G₁ G₂ : IteratedGradient E j}
    (h : ∀ m : Fin (j + 1) → E, evalL j m G₁ = evalL j m G₂) :
    G₁ = G₂ :=
  (toContinuousMultilinearMap E j).injective <| ContinuousMultilinearMap.ext h

/-- Evaluating `evalL` at a tuple updated in slot `i` with `v₁ + v₂` is the sum of the
evaluations at `v₁` and `v₂`. -/
@[simp]
theorem evalL_update_add (j : ℕ) (m : Fin (j + 1) → E) (i : Fin (j + 1)) (v₁ v₂ : E) :
    evalL j (Function.update m i (v₁ + v₂)) =
      evalL j (Function.update m i v₁) + evalL j (Function.update m i v₂) :=
  ((toContinuousMultilinearMap E j).toContinuousLinearMap).flipMultilinear.map_update_add m i v₁ v₂

/-- Evaluating `evalL` at a tuple updated in slot `i` with `c • v` scales the evaluation by
`c`. -/
@[simp]
theorem evalL_update_smul (j : ℕ) (m : Fin (j + 1) → E) (i : Fin (j + 1)) (c : ℝ) (v : E) :
    evalL j (Function.update m i (c • v)) = c • evalL j (Function.update m i v) :=
  ((toContinuousMultilinearMap E j).toContinuousLinearMap).flipMultilinear.map_update_smul m i c v

/-- Evaluating `evalL` at a tuple with zero in slot `i` gives the zero map. -/
@[simp]
theorem evalL_update_zero (j : ℕ) (m : Fin (j + 1) → E) (i : Fin (j + 1)) :
    evalL j (Function.update m i 0) = 0 :=
  ((toContinuousMultilinearMap E j).toContinuousLinearMap).flipMultilinear.map_update_zero m i

/-- Pointwise operator-norm bound for multilinear evaluation of an iterated gradient. -/
theorem norm_evalL_apply_le (j : ℕ) (m : Fin (j + 1) → E) (G : IteratedGradient E j) :
    ‖evalL j m G‖ ≤ ‖G‖ * ∏ k, ‖m k‖ := by
  rw [← toContinuousMultilinearMap_apply]
  exact ((toContinuousMultilinearMap E j G).le_opNorm m).trans_eq (by
    rw [(toContinuousMultilinearMap E j).norm_map G])

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
    fullContractL 0 h = innerSL ℝ h := by
  rw [fullContractL, evalL_zero]

@[simp]
theorem fullContractL_succ (j : ℕ) (h : E) :
    fullContractL (j + 1) h = (fullContractL j h).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E j) h) := by
  rw [fullContractL, evalL_succ]
  rfl

/-- Full contraction factors through any number of partial contractions in the same direction. -/
theorem fullContractL_add_eq_fullContractL_contractL (j i : ℕ) (h : E)
    (G : IteratedGradient E (j + i)) :
    fullContractL (j + i) h G = fullContractL j h (contractL j i h G) := by
  induction i with
  | zero => simp
  | succ i ih =>
      -- The recursive equations avoid rewriting the dependent index j + (i + 1).
      calc
        fullContractL (j + (i + 1)) h G = fullContractL (j + i) h (G h) :=
          evalL_succ_apply (j + i) (fun _ => h) G
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

/-- `fullContractL j` depends smoothly (`C^n` for every `n : ℕ∞ω`) on the direction vector. -/
theorem contDiff_fullContractL {n : ℕ∞ω} : ∀ j : ℕ, ContDiff ℝ n (fullContractL (E := E) j)
  | 0 => by rw [funext fullContractL_zero]; exact (innerSL ℝ (E := E)).contDiff
  | j + 1 => by
      rw [funext (fullContractL_succ j)]
      exact (contDiff_fullContractL j).clm_comp <| @ContinuousLinearMap.contDiff ℝ E
        ((E →L[ℝ] IteratedGradient E j) →L[ℝ] IteratedGradient E j) _ _ _ _ _ n
        (ContinuousLinearMap.apply ℝ (E' := E) (IteratedGradient E j))

/-- On any Hilbert space, full contraction of `iteratedGradientChain f j x` along `h` agrees with
`iteratedFDerivAlong ℝ (List.replicate (j + 1) h) f x` whenever `f` is `C^{j+1}` at `x`. -/
theorem fullContractL_iteratedGradientChain_eq_iteratedFDerivAlong [CompleteSpace E] :
    ∀ (j : ℕ) {f : E → ℝ} {x : E}, ContDiffAt ℝ (j + 1) f x → ∀ h : E,
      fullContractL j h (iteratedGradientChain f j x) =
        iteratedFDerivAlong ℝ (List.replicate (j + 1) h) f x
  | 0, f, x, _, h => by simpa [gradient] using real_inner_comm (gradient f x) h
  | j + 1, f, x, hf, h => by
      have hd := (contDiffAt_iteratedGradientChain (m := 1) hf j
        (by push_cast; ring_nf; exact le_rfl)).differentiableAt one_ne_zero
      have hcomp := (fullContractL j h).hasFDerivAt.comp x hd.hasFDerivAt
      have heq : fullContractL j h ∘ iteratedGradientChain f j =ᶠ[𝓝 x]
          iteratedFDerivAlong ℝ (List.replicate (j + 1) h) f :=
        (hf.eventually (by simp)).mono fun _ hy =>
          fullContractL_iteratedGradientChain_eq_iteratedFDerivAlong j
            (hy.of_le (by norm_cast; omega)) h
      rw [fullContractL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        List.replicate_succ, iteratedFDerivAlong_cons_apply, ← heq.fderiv_eq, hcomp.fderiv]; simp

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
