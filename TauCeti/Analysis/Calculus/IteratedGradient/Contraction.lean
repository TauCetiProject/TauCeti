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
specified number of outer slots along a tuple `m : Fin i → E` is `TauCeti.IteratedGradient.applyL`
(which is multilinear in each slot: `TauCeti.IteratedGradient.applyL_update_add`,
`TauCeti.IteratedGradient.applyL_update_smul`, `TauCeti.IteratedGradient.applyL_update_zero`), and
partial contraction `TauCeti.IteratedGradient.contractL` specializes this to a repeated direction
`h`. `TauCeti.IteratedGradient.toContinuousMultilinearMap` embeds `IteratedGradient E j` linearly
and isometrically into `E [×(j + 1)]→L[ℝ] ℝ` without assuming completeness of `E`. Full
contraction (`TauCeti.IteratedGradient.fullContractL`) contracts every outer slot at `h` and pairs
the remaining vector with `h`. These operations turn derivative fields into the directional
Taylor polynomials, without choosing coordinates.

All of these operations are continuous linear in the field. Evaluating `i` outer slots along `m` has
operator norm at most `∏ r, ‖m r‖`; partial contraction of `i` slots is homogeneous of degree `i`
in the direction and has norm at most `‖h‖ ^ i`; full contraction of `IteratedGradient E j` has
degree `j + 1`, has norm at most `‖h‖ ^ (j + 1)`, depends smoothly on the direction
(`TauCeti.IteratedGradient.contDiff_fullContractL`), and on a Hilbert space evaluates
`TauCeti.iteratedGradientChain` to repeated directional derivatives
(`TauCeti.IteratedGradient.fullContractL_iteratedGradientChain_eq_iteratedFDerivAlong`).
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

/-- Updating slot `r` of the direction tuple with `v₁ + v₂` splits `applyL` as a sum. -/
@[simp]
theorem applyL_update_add (j : ℕ) :
    ∀ (i : ℕ) (m : Fin i → E) (r : Fin i) (v₁ v₂ : E),
      applyL j i (Function.update m r (v₁ + v₂)) =
        applyL j i (Function.update m r v₁) + applyL j i (Function.update m r v₂)
  | 0, _, r, _, _ => r.elim0
  | i + 1, m, r, v₁, v₂ => by
      cases r using Fin.cases with
      | zero =>
          simp only [applyL_succ, Function.update_self, Fin.tail_update_zero, map_add,
            ContinuousLinearMap.comp_add]
      | succ r =>
          simp only [applyL_succ, Function.update_of_ne (Fin.succ_ne_zero r).symm,
            Fin.tail_update_succ, applyL_update_add j i (Fin.tail m) r v₁ v₂,
            ContinuousLinearMap.add_comp]

/-- Updating slot `r` of the direction tuple with `c • v` scales `applyL` by `c`. -/
@[simp]
theorem applyL_update_smul (j : ℕ) :
    ∀ (i : ℕ) (m : Fin i → E) (r : Fin i) (c : ℝ) (v : E),
      applyL j i (Function.update m r (c • v)) =
        c • applyL j i (Function.update m r v)
  | 0, _, r, _, _ => r.elim0
  | i + 1, m, r, c, v => by
      cases r using Fin.cases with
      | zero =>
          simp only [applyL_succ, Function.update_self, Fin.tail_update_zero, map_smul,
            ContinuousLinearMap.comp_smul]
      | succ r =>
          simp only [applyL_succ, Function.update_of_ne (Fin.succ_ne_zero r).symm,
            Fin.tail_update_succ, applyL_update_smul j i (Fin.tail m) r c v,
            ContinuousLinearMap.smul_comp]

/-- Evaluating `applyL` at a tuple with zero in slot `r` gives the zero map. -/
@[simp]
theorem applyL_update_zero (j i : ℕ) (m : Fin i → E) (r : Fin i) :
    applyL (E := E) j i (Function.update m r 0) = 0 := by
  simpa using applyL_update_smul j i m r 0 0

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
