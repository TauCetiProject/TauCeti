/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear

/-!
# Multilinear evaluation and orthonormal-basis bounds for iterated gradients

An iterated gradient `TauCeti.IteratedGradient E j` has `j` outer continuous-linear direction
slots above a vector in `E`. Pairing that vector with one final direction evaluates the field on a
tuple `m : Fin (j + 1) → E` of directions (`TauCeti.IteratedGradient.evalL`). When `E` is complete,
Riesz representation and left uncurrying assemble this evaluation into a linear isometric
equivalence `TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ` between
`TauCeti.IteratedGradient E j` and the space `E [×(j + 1)]→L[ℝ] ℝ` of scalar continuous multilinear
maps, sending `TauCeti.iteratedGradientChain f j x` to `iteratedFDeriv ℝ (j + 1) f x` without any
differentiability hypothesis.

Evaluating on a constant tuple `(fun _ => h)` recovers `TauCeti.IteratedGradient.fullContractL`,
and precomposing with a single outer contraction `TauCeti.IteratedGradient.contractL j 1 h`
prepends `h` to the direction tuple. Along a finite orthonormal basis `b` of `E`, the operator norm
of an iterated gradient and the sum of the norms of its basis entries are comparable with explicit
constants (`1` and `(card ι) ^ (j + 1)`).

## Main declarations

* `TauCeti.IteratedGradient.evalL`: continuous linear evaluation of `IteratedGradient E j` along a
  tuple `Fin (j + 1) → E` of directions.
* `TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ`: the linear isometric equivalence
  `IteratedGradient E j ≃ₗᵢ[ℝ] (E [×(j + 1)]→L[ℝ] ℝ)` when `E` is complete.
* `TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain`: under this
  equivalence, `iteratedGradientChain f j x` corresponds to `iteratedFDeriv ℝ (j + 1) f x`.
* `TauCeti.IteratedGradient.norm_le_sum_norm_evalL_orthonormalBasis` and
  `TauCeti.IteratedGradient.sum_norm_evalL_orthonormalBasis_le`: equivalence between the operator
  norm of an iterated gradient and the `ℓ¹` sum of its entries along a finite orthonormal basis.
-/

public section

noncomputable section

namespace TauCeti.IteratedGradient

open scoped InnerProductSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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

/-- Evaluating an iterated gradient on a constant tuple of directions is `fullContractL`. -/
@[simp]
theorem evalL_const (j : ℕ) (h : E) :
    evalL j (fun _ => h) = fullContractL j h := by
  induction j with
  | zero =>
      rw [evalL_zero, fullContractL_zero]
  | succ j ih =>
      rw [evalL_succ, fullContractL_succ]
      ext G
      exact congrArg (fun L : IteratedGradient E j →L[ℝ] ℝ => L (G h)) ih

/-- Pointwise evaluation after contracting one outermost slot at `h` evaluates at `Fin.cons h m`. -/
theorem evalL_contractL_one_apply (j : ℕ) (h : E) (m : Fin (j + 1) → E)
    (G : IteratedGradient E (j + 1)) :
    evalL j m (contractL j 1 h G) = evalL (j + 1) (Fin.cons h m) G := by
  rw [contractL_one_apply, evalL_succ_apply, Fin.cons_zero, Fin.tail_cons]

/-- Contracting one outermost slot at `h` and evaluating at `m` evaluates at `Fin.cons h m`. -/
theorem evalL_comp_contractL_one (j : ℕ) (h : E) (m : Fin (j + 1) → E) :
    (evalL j m).comp (contractL j 1 h) = evalL (j + 1) (Fin.cons h m) := by
  ext G
  exact evalL_contractL_one_apply j h m G

/-- Two iterated gradients are equal when they agree on every tuple of directions. -/
theorem ext_evalL {j : ℕ} {G₁ G₂ : IteratedGradient E j}
    (h : ∀ m : Fin (j + 1) → E, evalL j m G₁ = evalL j m G₂) :
    G₁ = G₂ := by
  induction j with
  | zero =>
      exact ext_inner_left ℝ fun v => h (fun _ => v)
  | succ j ih =>
      ext v
      refine ih fun m => ?_
      have hm := h (Fin.cons v m)
      rwa [evalL_succ_apply, evalL_succ_apply, Fin.cons_zero, Fin.tail_cons] at hm

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
          rw [mul_assoc]
          rfl

/-- Multilinear evaluation at `m` has operator norm at most `∏ k, ‖m k‖`. -/
theorem norm_evalL_le (j : ℕ) (m : Fin (j + 1) → E) :
    ‖evalL j m‖ ≤ ∏ k, ‖m k‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    fun G => ?_
  exact (norm_evalL_apply_le j m G).trans_eq (mul_comm _ _)

/-- Any entry of an iterated gradient along vectors of an orthonormal basis has norm at most the
operator norm of the field. -/
theorem norm_evalL_orthonormalBasis_le {ι : Type*} [Fintype ι] (j : ℕ) (G : IteratedGradient E j)
    (b : OrthonormalBasis ι ℝ E) (r : Fin (j + 1) → ι) :
    ‖evalL j (fun k => b (r k)) G‖ ≤ ‖G‖ := by
  refine (norm_evalL_apply_le j (fun k => b (r k)) G).trans_eq ?_
  rw [Finset.prod_eq_one fun k _ => b.orthonormal.1 (r k), mul_one]

/-- The sum of the norms of all entries of `G : IteratedGradient E j` along an orthonormal basis
`b` is at most `(card ι) ^ (j + 1) * ‖G‖`. -/
theorem sum_norm_evalL_orthonormalBasis_le {ι : Type*} [Fintype ι] (j : ℕ)
    (G : IteratedGradient E j) (b : OrthonormalBasis ι ℝ E) :
    ∑ r : Fin (j + 1) → ι, ‖evalL j (fun k => b (r k)) G‖ ≤
      (Fintype.card ι : ℝ) ^ (j + 1) * ‖G‖ := by
  calc
    ∑ r : Fin (j + 1) → ι, ‖evalL j (fun k => b (r k)) G‖
      ≤ ∑ _r : Fin (j + 1) → ι, ‖G‖ :=
        Finset.sum_le_sum fun r _ => norm_evalL_orthonormalBasis_le j G b r
    _ = (Fintype.card ι : ℝ) ^ (j + 1) * ‖G‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow]

end InnerProductSpace

section CompleteSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- On a complete real inner product space, `IteratedGradient E j` is linearly isometric to the
space `E [×(j + 1)]→L[ℝ] ℝ` of scalar continuous multilinear maps in `j + 1` arguments. -/
def toContinuousMultilinearMapₗᵢ :
    (j : ℕ) → IteratedGradient E j ≃ₗᵢ[ℝ] (E [×(j + 1)]→L[ℝ] ℝ)
  | 0 => (InnerProductSpace.toDual ℝ E).trans (continuousMultilinearCurryFin1 ℝ E ℝ).symm
  | j + 1 =>
      ({ toFun := fun A : E →L[ℝ] IteratedGradient E j =>
            (toContinuousMultilinearMapₗᵢ j :
              IteratedGradient E j →L[ℝ] (E [×(j + 1)]→L[ℝ] ℝ)).comp A
         map_add' := fun A B => ContinuousLinearMap.comp_add _ A B
         map_smul' := fun c A => ContinuousLinearMap.comp_smul _ c A
         invFun := fun B =>
            ((toContinuousMultilinearMapₗᵢ j).symm :
              (E [×(j + 1)]→L[ℝ] ℝ) →L[ℝ] IteratedGradient E j).comp B
         left_inv := fun A => by ext x; simp
         right_inv := fun B => by ext x; simp
         norm_map' :=
           ContinuousLinearMap.opNorm_linearIsometryEquiv_comp (toContinuousMultilinearMapₗᵢ j) } :
        (E →L[ℝ] IteratedGradient E j) ≃ₗᵢ[ℝ] (E →L[ℝ] (E [×(j + 1)]→L[ℝ] ℝ))).trans
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1 + 1) => E) ℝ).symm

variable {E}

/-- Evaluating `toContinuousMultilinearMapₗᵢ E j G` at `m` agrees with `evalL j m G`. -/
@[simp]
theorem toContinuousMultilinearMapₗᵢ_apply (j : ℕ) (G : IteratedGradient E j)
    (m : Fin (j + 1) → E) :
    toContinuousMultilinearMapₗᵢ E j G m = evalL j m G := by
  induction j with
  | zero =>
      rw [toContinuousMultilinearMapₗᵢ, LinearIsometryEquiv.trans_apply,
        continuousMultilinearCurryFin1_symm_apply, InnerProductSpace.toDual_apply_apply,
        evalL_zero_apply, real_inner_comm]
  | succ j ih =>
      exact ih (G (m 0)) (Fin.tail m)

/-- Contracting one outer slot of `G` at `h` curries `h` into the first argument of the
corresponding continuous multilinear map. -/
theorem toContinuousMultilinearMapₗᵢ_contractL_one (j : ℕ) (h : E)
    (G : IteratedGradient E (j + 1)) :
    toContinuousMultilinearMapₗᵢ E j (contractL j 1 h G) =
      (toContinuousMultilinearMapₗᵢ E (j + 1) G).curryLeft h := by
  ext m
  rw [toContinuousMultilinearMapₗᵢ_apply, ContinuousMultilinearMap.curryLeft_apply,
    toContinuousMultilinearMapₗᵢ_apply, evalL_contractL_one_apply]

/-- Under `toContinuousMultilinearMapₗᵢ`, the classical `j`th iterated-gradient field of any
scalar function `f` at `x` is `iteratedFDeriv ℝ (j + 1) f x`. No differentiability assumption is
needed: at non-differentiable points both sides vanish. -/
theorem toContinuousMultilinearMapₗᵢ_iteratedGradientChain (f : E → ℝ) (j : ℕ) (x : E) :
    toContinuousMultilinearMapₗᵢ E j (iteratedGradientChain f j x) =
      iteratedFDeriv ℝ (j + 1) f x := by
  induction j generalizing x with
  | zero =>
      ext m
      rw [toContinuousMultilinearMapₗᵢ_apply, evalL_zero_apply, iteratedGradientChain_zero,
        iteratedFDeriv_one_apply, gradient, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  | succ j ih =>
      have hfun : (toContinuousMultilinearMapₗᵢ E j ∘ iteratedGradientChain f j) =
          iteratedFDeriv ℝ (j + 1) f := funext ih
      ext m
      have hfd := congrArg (fun g : E → E [×(j + 1)]→L[ℝ] ℝ => fderiv ℝ g x (m 0) (Fin.tail m)) hfun
      rw [LinearIsometryEquiv.comp_fderiv] at hfd
      rw [toContinuousMultilinearMapₗᵢ_apply, evalL_succ_apply, iteratedGradientChain_succ,
        iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
        continuousMultilinearCurryLeftEquiv_symm_apply]
      exact (toContinuousMultilinearMapₗᵢ_apply j
        (fderiv ℝ (iteratedGradientChain f j) x (m 0)) (Fin.tail m)).symm.trans hfd

/-- Evaluating `iteratedGradientChain f j x` along `m` gives `iteratedFDeriv ℝ (j + 1) f x m`. -/
theorem evalL_iteratedGradientChain (f : E → ℝ) (j : ℕ) (x : E) (m : Fin (j + 1) → E) :
    evalL j m (iteratedGradientChain f j x) = iteratedFDeriv ℝ (j + 1) f x m := by
  rw [← toContinuousMultilinearMapₗᵢ_apply, toContinuousMultilinearMapₗᵢ_iteratedGradientChain]

/-- Full contraction of `iteratedGradientChain f j x` in direction `h` evaluates
`iteratedFDeriv ℝ (j + 1) f x` on the constant tuple `(fun _ => h)`. -/
theorem fullContractL_iteratedGradientChain (f : E → ℝ) (j : ℕ) (x h : E) :
    fullContractL j h (iteratedGradientChain f j x) =
      iteratedFDeriv ℝ (j + 1) f x (fun _ => h) := by
  rw [← evalL_const, evalL_iteratedGradientChain]

end CompleteSpace

section OrthonormalBasisLowerBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The operator norm of an iterated gradient is bounded by the sum of the norms of its entries
along a finite orthonormal basis `b`. Completeness of `E` is derived from the finite basis rather
than assumed. -/
theorem norm_le_sum_norm_evalL_orthonormalBasis {ι : Type*} [Fintype ι] (j : ℕ)
    (G : IteratedGradient E j) (b : OrthonormalBasis ι ℝ E) :
    ‖G‖ ≤ ∑ r : Fin (j + 1) → ι, ‖evalL j (fun k => b (r k)) G‖ := by
  have : FiniteDimensional ℝ E := b.toBasis.finiteDimensional_of_finite
  rw [← (toContinuousMultilinearMapₗᵢ E j).norm_map G]
  have h := (toContinuousMultilinearMapₗᵢ E j G).opNorm_le_sum_norm_apply_orthonormalBasis
    (fun _ => b)
  simp only [toContinuousMultilinearMapₗᵢ_apply] at h
  refine h.trans_eq ?_
  congr 1
  ext r
  simp

end OrthonormalBasisLowerBound

end TauCeti.IteratedGradient
