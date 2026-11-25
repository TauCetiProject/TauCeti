/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Rank-one iterated gradients and orthonormal basis expansion

Every `G : TauCeti.IteratedGradient E k` over a finite-dimensional real inner product space expands
along an orthonormal basis into rank-one iterated gradients `TauCeti.IteratedGradient.rankOne`
weighted by the tuple evaluation functionals `TauCeti.IteratedGradient.evalTupleL`
(`TauCeti.IteratedGradient.eq_sum_evalTupleL_rankOne`).
-/

public section

noncomputable section

namespace TauCeti.IteratedGradient

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rank-one iterated gradient built from `v : Fin (k + 1) → E`: `v 0` at index `0`, and
`w ↦ ⟪v (Fin.last (k + 1)), w⟫_ℝ • rankOne k (Fin.init v)` at index `k + 1`. -/
def rankOne : (k : ℕ) → (Fin (k + 1) → E) → IteratedGradient E k
  | 0, v => v 0
  | k + 1, v => (innerSL ℝ (v (Fin.last (k + 1)))).smulRight (rankOne k (Fin.init v))

@[simp] theorem rankOne_zero (v : Fin 1 → E) : rankOne 0 v = v 0 := (rfl)

@[simp] theorem rankOne_succ (k : ℕ) (v : Fin (k + 2) → E) :
    rankOne (k + 1) v = (innerSL ℝ (v (Fin.last (k + 1)))).smulRight (rankOne k (Fin.init v)) :=
  (rfl)

/-- Appending `w` via `Fin.snoc` tensors `rankOne k v` on the outer slot with `innerSL ℝ w`. -/
theorem rankOne_snoc (k : ℕ) (v : Fin (k + 1) → E) (w : E) :
    rankOne (k + 1) (Fin.snoc v w) = (innerSL ℝ w).smulRight (rankOne k v) := by simp [rankOne_succ]

/-- Full contraction of `rankOne k v` along `h` is the product `∏ l, ⟪v l, h⟫_ℝ`. -/
@[simp] theorem fullContractL_rankOne : ∀ (k : ℕ) (h : E) (v : Fin (k + 1) → E),
    fullContractL k h (rankOne k v) = ∏ l : Fin (k + 1), ⟪v l, h⟫_ℝ
  | 0, _, _ => by simp [real_inner_comm]
  | k + 1, h, v => by
      rw [fullContractL_succ, rankOne_succ, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply]
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp [fullContractL_rankOne k h fun i => v i.castSucc, Fin.init_def, mul_comm]

/-- The operator norm of a rank-one iterated gradient is the product of the vector norms. -/
@[simp] theorem norm_rankOne :
    ∀ (k : ℕ) (v : Fin (k + 1) → E), ‖rankOne k v‖ = ∏ l : Fin (k + 1), ‖v l‖
  | 0, _ => by simp
  | k + 1, v => by
      rw [rankOne_succ, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm,
        norm_rankOne k (Fin.init v)]
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp only [Fin.init_def, mul_comm]

/-- Evaluate an iterated gradient successively on `v k, …, v 1` and pair with `v 0`. -/
def evalTupleL : (k : ℕ) → (Fin (k + 1) → E) → IteratedGradient E k →L[ℝ] ℝ
  | 0, v => innerSL ℝ (v 0)
  | k + 1, v => (evalTupleL k (Fin.init v)).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E k) (v (Fin.last (k + 1))))

@[simp] theorem evalTupleL_zero (v : Fin 1 → E) : evalTupleL 0 v = innerSL ℝ (v 0) := (rfl)

@[simp] theorem evalTupleL_succ (k : ℕ) (v : Fin (k + 2) → E) :
    evalTupleL (k + 1) v = (evalTupleL k (Fin.init v)).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E k) (v (Fin.last (k + 1)))) := (rfl)

/-- Evaluating `evalTupleL (k + 1) (Fin.snoc v x)` on `G` applies `G` to `x` first. -/
theorem evalTupleL_snoc_apply (k : ℕ) (v : Fin (k + 1) → E) (x : E)
    (G : IteratedGradient E (k + 1)) :
    evalTupleL (k + 1) (Fin.snoc v x) G = evalTupleL k v (G x) := by
  rw [evalTupleL_succ, Fin.init_snoc, Fin.snoc_last, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]

/-- Evaluating `evalTupleL k u` on `rankOne k v` gives the product `∏ l, ⟪u l, v l⟫_ℝ`. -/
@[simp] theorem evalTupleL_rankOne : ∀ (k : ℕ) (u v : Fin (k + 1) → E),
    evalTupleL k u (rankOne k v) = ∏ l : Fin (k + 1), ⟪u l, v l⟫_ℝ
  | 0, _, _ => by simp
  | k + 1, u, v => by
      rw [evalTupleL_succ, rankOne_succ, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, ContinuousLinearMap.smulRight_apply, map_smul,
        innerSL_apply_apply, real_inner_comm, smul_eq_mul,
        evalTupleL_rankOne k (Fin.init u) (Fin.init v)]
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp only [Fin.init_def, mul_comm]

/-- Evaluating along `fun _ => h` recovers `fullContractL k h`. -/
@[simp] theorem evalTupleL_const : ∀ (k : ℕ) (h : E), evalTupleL k (fun _ => h) = fullContractL k h
  | 0, _ => by simp
  | k + 1, h => by simp [Fin.init_def, evalTupleL_const k h]

/-- Pointwise bound for `evalTupleL` in terms of `‖G‖` and the product of the direction norms. -/
theorem norm_evalTupleL_apply_le : ∀ (k : ℕ) (v : Fin (k + 1) → E) (G : IteratedGradient E k),
    ‖evalTupleL k v G‖ ≤ ‖G‖ * ∏ l : Fin (k + 1), ‖v l‖
  | 0, v, G => by
      rw [evalTupleL_zero, innerSL_apply_apply, Fin.prod_univ_one]
      exact (norm_inner_le_norm (v 0) G).trans_eq (mul_comm _ _)
  | k + 1, v, G => by
      rw [evalTupleL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
      refine (norm_evalTupleL_apply_le k (Fin.init v) _).trans
        ((mul_le_mul_of_nonneg_right (G.le_opNorm _)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _)).trans_eq ?_)
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp only [Fin.init_def]; ring

/-- The operator norm of `evalTupleL k v` is the product of the norms of its direction vectors. -/
@[simp] theorem norm_evalTupleL (k : ℕ) (v : Fin (k + 1) → E) :
    ‖evalTupleL k v‖ = ∏ l : Fin (k + 1), ‖v l‖ := by
  refine le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      fun G => (norm_evalTupleL_apply_le k v G).trans_eq (mul_comm _ _)) ?_
  rcases eq_or_lt_of_le (Finset.prod_nonneg fun l (_ : l ∈ Finset.univ) => norm_nonneg (v l)) with
    h0 | hpos
  · exact h0 ▸ norm_nonneg _
  · have hval : ‖evalTupleL k v (rankOne k v)‖ =
        (∏ l : Fin (k + 1), ‖v l‖) * ∏ l : Fin (k + 1), ‖v l‖ := by
      rw [evalTupleL_rankOne, Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ =>
        real_inner_self_nonneg)]
      simp_rw [real_inner_self_eq_norm_sq, sq, Finset.prod_mul_distrib]
    exact le_of_mul_le_mul_right
      (by simpa only [hval, norm_rankOne] using (evalTupleL k v).le_opNorm (rankOne k v)) hpos

/-- Every `G : IteratedGradient E k` expands along a finite orthonormal basis `b` into rank-one
iterated gradients weighted by `evalTupleL`. -/
theorem eq_sum_evalTupleL_rankOne {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    ∀ (k : ℕ) (G : IteratedGradient E k),
      G = ∑ I : Fin (k + 1) → ι, evalTupleL k (b ∘ I) G • rankOne k (b ∘ I)
  | 0, G => by
      symm; rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
      exact (Finset.sum_congr rfl fun _ _ => by simp).trans (b.sum_repr' G)
  | k + 1, G => by
      ext w
      rw [FunLike.coe_sum, Finset.sum_apply, ← (Fin.snocEquiv fun _ : Fin (k + 2) => ι).sum_comp]
      simp only [Fintype.sum_prod_type, Fin.snocEquiv_apply]
      conv_lhs => rw [← b.sum_repr' w, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, eq_sum_evalTupleL_rankOne b k (G (b i)), Finset.smul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [Fin.comp_snoc b J i, evalTupleL_snoc_apply, rankOne_snoc]; simp [smul_smul, mul_comm]

end TauCeti.IteratedGradient
