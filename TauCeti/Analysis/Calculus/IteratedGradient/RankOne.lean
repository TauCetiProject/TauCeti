/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Rank-one iterated gradients, basis expansion, and smooth contraction

Every element of `TauCeti.IteratedGradient E k` over a finite-dimensional real inner product space
expands along an orthonormal basis into rank-one iterated gradients built from `k + 1` vectors.
Full contraction turns each rank-one iterated gradient into a product of inner products, and on a
Hilbert space full contraction of `TauCeti.iteratedGradientChain` recovers repeated directional
derivatives.

## Main declarations

* `TauCeti.IteratedGradient.rankOne`: the rank-one iterated gradient built from
  `v : Fin (k + 1) → E`, together with `TauCeti.IteratedGradient.fullContractL_rankOne` and
  `TauCeti.IteratedGradient.norm_rankOne`.
* `TauCeti.IteratedGradient.evalTuple` and `TauCeti.IteratedGradient.eq_sum_evalTuple_rankOne`:
  successive evaluation along `k + 1` vectors and expansion of any `G : IteratedGradient E k` along
  a finite `OrthonormalBasis`.
* `TauCeti.IteratedGradient.contDiff_fullContractL`: `fullContractL k` is `C^n` for every `n : ℕ∞ω`.
* `TauCeti.IteratedGradient.fullContractL_iteratedGradientChain_eq_iteratedFDerivAlong`: on any
  Hilbert space, contracting `iteratedGradientChain f j x` along `h` equals the `(j + 1)`-fold
  directional derivative `iteratedFDerivAlong ℝ (List.replicate (j + 1) h) f x`.
-/

public section

noncomputable section

namespace TauCeti.IteratedGradient

open scoped ContDiff InnerProductSpace

section RankOne

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rank-one iterated gradient built from `k + 1` vectors `v 0, …, v k`: at index `0` this is
`v 0`, and at index `k + 1` it sends `w` to
`⟪v (Fin.last (k + 1)), w⟫_ℝ • rankOne k (Fin.init v)`. -/
def rankOne : (k : ℕ) → (Fin (k + 1) → E) → IteratedGradient E k
  | 0, v => v 0
  | k + 1, v => (innerSL ℝ (v (Fin.last (k + 1)))).smulRight (rankOne k (Fin.init v))

/-- At index `0`, `rankOne 0 v` is the vector `v 0`. -/
@[simp]
theorem rankOne_zero (v : Fin 1 → E) : rankOne 0 v = v 0 :=
  (rfl)

/-- Recursive step for `rankOne` at index `k + 1`. -/
@[simp]
theorem rankOne_succ (k : ℕ) (v : Fin (k + 2) → E) :
    rankOne (k + 1) v = (innerSL ℝ (v (Fin.last (k + 1)))).smulRight (rankOne k (Fin.init v)) :=
  (rfl)

/-- Appending `w` via `Fin.snoc` tensors `rankOne k v` on the outer slot with `innerSL ℝ w`. -/
theorem rankOne_snoc (k : ℕ) (v : Fin (k + 1) → E) (w : E) :
    rankOne (k + 1) (Fin.snoc v w) = (innerSL ℝ w).smulRight (rankOne k v) := by
  simp [rankOne_succ]

/-- Full contraction of `rankOne k v` along `h` is the product `∏ l, ⟪v l, h⟫_ℝ`. -/
@[simp]
theorem fullContractL_rankOne :
    ∀ (k : ℕ) (h : E) (v : Fin (k + 1) → E),
      fullContractL k h (rankOne k v) = ∏ l : Fin (k + 1), ⟪v l, h⟫_ℝ
  | 0, h, v => by simp [real_inner_comm]
  | k + 1, h, v => by
      rw [fullContractL_succ, rankOne_succ, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
        map_smul, smul_eq_mul, fullContractL_rankOne k h (Fin.init v)]
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp only [Fin.init_def, mul_comm]

/-- The operator norm of a rank-one iterated gradient is the product of the vector norms. -/
theorem norm_rankOne :
    ∀ (k : ℕ) (v : Fin (k + 1) → E), ‖rankOne k v‖ = ∏ l : Fin (k + 1), ‖v l‖
  | 0, v => by simp
  | k + 1, v => by
      rw [rankOne_succ, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm,
        norm_rankOne k (Fin.init v)]
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp only [Fin.init_def, mul_comm]

/-- Evaluate an iterated gradient successively on `v k, …, v 1` and pair the resulting vector
with `v 0`. -/
def evalTuple : (k : ℕ) → (Fin (k + 1) → E) → IteratedGradient E k →L[ℝ] ℝ
  | 0, v => innerSL ℝ (v 0)
  | k + 1, v => (evalTuple k (Fin.init v)).comp
      (ContinuousLinearMap.apply ℝ (IteratedGradient E k) (v (Fin.last (k + 1))))

/-- At index `0`, `evalTuple 0 v` pairs against `v 0`. -/
@[simp]
theorem evalTuple_zero (v : Fin 1 → E) : evalTuple 0 v = innerSL ℝ (v 0) :=
  (rfl)

/-- Evaluating `evalTuple (k + 1) (Fin.snoc v x)` on `G` applies `G` to `x` first. -/
theorem evalTuple_snoc_apply (k : ℕ) (v : Fin (k + 1) → E) (x : E)
    (G : IteratedGradient E (k + 1)) :
    evalTuple (k + 1) (Fin.snoc v x) G = evalTuple k v (G x) := by
  rw [evalTuple, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  simp

/-- Every element of `IteratedGradient E k` expands along a finite orthonormal basis `b` into
rank-one iterated gradients weighted by `evalTuple`. -/
theorem eq_sum_evalTuple_rankOne {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    ∀ (k : ℕ) (G : IteratedGradient E k),
      G = ∑ I : Fin (k + 1) → ι, evalTuple k (b ∘ I) G • rankOne k (b ∘ I)
  | 0, G => by
      symm
      rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
      exact (Finset.sum_congr rfl fun i _ => by simp).trans (b.sum_repr' G)
  | k + 1, G => by
      ext w
      rw [FunLike.coe_sum, Finset.sum_apply, ← (Fin.snocEquiv fun _ : Fin (k + 2) => ι).sum_comp]
      simp only [Fintype.sum_prod_type, Fin.snocEquiv_apply]
      conv_lhs => rw [← b.sum_repr' w, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, eq_sum_evalTuple_rankOne b k (G (b i)), Finset.smul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      have hcomp : b ∘ Fin.snoc J i = Fin.snoc (b ∘ J) (b i) :=
        funext (Fin.lastCases (by simp) fun l => by simp)
      rw [hcomp, evalTuple_snoc_apply, rankOne_snoc]
      simp [smul_smul, mul_comm]

end RankOne

section Smoothness

private theorem contDiff_apply_clm {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ∞ω} : ContDiff 𝕜 n (fun v : E => ContinuousLinearMap.apply 𝕜 F v) :=
  IsBoundedLinearMap.contDiff
    { map_add := fun x y => by ext f; simp
      map_smul := fun c x => by ext f; simp
      bound := ⟨1, zero_lt_one, fun v => by
        rw [one_mul]
        exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun f =>
          (f.le_opNorm v).trans_eq (mul_comm _ _)⟩ }

/-- `fullContractL k` depends smoothly (`C^n` for every `n : ℕ∞ω`) on the direction vector. -/
theorem contDiff_fullContractL {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ∞ω} : ∀ k : ℕ, ContDiff ℝ n (fullContractL (E := E) k)
  | 0 => by
      rw [funext fullContractL_zero]
      exact (innerSL ℝ (E := E)).contDiff
  | k + 1 => by
      rw [funext (fullContractL_succ k)]
      exact (contDiff_fullContractL k).clm_comp contDiff_apply_clm

/-- On any Hilbert space, full contraction of `iteratedGradientChain f j x` along `h` agrees with
the `(j + 1)`-fold directional derivative `iteratedFDerivAlong ℝ (List.replicate (j + 1) h) f x`
whenever `f` is `C^{j+1}`. -/
theorem fullContractL_iteratedGradientChain_eq_iteratedFDerivAlong
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    ∀ (j : ℕ) {f : E → ℝ}, ContDiff ℝ (j + 1) f → ∀ x h : E,
      fullContractL j h (iteratedGradientChain f j x) =
        iteratedFDerivAlong ℝ (List.replicate (j + 1) h) f x
  | 0, _, _, x, h => by
      rw [fullContractL_zero, iteratedGradientChain_zero, innerSL_apply_apply,
        real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]
      simp
  | j + 1, f, hf, x, h => by
      have hd : DifferentiableAt ℝ (iteratedGradientChain f j) x :=
        (contDiffAt_iteratedGradientChain (m := 1) hf.contDiffAt j
          (by push_cast; ring_nf; exact le_rfl)).differentiableAt one_ne_zero
      have hcomp : HasFDerivAt
          (fun y => fullContractL j h (iteratedGradientChain f j y))
          ((fullContractL j h).comp (fderiv ℝ (iteratedGradientChain f j) x)) x :=
        (fullContractL j h).hasFDerivAt.comp x hd.hasFDerivAt
      have heq : (fun y => fullContractL j h (iteratedGradientChain f j y)) =
          iteratedFDerivAlong ℝ (List.replicate (j + 1) h) f :=
        funext fun y => fullContractL_iteratedGradientChain_eq_iteratedFDerivAlong j
          (hf.of_le (by norm_cast; omega)) y h
      have hrep : List.replicate (j + 1 + 1) h = h :: List.replicate (j + 1) h :=
        List.replicate_succ
      rw [fullContractL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        iteratedGradientChain_succ, ← ContinuousLinearMap.comp_apply, ← hcomp.fderiv, heq, hrep,
        iteratedFDerivAlong_cons_apply]

end Smoothness

-- Contracting a rank-one Hessian on `ℝ` built from `[2, 5]` in direction `3` gives `(2*3)*(5*3)`.
example : fullContractL 1 (3 : ℝ) (rankOne 1 ![2, 5]) = 90 := by
  rw [fullContractL_rankOne, Fin.prod_univ_two]
  norm_num [RCLike.inner_apply]

end TauCeti.IteratedGradient
