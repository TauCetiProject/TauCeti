/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.Sparsity
import TauCeti.Analysis.InnerProductSpace.PenalizedLeastSquares
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# The lasso: existence and optimality

For a design `X : Matrix (Fin n) ι ℝ`, observations `y : EuclideanSpace ℝ (Fin n)` and a
penalty level `λ`, the lasso objective is

`L(β) = ‖y - Xβ‖² / (2n) + λ ‖β‖₁`

(Wainwright, (7.18), p. 206), and a lasso solution is any global minimizer of `L`. No
measurable selection of a solution is made: later results are stated for every solution.

## Main definitions

* `TauCeti.lassoObjective X y λ β`: the lasso objective `‖y - Xβ‖² / (2n) + λ ‖β‖₁`.
* `TauCeti.IsLassoSolution X y λ β̂`: `β̂` minimizes the lasso objective.

The objective is continuous (`TauCeti.continuous_lassoObjective`) and equals `‖y‖² / (2n)` at
`β = 0` (`TauCeti.lassoObjective_zero`).

## Main results

* `TauCeti.exists_isLassoSolution`: for `λ ≥ 0` a solution exists.
* `TauCeti.isLassoSolution_iff_forall_inner_le`: for `λ ≥ 0`, `β̂` is a solution iff
  `⟪y - Xβ̂, X(b - β̂)⟫ / n ≤ λ (‖b‖₁ - ‖β̂‖₁)` for every `b`, that is, iff `Xᵀ(y - Xβ̂)/n` is a
  subgradient of `λ ‖·‖₁` at `β̂`. The converse direction,
  `TauCeti.isLassoSolution_of_forall_inner_le`, holds for every `λ`.
* `TauCeti.isLassoSolution_iff`: the optimality (Karush–Kuhn–Tucker) conditions, for `λ ≥ 0`:
  `(Xᵀ(y - Xβ̂))ⱼ / n = λ sign β̂ⱼ` when `β̂ⱼ ≠ 0` and `|(Xᵀ(y - Xβ̂))ⱼ / n| ≤ λ` when `β̂ⱼ = 0`
  (van de Geer, (2.4), p. 9). The `j`-th coordinate `(Xᵀr)ⱼ` is the inner product `⟪X_j, r⟫`
  of the `j`-th column of `X` with `r`.
* `TauCeti.isLassoSolution_zero_iff`: the zero vector is a solution iff
  `|(Xᵀy)ⱼ| / n ≤ λ` for every `j`.
* `TauCeti.IsLassoSolution.toEuclideanLin_eq`, `TauCeti.IsLassoSolution.fit_eq`: for `λ ≥ 0`
  any two solutions have the same fit `Xβ̂`, and for `λ > 0` also the same `ℓ¹` norm.
* `TauCeti.IsLassoSolution.variational`: the variational inequality
  `‖X(β̂ - b)‖² / n ≤ ⟪y - Xb, X(β̂ - b)⟫ / n + λ (‖b‖₁ - ‖β̂‖₁)` for every `b` (van de Geer,
  §2.4, p. 9), twice as sharp as the comparison of objective values.

The optimality results are the case `A = X`, `c = 1/n`, `h = λ ‖·‖₁` of the first-order
conditions for penalized least squares in
`TauCeti.Analysis.InnerProductSpace.PenalizedLeastSquares`, with the subdifferential of the
`ℓ¹` norm computed coordinatewise by `EuclideanSpace.forall_sum_mul_sub_le_iff`.

## References

* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
  University Press, 2019, §7.3.
* S. van de Geer, *Estimation and Testing Under Sparsity*, Lecture Notes in Mathematics 2159,
  Springer, 2016, §2.1–2.4.

The definitions are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Nonparametric/Models.lean` (`lassoObjective`, `IsLassoEstimator`); the results and
their proofs are new.
-/

public section

noncomputable section

open Set
open scoped RealInnerProductSpace Matrix

namespace TauCeti

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : Matrix (Fin n) ι ℝ} {y : EuclideanSpace ℝ (Fin n)} {lam : ℝ} {βh βh' : EuclideanSpace ℝ ι}

/-- The lasso objective `L(β) = ‖y - Xβ‖² / (2n) + λ ‖β‖₁` for the design `X`, the observations
`y` and the penalty level `λ`. -/
def lassoObjective (X : Matrix (Fin n) ι ℝ) (y : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    (β : EuclideanSpace ℝ ι) : ℝ :=
  ‖y - Matrix.toEuclideanLin X β‖ ^ 2 / (2 * n) + lam * β.restrictedL1Norm Finset.univ

/-- The lasso objective is `‖y - Xβ‖² / (2n) + λ ‖β‖₁`. -/
theorem lassoObjective_def (X : Matrix (Fin n) ι ℝ) (y : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    (β : EuclideanSpace ℝ ι) :
    lassoObjective X y lam β =
      ‖y - Matrix.toEuclideanLin X β‖ ^ 2 / (2 * n) + lam * β.restrictedL1Norm Finset.univ :=
  (rfl)

/-- At `β = 0` the lasso objective is `‖y‖² / (2n)`, for every penalty level. -/
@[simp]
theorem lassoObjective_zero (X : Matrix (Fin n) ι ℝ) (y : EuclideanSpace ℝ (Fin n)) (lam : ℝ) :
    lassoObjective X y lam 0 = ‖y‖ ^ 2 / (2 * n) := by
  simp [lassoObjective_def]

/-- The lasso objective is continuous. -/
theorem continuous_lassoObjective (X : Matrix (Fin n) ι ℝ) (y : EuclideanSpace ℝ (Fin n))
    (lam : ℝ) : Continuous (lassoObjective X y lam) := by
  have hX := (Matrix.toEuclideanLin X).continuous_of_finiteDimensional
  exact (((continuous_const.sub hX).norm.pow 2).div_const _).add
    (continuous_const.mul (EuclideanSpace.continuous_restrictedL1Norm _))

/-- The lasso objective in the form `c ‖y - A β‖² / 2 + h β` of penalized least squares. -/
private theorem lassoObjective_eq (X : Matrix (Fin n) ι ℝ) (y : EuclideanSpace ℝ (Fin n))
    (lam : ℝ) :
    lassoObjective X y lam = fun β ↦ (n : ℝ)⁻¹ * ‖y - Matrix.toEuclideanLin X β‖ ^ 2 / 2 +
      lam * β.restrictedL1Norm Finset.univ := by
  ext β
  rw [lassoObjective_def]
  ring

/-- `β̂` is a lasso solution for the design `X`, the observations `y` and the penalty level `λ`
when it minimizes the lasso objective. -/
def IsLassoSolution (X : Matrix (Fin n) ι ℝ) (y : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    (βh : EuclideanSpace ℝ ι) : Prop :=
  IsMinOn (lassoObjective X y lam) univ βh

/-- A lasso solution is a global minimizer of the lasso objective. -/
theorem isLassoSolution_def :
    IsLassoSolution X y lam βh ↔ IsMinOn (lassoObjective X y lam) univ βh :=
  Iff.rfl

/-- `β̂` is a lasso solution iff its objective value is at most that of every `β`. -/
theorem isLassoSolution_iff_forall_le :
    IsLassoSolution X y lam βh ↔ ∀ β, lassoObjective X y lam βh ≤ lassoObjective X y lam β :=
  isMinOn_univ_iff

/-- The objective value of a lasso solution is at most that of every `β`. -/
theorem IsLassoSolution.le (h : IsLassoSolution X y lam βh) (β : EuclideanSpace ℝ ι) :
    lassoObjective X y lam βh ≤ lassoObjective X y lam β :=
  isLassoSolution_iff_forall_le.1 h β

/-- For `λ ≥ 0` the lasso has a solution. -/
theorem exists_isLassoSolution (X : Matrix (Fin n) ι ℝ) (y : EuclideanSpace ℝ (Fin n))
    (hlam : 0 ≤ lam) : ∃ βh, IsLassoSolution X y lam βh := by
  rcases hlam.eq_or_lt with rfl | hlam
  · -- For `λ = 0`, a preimage of the orthogonal projection of `y` onto the range of `X`.
    let U : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := LinearMap.range (Matrix.toEuclideanLin X)
    obtain ⟨βh, hβh⟩ := LinearMap.mem_range.1 (U.starProjection_apply_mem y)
    refine ⟨βh, isLassoSolution_iff_forall_le.2 fun β ↦ ?_⟩
    have hle : ‖y - Matrix.toEuclideanLin X βh‖ ≤ ‖y - Matrix.toEuclideanLin X β‖ := by
      rw [hβh, Submodule.starProjection_minimal]
      have hb : BddBelow (range fun u : U ↦ ‖y - (u : EuclideanSpace ℝ (Fin n))‖) :=
        ⟨0, by rintro _ ⟨u, rfl⟩; exact norm_nonneg _⟩
      exact ciInf_le hb (⟨_, LinearMap.mem_range_self _ β⟩ : U)
    simp only [lassoObjective_def, zero_mul, add_zero]
    gcongr
  · -- For `λ > 0` the objective is continuous and coercive: outside a large ball,
    -- `L(0) < λ ‖β‖ ≤ λ ‖β‖₁ ≤ L(β)`.
    have hev : ∀ᶠ β in Filter.cocompact (EuclideanSpace ℝ ι),
        lassoObjective X y lam 0 ≤ lassoObjective X y lam β := by
      refine Filter.mem_cocompact.2 ⟨Metric.closedBall 0 (‖y‖ ^ 2 / (2 * n) / lam),
        isCompact_closedBall _ _, fun β hβ ↦ ?_⟩
      rw [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hlam] at hβ
      have h1 := mul_le_mul_of_nonneg_left β.norm_le_restrictedL1Norm_univ hlam.le
      have h2 : 0 ≤ ‖y - Matrix.toEuclideanLin X β‖ ^ 2 / (2 * n) := by positivity
      simp only [mem_ofPred_eq, lassoObjective_zero]
      rw [lassoObjective_def]
      linarith
    obtain ⟨βh, hβh⟩ := (continuous_lassoObjective X y lam).exists_forall_le' 0 hev
    exact ⟨βh, isLassoSolution_iff_forall_le.2 hβh⟩

omit [DecidableEq ι] in
/-- The penalty `λ ‖·‖₁` is convex for `λ ≥ 0`. -/
private theorem convexOn_penalty (hlam : 0 ≤ lam) :
    ConvexOn ℝ univ fun β : EuclideanSpace ℝ ι ↦ lam * β.restrictedL1Norm Finset.univ := by
  simpa only [smul_eq_mul] using (EuclideanSpace.convexOn_restrictedL1Norm _).smul hlam

/-- If `⟪y - Xβ̂, X(b - β̂)⟫ / n ≤ λ (‖b‖₁ - ‖β̂‖₁)` for every `b`, then `β̂` is a lasso
solution. -/
theorem isLassoSolution_of_forall_inner_le
    (H : ∀ b, ⟪y - Matrix.toEuclideanLin X βh, Matrix.toEuclideanLin X (b - βh)⟫ / n ≤
      lam * (b.restrictedL1Norm Finset.univ - βh.restrictedL1Norm Finset.univ)) :
    IsLassoSolution X y lam βh := by
  rw [isLassoSolution_def, lassoObjective_eq]
  exact TauCeti.isMinOn_of_forall_mul_inner_le (inv_nonneg.2 n.cast_nonneg) fun b ↦ by
    rw [inv_mul_eq_div, ← mul_sub]
    exact H b

/-- For `λ ≥ 0`, `β̂` is a lasso solution iff `⟪y - Xβ̂, X(b - β̂)⟫ / n ≤ λ (‖b‖₁ - ‖β̂‖₁)` for
every `b`: the vector `Xᵀ(y - Xβ̂)/n` is a subgradient of `λ ‖·‖₁` at `β̂`. -/
theorem isLassoSolution_iff_forall_inner_le (hlam : 0 ≤ lam) :
    IsLassoSolution X y lam βh ↔
      ∀ b, ⟪y - Matrix.toEuclideanLin X βh, Matrix.toEuclideanLin X (b - βh)⟫ / n ≤
        lam * (b.restrictedL1Norm Finset.univ - βh.restrictedL1Norm Finset.univ) := by
  refine ⟨fun h b ↦ ?_, isLassoSolution_of_forall_inner_le⟩
  rw [isLassoSolution_def, lassoObjective_eq] at h
  rw [← inv_mul_eq_div, mul_sub]
  exact h.mul_inner_le (convexOn_penalty hlam) b

/-- The optimality conditions of the lasso: for `λ ≥ 0`, `β̂` is a lasso solution iff for every
`j`, `(Xᵀ(y - Xβ̂))ⱼ / n = λ sign β̂ⱼ` when `β̂ⱼ ≠ 0` and `|(Xᵀ(y - Xβ̂))ⱼ / n| ≤ λ` when
`β̂ⱼ = 0`. -/
theorem isLassoSolution_iff (X : Matrix (Fin n) ι ℝ) (y : EuclideanSpace ℝ (Fin n))
    (hlam : 0 ≤ lam) (βh : EuclideanSpace ℝ ι) :
    IsLassoSolution X y lam βh ↔
      ∀ j, (βh j ≠ 0 → Matrix.toEuclideanLin Xᵀ (y - Matrix.toEuclideanLin X βh) j / n =
          lam * Real.sign (βh j)) ∧
        (βh j = 0 → |Matrix.toEuclideanLin Xᵀ (y - Matrix.toEuclideanLin X βh) j / n| ≤ lam) := by
  rw [isLassoSolution_iff_forall_inner_le hlam,
    ← EuclideanSpace.forall_sum_mul_sub_le_iff βh _ hlam]
  simp only [Matrix.inner_toEuclideanLin_eq_sum, Finset.sum_div, div_mul_eq_mul_div,
    PiLp.sub_apply]

/-- The zero vector is a lasso solution iff `|(Xᵀy)ⱼ| / n ≤ λ` for every `j`. -/
theorem isLassoSolution_zero_iff :
    IsLassoSolution X y lam 0 ↔ ∀ j, |Matrix.toEuclideanLin Xᵀ y j| / n ≤ lam := by
  have hsum := EuclideanSpace.forall_sum_mul_sub_le_iff_forall_mul_sub_le (0 : EuclideanSpace ℝ ι)
    (fun j ↦ Matrix.toEuclideanLin Xᵀ y j / n) lam
  simp only [PiLp.zero_apply, sub_zero, abs_zero, EuclideanSpace.restrictedL1Norm_zero] at hsum
  constructor
  · intro h j
    -- The variational inequality at `0` holds for every `λ`, since `λ ‖·‖₁` is homogeneous.
    rw [isLassoSolution_def, lassoObjective_eq] at h
    have H := hsum.1 (fun b ↦ by
      have hb := h.mul_inner_le_of_forall_mem_Ioo (b := b) fun s hs ↦ by
        simp only [zero_add, sub_zero, EuclideanSpace.restrictedL1Norm_smul, abs_of_pos hs.1,
          EuclideanSpace.restrictedL1Norm_zero, mul_zero]
        exact le_of_eq (by ring)
      simpa [Matrix.inner_toEuclideanLin_eq_sum, Finset.sum_div, div_mul_eq_mul_div,
        inv_mul_eq_div] using hb) j
    rw [← Nat.abs_cast n, ← abs_div]
    exact forall_mul_le_mul_abs_iff.1 H
  · intro h
    refine isLassoSolution_of_forall_inner_le fun b ↦ ?_
    have hj (j : ι) : |Matrix.toEuclideanLin Xᵀ y j / n| ≤ lam := by
      rw [abs_div, Nat.abs_cast]
      exact h j
    simpa [Matrix.inner_toEuclideanLin_eq_sum, Finset.sum_div, div_mul_eq_mul_div] using
      hsum.2 (fun j ↦ forall_mul_le_mul_abs_iff.2 (hj j)) b

/-- For `λ ≥ 0`, any two lasso solutions have the same fit `Xβ̂`. -/
theorem IsLassoSolution.toEuclideanLin_eq (hlam : 0 ≤ lam) (h : IsLassoSolution X y lam βh)
    (h' : IsLassoSolution X y lam βh') :
    Matrix.toEuclideanLin X βh = Matrix.toEuclideanLin X βh' := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact Subsingleton.elim _ _
  rw [isLassoSolution_def, lassoObjective_eq] at h h'
  exact h.map_eq_of_isMinOn (inv_pos.2 (Nat.cast_pos.2 hn)) (convexOn_penalty hlam) h'

/-- For `λ > 0`, any two lasso solutions have the same fit `Xβ̂` and the same `ℓ¹` norm. -/
theorem IsLassoSolution.fit_eq (hlam : 0 < lam) (h : IsLassoSolution X y lam βh)
    (h' : IsLassoSolution X y lam βh') :
    Matrix.toEuclideanLin X βh = Matrix.toEuclideanLin X βh' ∧
      βh.restrictedL1Norm Finset.univ = βh'.restrictedL1Norm Finset.univ := by
  refine ⟨h.toEuclideanLin_eq hlam.le h', (mul_right_inj' hlam.ne').1 ?_⟩
  rw [isLassoSolution_def, lassoObjective_eq] at h h'
  exact (h.apply_eq_of_isMinOn (inv_nonneg.2 n.cast_nonneg) (convexOn_penalty hlam.le) h' :)

/-- The variational inequality of a lasso solution: for `λ ≥ 0` and every `b`,
`‖X(β̂ - b)‖² / n ≤ ⟪y - Xb, X(β̂ - b)⟫ / n + λ (‖b‖₁ - ‖β̂‖₁)`. -/
theorem IsLassoSolution.variational (hlam : 0 ≤ lam) (h : IsLassoSolution X y lam βh)
    (b : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanLin X (βh - b)‖ ^ 2 / n ≤
      ⟪y - Matrix.toEuclideanLin X b, Matrix.toEuclideanLin X (βh - b)⟫ / n +
        lam * (b.restrictedL1Norm Finset.univ - βh.restrictedL1Norm Finset.univ) := by
  rw [isLassoSolution_def, lassoObjective_eq] at h
  have hv := h.mul_norm_sq_le (convexOn_penalty hlam) b
  rw [← inv_mul_eq_div, ← inv_mul_eq_div, mul_sub]
  exact hv

end TauCeti
