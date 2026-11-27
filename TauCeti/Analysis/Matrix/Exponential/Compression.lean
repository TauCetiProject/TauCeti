/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Analysis.Complex.Schwarz
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.LogDet.TraceExpansion
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Analysis.Normed.Algebra.MatrixExponential

/-!
# Compressions of products of matrix exponentials

Let `Q` be an orthogonal projection of `ℂⁿ` and `A₁, …, Aₘ` complex square matrices. The
determinant of the compression of `M = exp A₁ ⋯ exp Aₘ` to the range of `Q` is
`det (1 + Q (M - 1))`. This file expands it to second order:
`det (1 + Q (M - 1)) = exp (tr (Q ∑ Aᵢ) + Σ′ + R)`, where
`Σ′ = ∑_{i < j} tr (Q Aᵢ (1 - Q) Aⱼ) + ½ ∑ᵢ tr (Q Aᵢ (1 - Q) Aᵢ)` is
`Matrix.crossTrace Q [A₁, …, Aₘ]`, with two bounds for the remainder `R` in terms of
Frobenius norms, neither depending on the size of the matrices:

* `‖R‖ ≤ 3 s ³` when `s = ∑ ‖Aᵢ‖ ≤ 3 / 8`: the remainder vanishes to third order;
* `‖R‖ ≤ 21 s c ²` when moreover `s ≤ 3 / 20` and `c = ∑ ‖[Q, Aᵢ]‖`: the remainder also vanishes
  to second order in the parts of the `Aᵢ` that cross `Q`. In particular, for three matrices of
  norm at most `δ ≤ 1 / 20` whose commutators with `Q` have norm at most `ζ`,
  `‖R‖ ≤ 10 ⁴ δ ζ ²`.

When every `Aᵢ` commutes with `Q` the formula is exact with `R = 0` and `Σ′ = 0`.

The first bound expands `exp A₁ ⋯ exp Aₘ` to second order, comparing each norm with the
corresponding coefficient of `Real.exp s`, and combines it with the trace expansion
`Matrix.exists_det_one_add_eq_exp_sum_trace_pow` of `det (1 + Y)`. The traces are bounded by
`‖tr (X Y)‖ ≤ ‖X‖ ‖Y‖`, never through `‖1‖`, which keeps the bounds free of the dimension.
For the second bound, write `Aᵢ = Dᵢ + Cᵢ` with `Dᵢ` commuting with `Q` and `Cᵢ` crossing it, and
replace `Cᵢ` by `w Cᵢ` for a complex parameter `w`. The remainder is a holomorphic function of `w`.
It vanishes at `w = 0`, where everything commutes with `Q`, and is even in `w`, by conjugation
with the reflection `2 Q - 1`. On the disc where `‖w‖ ∑ ‖Cᵢ‖ ≤ (3 / 2) s` the first bound applies,
and Schwarz's lemma for even functions (`Complex.norm_le_mul_div_sq_of_even`) evaluates the
remainder at `w = 1`.

## Main definitions

* `Matrix.crossTrace Q L`: the second-order cross term
  `∑_{i < j} tr (Q Aᵢ (1 - Q) Aⱼ) + ½ ∑ᵢ tr (Q Aᵢ (1 - Q) Aᵢ)` of a list `L = [A₁, …, Aₘ]`.

## Main results

* `Matrix.det_one_add_mul_list_prod_exp_sub_one_of_forall_commute`: the exact formula
  `det (1 + Q (∏ exp Aᵢ - 1)) = exp (tr (Q ∑ Aᵢ))` when the `Aᵢ` commute with an idempotent `Q`.
* `Matrix.exists_det_one_add_mul_list_prod_exp_sub_one_eq_exp_of_sum_norm_le`: the second-order
  expansion with `‖R‖ ≤ 3 s ³`.
* `Matrix.exists_det_one_add_mul_list_prod_exp_sub_one_eq_exp_of_sum_norm_lie_le`: the
  second-order expansion with `‖R‖ ≤ 21 s c ²`.
* `Matrix.exists_det_one_add_mul_exp_mul_exp_mul_exp_sub_one_eq_exp`: the case of three matrices,
  with `‖R‖ ≤ 10 ⁴ δ ζ ²`.

## References

* P. Nelson, A. Venkatesh, *The orbit method and analysis of automorphic forms*, Acta Math. 226
  (2021), coherent states and the asymptotics of matrix coefficients near the identity.
* [grh-lean](https://github.com/lsernau/grh-lean), Apache 2.0, the method of the proof
  (`src/New/Appendix/DiscreteSeries/MinorSecondOrder.lean`).
-/

public section

open NormedSpace Finset Metric
open scoped Nat Matrix Matrix.Norms.Frobenius

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The second-order cross term -/

section CrossTrace

variable {𝕜 : Type*} [Field 𝕜]

/-- The second-order cross term of a list `[A₁, …, Aₘ]` of square matrices against `Q`:
`∑_{i < j} tr (Q Aᵢ (1 - Q) Aⱼ) + ½ ∑ᵢ tr (Q Aᵢ (1 - Q) Aᵢ)`. For an orthogonal projection `Q`
it is the second-order term of `log det (1 + Q (exp A₁ ⋯ exp Aₘ - 1))` beyond `tr (Q ∑ Aᵢ)`. -/
def crossTrace (Q : Matrix n n 𝕜) : List (Matrix n n 𝕜) → 𝕜
  | [] => 0
  | A :: L => (Q * A * (1 - Q) * A).trace / 2 + (Q * A * (1 - Q) * L.sum).trace + crossTrace Q L

@[simp]
theorem crossTrace_nil (Q : Matrix n n 𝕜) : crossTrace Q [] = 0 := (rfl)

@[simp]
theorem crossTrace_cons (Q A : Matrix n n 𝕜) (L : List (Matrix n n 𝕜)) :
    crossTrace Q (A :: L) =
      (Q * A * (1 - Q) * A).trace / 2 + (Q * A * (1 - Q) * L.sum).trace + crossTrace Q L :=
  (rfl)

/-- The cross term vanishes when every matrix of the list commutes with the idempotent `Q`. -/
theorem crossTrace_eq_zero_of_forall_commute (Q : Matrix n n 𝕜) (hQ : IsIdempotentElem Q)
    {L : List (Matrix n n 𝕜)} (hL : ∀ A ∈ L, Commute Q A) : crossTrace Q L = 0 := by
  induction L with
  | nil => rfl
  | cons A L ih =>
    have h0 : Q * A * (1 - Q) = 0 := by
      rw [(hL A List.mem_cons_self).eq, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
        hQ.eq, sub_self, Matrix.mul_zero]
    simp [h0, ih fun B hB ↦ hL B (List.mem_cons_of_mem _ hB)]

end CrossTrace

/-! ### Matrices commuting with the projection -/

/-- If every matrix of `L` commutes with the idempotent `Q`, the compression of
`∏ A ∈ L, exp A` to the range of `Q` has determinant exactly `exp (tr (Q ∑ A ∈ L, A))`. -/
theorem det_one_add_mul_list_prod_exp_sub_one_of_forall_commute {𝕜 : Type*} [RCLike 𝕜]
    (Q : Matrix n n 𝕜) (hQ : IsIdempotentElem Q) {L : List (Matrix n n 𝕜)}
    (hL : ∀ A ∈ L, Commute Q A) :
    (1 + Q * ((L.map exp).prod - 1)).det = exp (Q * L.sum).trace := by
  induction L with
  | nil => simp
  | cons A L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hA : Commute Q A := hL A List.mem_cons_self
    have hexp : Q * exp A + 1 - Q = exp (Q * A) := by
      let _ : NormedAlgebra ℚ (Matrix n n 𝕜) := NormedAlgebra.restrictScalars ℚ 𝕜 _
      exact (hQ.exp_mul hA).symm
    have e (M : Matrix n n 𝕜) : 1 + Q * (M - 1) = Q * M + 1 - Q := by noncomm_ring
    rw [e, ← IsIdempotentElem.mul_add_one_sub_mul_mul_add_one_sub hQ hA.exp_right, hexp,
      det_mul, ← e, ih fun B hB ↦ hL B (List.mem_cons_of_mem _ hB), Matrix.det_exp,
      Matrix.mul_add, trace_add, exp_add]

/-! ### The expansion to third order -/

section ThirdOrder

private theorem norm_exp_sub_one_le (A : Matrix n n ℂ) : ‖exp A - 1‖ ≤ Real.exp ‖A‖ - 1 := by
  have h := TauCeti.norm_exp_sub_sum_le_exp_norm_sub_sum (𝕜 := ℂ) A (n := 1) one_pos
  simp only [sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    div_one] at h
  exact h

private theorem norm_exp_sub_one_sub_le (A : Matrix n n ℂ) :
    ‖exp A - 1 - A‖ ≤ Real.exp ‖A‖ - 1 - ‖A‖ := by
  have h := TauCeti.norm_exp_sub_sum_le_exp_norm_sub_sum (𝕜 := ℂ) A (n := 2) two_pos
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, inv_one, pow_zero, pow_one, one_smul, div_one] at h
  rw [sub_sub, sub_sub]
  exact h

/-- The trace of `Q` times the tail of the exponential series after the quadratic term is bounded
by the tail of the real exponential series. -/
private theorem norm_trace_mul_exp_sub_le {Q : Matrix n n ℂ} (hQ : IsStarProjection Q)
    (A : Matrix n n ℂ) :
    ‖(Q * (exp A - 1 - A - (2⁻¹ : ℂ) • A ^ 2)).trace‖ ≤
      Real.exp ‖A‖ - 1 - ‖A‖ - ‖A‖ ^ 2 / 2 := by
  let trQ : Matrix n n ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap ((traceLinearMap n ℂ ℂ) ∘ₗ LinearMap.mulLeft ℂ Q)
  have hx := trQ.hasSum ((hasSum_nat_add_iff' 3).mpr (exp_series_hasSum_exp' (𝕂 := ℂ) A))
  have hr := (hasSum_nat_add_iff' 3).mpr (expSeries_div_hasSum_exp ‖A‖)
  rw [← Real.exp_eq_exp_ℝ] at hr
  have h := hx.norm_le_of_bounded hr fun k ↦ by
    have e : trQ (((k + 3)! : ℂ)⁻¹ • A ^ (k + 3)) =
        ((k + 3)! : ℂ)⁻¹ * (Q * A * A ^ (k + 2)).trace := by
      simp only [trQ, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
        Function.comp_apply, LinearMap.mulLeft_apply, traceLinearMap_apply, Matrix.mul_smul,
        trace_smul, smul_eq_mul, Matrix.mul_assoc, ← pow_succ']
    rw [e, norm_mul, norm_inv, RCLike.norm_natCast, div_eq_inv_mul]
    gcongr
    rw [pow_succ' ‖A‖ (k + 2)]
    exact (norm_trace_mul_le _ _).trans (mul_le_mul
      (frobenius_norm_mul_le_of_isStarProjection A hQ) (norm_pow_le' A (by omega))
      (norm_nonneg _) (norm_nonneg _))
  simp only [trQ, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
    Function.comp_apply, LinearMap.mulLeft_apply, traceLinearMap_apply, sum_range_succ,
    sum_range_zero, zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two,
    Nat.cast_one, Nat.cast_ofNat, inv_one, pow_zero, pow_one, one_smul, div_one] at h
  rw [add_assoc, add_assoc] at h
  rw [sub_sub, sub_sub, sub_sub, sub_sub]
  exact h

/-- The expansion of `∏ exp Aᵢ` to zeroth and first order, each with its error bounded by the
matching tail of `Real.exp (∑ ‖Aᵢ‖)`. -/
private theorem prod_exp_norm_bounds (L : List (Matrix n n ℂ)) :
    ‖(L.map exp).prod - 1‖ ≤ Real.exp (L.map (‖·‖)).sum - 1 ∧
    ‖(L.map exp).prod - 1 - L.sum‖ ≤ Real.exp (L.map (‖·‖)).sum - 1 - (L.map (‖·‖)).sum := by
  induction L with
  | nil => simp
  | cons A L ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    set M := (L.map exp).prod
    have e1 := norm_exp_sub_one_le A
    have e2 := norm_exp_sub_one_sub_le A
    have hp := mul_le_mul e1 h1 (norm_nonneg (M - 1)) ((norm_nonneg _).trans e1)
    have hexp : Real.exp (‖A‖ + (L.map (‖·‖)).sum) =
        Real.exp ‖A‖ * Real.exp (L.map (‖·‖)).sum := Real.exp_add _ _
    have e : exp A * M - 1 = (exp A - 1) + (M - 1) + (exp A - 1) * (M - 1) := by noncomm_ring
    have e' : exp A * M - 1 - (A + L.sum) =
        (exp A - 1 - A) + (M - 1 - L.sum) + (exp A - 1) * (M - 1) := by noncomm_ring
    refine ⟨?_, ?_⟩
    · rw [e, hexp]
      calc _ ≤ ‖exp A - 1‖ + ‖M - 1‖ + ‖exp A - 1‖ * ‖M - 1‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
        _ ≤ _ := by linarith
    · rw [e', hexp]
      calc _ ≤ ‖exp A - 1 - A‖ + ‖M - 1 - L.sum‖ + ‖exp A - 1‖ * ‖M - 1‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
        _ ≤ _ := by linarith

/-- The expansion of `∏ exp Aᵢ` to second order, read through the trace against `Q`, with its
error bounded by the matching tail of `Real.exp (∑ ‖Aᵢ‖)`. -/
private theorem prod_exp_trace_bound {Q : Matrix n n ℂ} (hQ : IsStarProjection Q)
    (L : List (Matrix n n ℂ)) :
    ‖(Q * ((L.map exp).prod - 1 - L.sum)).trace - crossTrace Q L -
        (Q * L.sum * Q * L.sum).trace / 2‖ ≤
      Real.exp (L.map (‖·‖)).sum - 1 - (L.map (‖·‖)).sum - (L.map (‖·‖)).sum ^ 2 / 2 := by
  induction L with
  | nil => simp
  | cons A L ih =>
    obtain ⟨h1, h2⟩ := prod_exp_norm_bounds L
    simp only [List.map_cons, List.prod_cons, List.sum_cons, crossTrace_cons]
    set S := L.sum
    set M := (L.map exp).prod
    have hc : (Q * S * Q * A).trace = (Q * A * Q * S).trace := by
      rw [Matrix.mul_assoc (Q * S), trace_mul_comm, ← Matrix.mul_assoc]
    -- the error of the cons is the sum of the errors of the head, the tail and their product
    have hsplit : (Q * (exp A * M - 1 - (A + S))).trace -
        ((Q * A * (1 - Q) * A).trace / 2 + (Q * A * (1 - Q) * S).trace + crossTrace Q L) -
        (Q * (A + S) * Q * (A + S)).trace / 2 =
        (Q * (exp A - 1 - A - (2⁻¹ : ℂ) • A ^ 2)).trace +
        ((Q * (M - 1 - S)).trace - crossTrace Q L - (Q * S * Q * S).trace / 2) +
        ((Q * (exp A - 1 - A) * (M - 1)).trace + (Q * A * (M - 1 - S)).trace) := by
      rw [show exp A * M - 1 - (A + S) =
        (exp A - 1 - A) + (M - 1 - S) + (exp A - 1) * (M - 1) by noncomm_ring]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, trace_add,
        trace_sub, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, trace_smul, smul_eq_mul,
        pow_two] at hc ⊢
      simp only [Matrix.mul_assoc] at hc ⊢
      linear_combination (-1 / 2 : ℂ) * hc
    rw [hsplit, Real.exp_add]
    have e2 := norm_exp_sub_one_sub_le A
    have e3 := norm_trace_mul_exp_sub_le hQ A
    have t1 : ‖(Q * (exp A - 1 - A) * (M - 1)).trace‖ ≤ ‖exp A - 1 - A‖ * ‖M - 1‖ :=
      (norm_trace_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (frobenius_norm_mul_le_of_isStarProjection _ hQ) (norm_nonneg _))
    have t2 : ‖(Q * A * (M - 1 - S)).trace‖ ≤ ‖A‖ * ‖M - 1 - S‖ :=
      (norm_trace_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (frobenius_norm_mul_le_of_isStarProjection _ hQ) (norm_nonneg _))
    have p1 := mul_le_mul e2 h1 (norm_nonneg _) ((norm_nonneg _).trans e2)
    have p2 := mul_le_mul_of_nonneg_left h2 (norm_nonneg A)
    generalize (Q * (exp A - 1 - A - (2⁻¹ : ℂ) • A ^ 2)).trace = u at e3 ⊢
    generalize (Q * (M - 1 - S)).trace - crossTrace Q L - (Q * S * Q * S).trace / 2 = v at ih ⊢
    generalize (Q * (exp A - 1 - A) * (M - 1)).trace = x at t1 ⊢
    generalize (Q * A * (M - 1 - S)).trace = z at t2 ⊢
    have hn : ‖u + v + (x + z)‖ ≤ ‖u‖ + ‖v‖ + (‖x‖ + ‖z‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    linarith

/-- The difference of the quadratic terms `tr (Q X Q X) - tr (Q S Q S)`, written as
`tr (Q (X - S) Q X) + tr (Q S Q (X - S))`, is at most `‖X - S‖ (‖X‖ + ‖S‖)`. -/
private theorem norm_trace_quadratic_sub_le {Q : Matrix n n ℂ} (hQ : IsStarProjection Q)
    (X S : Matrix n n ℂ) :
    ‖(Q * (X - S) * (Q * X)).trace + (Q * S * (Q * (X - S))).trace‖ ≤
      ‖X - S‖ * ‖X‖ + ‖S‖ * ‖X - S‖ :=
  (norm_add_le _ _).trans (add_le_add
    ((norm_trace_mul_le _ _).trans (mul_le_mul (frobenius_norm_mul_le_of_isStarProjection _ hQ)
      (frobenius_norm_mul_le_of_isStarProjection _ hQ) (norm_nonneg _) (norm_nonneg _)))
    ((norm_trace_mul_le _ _).trans (mul_le_mul (frobenius_norm_mul_le_of_isStarProjection _ hQ)
      (frobenius_norm_mul_le_of_isStarProjection _ hQ) (norm_nonneg _) (norm_nonneg _))))

/-- **The compression of a product of exponentials to second order.** For an orthogonal
projection `Q` and a list `L = [A₁, …, Aₘ]` of complex matrices with `s = ∑ ‖Aᵢ‖ ≤ 3 / 8`
(Frobenius norms),
`det (1 + Q (exp A₁ ⋯ exp Aₘ - 1)) = exp (tr (Q ∑ Aᵢ) + crossTrace Q L + r)` with
`‖r‖ ≤ 3 s ³`, whatever the size of the matrices. -/
theorem exists_det_one_add_mul_list_prod_exp_sub_one_eq_exp_of_sum_norm_le (Q : Matrix n n ℂ)
    (hQ : IsStarProjection Q) {L : List (Matrix n n ℂ)} (hL : (L.map (‖·‖)).sum ≤ 3 / 8) :
    ∃ r : ℂ, (1 + Q * ((L.map exp).prod - 1)).det =
        Complex.exp ((Q * L.sum).trace + crossTrace Q L + r) ∧
      ‖r‖ ≤ 3 * (L.map (‖·‖)).sum ^ 3 := by
  obtain ⟨h1, h2⟩ := prod_exp_norm_bounds L
  have h3 := prod_exp_trace_bound hQ L
  set s := (L.map (‖·‖)).sum
  set S := L.sum
  set X := (L.map exp).prod - 1 with hXdef
  have hs0 : 0 ≤ s := List.sum_nonneg (by simp)
  have hS : ‖S‖ ≤ s := List.le_sum_of_subadditive _ norm_zero.le norm_add_le L
  -- polynomial bounds for the tails of `Real.exp s`
  have b2 := Real.exp_bound' hs0 (by linarith) (n := 2) two_pos
  have b3 := Real.exp_bound' hs0 (by linarith) (n := 3) three_pos
  norm_num [sum_range_succ, Nat.factorial] at b2 b3
  have hXS : ‖X - S‖ ≤ 3 / 4 * s ^ 2 := by linarith
  have hX : ‖X‖ ≤ 41 / 32 * s := by nlinarith
  have hY : ‖Q * X‖ ≤ 1 / 2 := by nlinarith [frobenius_norm_mul_le_of_isStarProjection X hQ]
  obtain ⟨r₁, hdet, hr₁⟩ :=
    exists_det_one_add_eq_exp_sum_trace_pow (Q * X) (hY.trans_lt (by norm_num)) (k := 2)
      one_le_two
  refine ⟨r₁ + ((Q * (X - S)).trace - crossTrace Q L - (Q * S * Q * S).trace / 2) -
    ((Q * (X - S) * (Q * X)).trace + (Q * S * (Q * (X - S))).trace) / 2, ?_, ?_⟩
  · rw [hdet]
    congr 1
    simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one, pow_two, Nat.cast_zero,
      Nat.cast_one, Nat.cast_ofNat, div_zero, div_one, zero_add, Matrix.mul_sub, Matrix.sub_mul,
      trace_sub, Matrix.mul_assoc]
    ring
  · have hr₁' : ‖r₁‖ ≤ 2 / 3 * (41 / 32 * s) ^ 3 := by
      have hinv : (1 - ‖Q * X‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith [hY]) two_pos]; linarith [hY]
      have : ‖Q * X‖ ^ 3 ≤ (41 / 32 * s) ^ 3 := pow_le_pow_left₀ (norm_nonneg _)
        ((frobenius_norm_mul_le_of_isStarProjection X hQ).trans hX) 3
      have : 0 ≤ (1 - ‖Q * X‖)⁻¹ := inv_nonneg.mpr (by linarith)
      refine hr₁.trans ?_
      norm_num
      nlinarith [pow_nonneg (norm_nonneg (Q * X)) 3]
    have hq := norm_trace_quadratic_sub_le hQ X S
    have p2 : ‖X - S‖ * ‖X‖ ≤ 3 / 4 * s ^ 2 * (41 / 32 * s) :=
      mul_le_mul hXS hX (norm_nonneg _) (by positivity)
    have p3 : ‖S‖ * ‖X - S‖ ≤ s * (3 / 4 * s ^ 2) := mul_le_mul hS hXS (norm_nonneg _) hs0
    have h3' : ‖(Q * (X - S)).trace - crossTrace Q L - (Q * S * Q * S).trace / 2‖ ≤
        2 / 9 * s ^ 3 := by
      rw [hXdef]; linarith
    generalize (Q * (X - S)).trace - crossTrace Q L - (Q * S * Q * S).trace / 2 = v at h3' ⊢
    generalize (Q * (X - S) * (Q * X)).trace + (Q * S * (Q * (X - S))).trace = w at hq ⊢
    have hn : ‖r₁ + v - w / 2‖ ≤ ‖r₁‖ + ‖v‖ + ‖w‖ / 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_div, Complex.norm_two]
      gcongr
      exact norm_add_le _ _
    nlinarith

end ThirdOrder

/-! ### Conjugation by an involution commuting with the projection -/

section Conj

variable {U : Matrix n n ℂ}

private theorem conj_mul_conj (hU : U * U = 1) (X Y : Matrix n n ℂ) :
    U * X * U * (U * Y * U) = U * (X * Y) * U := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U U, hU, Matrix.one_mul]

private theorem conj_of_commute (hU : U * U = 1) {Q : Matrix n n ℂ} (hQU : Commute Q U) :
    U * Q * U = Q := by
  rw [← hQU.eq, Matrix.mul_assoc, hU, Matrix.mul_one]

private theorem trace_mul_conj (hU : U * U = 1) {Q : Matrix n n ℂ} (hQU : Commute Q U)
    (X : Matrix n n ℂ) : (Q * (U * X * U)).trace = (Q * X).trace := by
  conv_lhs => rw [← conj_of_commute hU hQU]
  rw [conj_mul_conj hU, trace_mul_cycle, hU, Matrix.one_mul]

private theorem prod_map_exp_conj (hU : U * U = 1) (L : List (Matrix n n ℂ)) :
    ((L.map fun A ↦ U * A * U).map exp).prod = U * (L.map exp).prod * U := by
  have hinv : U⁻¹ = U := Matrix.inv_eq_left_inv hU
  have hunit : IsUnit U := ⟨⟨U, U, hU, hU⟩, rfl⟩
  induction L with
  | nil => simp [hU]
  | cons A L ih =>
    simp only [List.map_cons, List.prod_cons] at ih ⊢
    have h := Matrix.exp_conj U A hunit
    rw [hinv] at h
    rw [ih, h, conj_mul_conj hU]

omit [DecidableEq n] in
private theorem sum_map_conj (L : List (Matrix n n ℂ)) :
    (L.map fun A ↦ U * A * U).sum = U * L.sum * U := by
  rw [List.sum_map_mul_right, List.sum_map_mul_left, List.map_id']

private theorem crossTrace_map_conj (hU : U * U = 1) {Q : Matrix n n ℂ} (hQU : Commute Q U)
    (L : List (Matrix n n ℂ)) : crossTrace Q (L.map fun A ↦ U * A * U) = crossTrace Q L := by
  have hQ' : U * (1 - Q) * U = 1 - Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU, conj_of_commute hU hQU]
  have key (X Y : Matrix n n ℂ) :
      (Q * (U * X * U) * (1 - Q) * (U * Y * U)).trace = (Q * X * (1 - Q) * Y).trace := by
    have hl : Q * (U * X * U) = U * (Q * X) * U := by
      conv_lhs => rw [← conj_of_commute hU hQU]
      exact conj_mul_conj hU Q X
    have hr : (1 - Q) * (U * Y * U) = U * ((1 - Q) * Y) * U := by
      conv_lhs => rw [← hQ']
      exact conj_mul_conj hU _ _
    rw [Matrix.mul_assoc (Q * (U * X * U)), hr, hl, conj_mul_conj hU, trace_mul_cycle, hU,
      Matrix.one_mul, ← Matrix.mul_assoc]
  induction L with
  | nil => rfl
  | cons A L ih => simp only [List.map_cons, crossTrace_cons, ih, sum_map_conj, key]

private theorem det_one_add_mul_conj_sub_one (hU : U * U = 1) {Q : Matrix n n ℂ}
    (hQU : Commute Q U) (M : Matrix n n ℂ) :
    (1 + Q * (U * M * U - 1)).det = (1 + Q * (M - 1)).det := by
  have e : 1 + Q * (U * M * U - 1) = U * (1 + Q * (M - 1)) * U := by
    symm
    calc U * (1 + Q * (M - 1)) * U = U * U + U * Q * (M - 1) * U := by noncomm_ring
      _ = U * U + Q * U * (M - 1) * U := by rw [hQU.eq]
      _ = U * U + Q * (U * M * U - U * U) := by noncomm_ring
      _ = 1 + Q * (U * M * U - 1) := by rw [hU]
  rw [e, det_mul, det_mul, mul_right_comm, ← det_mul, hU, det_one, one_mul]

end Conj

/-! ### Differentiability along a complex parameter -/

section Differentiable

private theorem differentiable_det_comp {f : ℂ → Matrix n n ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun w ↦ (f w).det := by
  have h (i j : n) : Differentiable ℂ fun w ↦ f w i j :=
    ((entryLinearMap ℂ ℂ i j).toContinuousLinearMap.differentiable).comp hf
  simp only [det_apply]
  fun_prop

omit [DecidableEq n] in
private theorem differentiable_trace_comp {f : ℂ → Matrix n n ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun w ↦ (f w).trace :=
  ((traceLinearMap n ℂ ℂ).toContinuousLinearMap.differentiable).comp hf

variable {ι : Type*} {f : ι → ℂ → Matrix n n ℂ}

private theorem differentiable_list_prod (hf : ∀ i, Differentiable ℂ (f i)) (L : List ι) :
    Differentiable ℂ fun w ↦ (L.map fun i ↦ f i w).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha := hf a
    fun_prop

private theorem differentiable_list_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : ι → ℂ → E} (hg : ∀ i, Differentiable ℂ (g i)) (L : List ι) :
    Differentiable ℂ fun w ↦ (L.map fun i ↦ g i w).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hg a).add ih

private theorem differentiable_crossTrace (Q : Matrix n n ℂ) (hf : ∀ i, Differentiable ℂ (f i))
    (L : List ι) : Differentiable ℂ fun w ↦ crossTrace Q (L.map fun i ↦ f i w) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, crossTrace_cons]
    have ha := hf a
    have hs := differentiable_list_sum hf L
    refine (((differentiable_trace_comp ?_).div_const 2).add (differentiable_trace_comp ?_)).add ih
    · exact (((differentiable_const Q).mul ha).mul (differentiable_const _)).mul ha
    · exact (((differentiable_const Q).mul ha).mul (differentiable_const _)).mul hs

end Differentiable

/-! ### The reflection `2 Q - 1` -/

section Reflection

variable {Q U : Matrix n n ℂ}

private theorem conj_path (hU : U * U = 1) (A : Matrix n n ℂ) (w : ℂ) :
    U * ((2⁻¹ : ℂ) • (A + U * A * U) + w • (2⁻¹ : ℂ) • (A - U * A * U)) * U =
      (2⁻¹ : ℂ) • (A + U * A * U) + (-w) • (2⁻¹ : ℂ) • (A - U * A * U) := by
  have e : U * (U * A * U) * U = A := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU,
      Matrix.mul_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, e]
  module

private theorem commute_half_add (hU : U * U = 1) (hQ : Q = (2⁻¹ : ℂ) • (U + 1))
    (A : Matrix n n ℂ) : Commute Q ((2⁻¹ : ℂ) • (A + U * A * U)) := by
  have hUD : Commute U ((2⁻¹ : ℂ) • (A + U * A * U)) := by
    rw [commute_iff_eq]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
    have e1 : U * (U * A * U) = A * U := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    have e2 : U * A * U * U = U * A := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]
    rw [e1, e2, add_comm]
  rw [hQ]
  exact (hUD.add_left (Commute.one_left _)).smul_left _

private theorem norm_conj_eq (hU : U ∈ unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ‖U * A * U‖ = ‖A‖ := by
  rw [UnitaryGroup.frobenius_norm_mul_right ⟨U, hU⟩, UnitaryGroup.frobenius_norm_mul_left ⟨U, hU⟩]

private theorem norm_half_add_le (hU : U ∈ unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ‖(2⁻¹ : ℂ) • (A + U * A * U)‖ ≤ ‖A‖ := by
  rw [norm_smul, norm_inv, Complex.norm_two]
  linarith [norm_add_le A (U * A * U), norm_conj_eq hU A]

private theorem norm_half_sub_le (hU : U ∈ unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ‖(2⁻¹ : ℂ) • (A - U * A * U)‖ ≤ ‖A‖ := by
  rw [norm_smul, norm_inv, Complex.norm_two]
  linarith [norm_sub_le A (U * A * U), norm_conj_eq hU A]

/-- The part of `A` crossing `Q` is `-[Q, A] (2 Q - 1)`, of norm `‖[Q, A]‖`. -/
private theorem norm_half_sub_eq (hQ : IsStarProjection Q) (A : Matrix n n ℂ) :
    ‖(2⁻¹ : ℂ) • (A - (2 * Q - 1) * A * (2 * Q - 1))‖ = ‖⁅Q, A⁆‖ := by
  have hQQ : Q * Q = Q := hQ.isIdempotentElem.eq
  have h1 : A - (2 * Q - 1) * A * (2 * Q - 1) =
      2 * (Q * A) + 2 * (A * Q) - 4 * (Q * A * Q) := by
    noncomm_ring
  have h2 : ⁅Q, A⁆ * (2 * Q - 1) = 2 * (Q * A * Q) - Q * A - 2 * (A * (Q * Q)) + A * Q := by
    rw [Ring.lie_def]
    noncomm_ring
  rw [hQQ] at h2
  have h3 : A - (2 * Q - 1) * A * (2 * Q - 1) = -(2 : ℂ) • (⁅Q, A⁆ * (2 * Q - 1)) := by
    rw [h1, h2, neg_smul, two_smul]
    noncomm_ring
  rw [h3, smul_smul, norm_smul,
    UnitaryGroup.frobenius_norm_mul_right ⟨_, hQ.two_mul_sub_one_mem_unitary⟩]
  norm_num

end Reflection

/-! ### The expansion to second order in the crossing parts -/

section SecondOrder

variable {Q : Matrix n n ℂ}

/-- The path `w ↦ D + w • C` through the part `D` of `A` that commutes with `Q`, along the part
`C` that crosses `Q`; it passes through `A` at `w = 1`. -/
private noncomputable def reflPath (Q A : Matrix n n ℂ) (w : ℂ) : Matrix n n ℂ :=
  (2⁻¹ : ℂ) • (A + (2 * Q - 1) * A * (2 * Q - 1)) +
    w • (2⁻¹ : ℂ) • (A - (2 * Q - 1) * A * (2 * Q - 1))

/-- The determinant along the path, divided by the exponential of its second-order expansion. -/
private noncomputable def remFactor (Q : Matrix n n ℂ) (L : List (Matrix n n ℂ)) (w : ℂ) : ℂ :=
  (1 + Q * (((L.map fun A ↦ reflPath Q A w).map exp).prod - 1)).det *
    Complex.exp (-((Q * (L.map fun A ↦ reflPath Q A w).sum).trace +
      crossTrace Q (L.map fun A ↦ reflPath Q A w)))

private theorem reflPath_one (Q A : Matrix n n ℂ) : reflPath Q A 1 = A := by
  rw [reflPath, one_smul, ← smul_add]
  module

private theorem norm_reflPath_le (hQ : IsStarProjection Q) (A : Matrix n n ℂ) (w : ℂ) :
    ‖reflPath Q A w‖ ≤ ‖A‖ + ‖w‖ * ‖⁅Q, A⁆‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_half_add_le hQ.two_mul_sub_one_mem_unitary A
  · rw [norm_smul, norm_half_sub_eq hQ]

private theorem differentiable_remFactor (Q : Matrix n n ℂ) (L : List (Matrix n n ℂ)) :
    Differentiable ℂ (remFactor Q L) := by
  have hp (A : Matrix n n ℂ) : Differentiable ℂ (reflPath Q A) := by
    unfold reflPath
    fun_prop
  have he (A : Matrix n n ℂ) : Differentiable ℂ fun w ↦ exp (reflPath Q A w) := fun w ↦
    (NormedSpace.exp_analytic (𝕂 := ℂ) _).differentiableAt.comp w (hp A w)
  have hdet : Differentiable ℂ fun w ↦
      (1 + Q * ((L.map fun A ↦ exp (reflPath Q A w)).prod - 1)).det :=
    differentiable_det_comp ((differentiable_const _).add
      ((differentiable_const _).mul ((differentiable_list_prod he L).sub (differentiable_const _))))
  have htr :=
    differentiable_trace_comp ((differentiable_const Q).mul (differentiable_list_sum hp L))
  unfold remFactor
  simp only [List.map_map, Function.comp_def]
  exact hdet.mul (((htr.add (differentiable_crossTrace Q hp L)).neg).cexp)

/-- `remFactor` is even, by conjugation with the reflection `2 Q - 1`. -/
private theorem remFactor_neg (hQ : IsIdempotentElem Q) (L : List (Matrix n n ℂ)) (w : ℂ) :
    remFactor Q L (-w) = remFactor Q L w := by
  set U := 2 * Q - 1
  have hU : U * U = 1 := hQ.two_mul_sub_one_mul_self
  have hQU : Commute Q U :=
    ((Commute.ofNat_right Q 2).mul_right (Commute.refl Q)).sub_right (Commute.one_right Q)
  have hL : (L.map fun A ↦ reflPath Q A (-w)) =
      (L.map fun A ↦ reflPath Q A w).map fun B ↦ U * B * U := by
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left fun A _ ↦ (conj_path hU A w).symm
  rw [remFactor, remFactor, hL, prod_map_exp_conj hU, det_one_add_mul_conj_sub_one hU hQU,
    sum_map_conj, trace_mul_conj hU hQU, crossTrace_map_conj hU hQU]

/-- At `w = 0` every matrix of the path commutes with `Q`, and `remFactor` is `1`. -/
private theorem remFactor_zero (hQ : IsIdempotentElem Q) (L : List (Matrix n n ℂ)) :
    remFactor Q L 0 = 1 := by
  set U := 2 * Q - 1
  have hU : U * U = 1 := hQ.two_mul_sub_one_mul_self
  have hQ2 : Q = (2⁻¹ : ℂ) • (U + 1) := by
    rw [sub_add_cancel, two_mul, ← two_smul ℂ Q, smul_smul, inv_mul_cancel₀ two_ne_zero,
      one_smul]
  have hc : ∀ B ∈ L.map fun A ↦ reflPath Q A 0, Commute Q B := by
    simp only [List.mem_map]
    rintro _ ⟨A, -, rfl⟩
    simpa [reflPath] using commute_half_add hU hQ2 A
  rw [remFactor, det_one_add_mul_list_prod_exp_sub_one_of_forall_commute Q hQ hc,
    ← Complex.exp_eq_exp_ℂ,
    crossTrace_eq_zero_of_forall_commute Q hQ hc, add_zero, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero]

/-- Where `‖w‖ ∑ ‖[Q, Aᵢ]‖ ≤ (3 / 2) s`, the third-order expansion bounds the logarithm of
`remFactor`. -/
private theorem exists_remFactor_eq_exp (hQ : IsStarProjection Q) {L : List (Matrix n n ℂ)}
    {s : ℝ} (hLs : (L.map (‖·‖)).sum ≤ s) (hs : s ≤ 3 / 20) {w : ℂ}
    (hw : ‖w‖ * (L.map fun A ↦ ‖⁅Q, A⁆‖).sum ≤ 3 / 2 * s) :
    ∃ r : ℂ, remFactor Q L w = Complex.exp r ∧ ‖r‖ ≤ 3 * (5 / 2 * s) ^ 3 := by
  have hnorm : ((L.map fun A ↦ reflPath Q A w).map (‖·‖)).sum ≤ 5 / 2 * s := by
    calc _ ≤ (L.map fun A ↦ ‖A‖ + ‖w‖ * ‖⁅Q, A⁆‖).sum := by
          rw [List.map_map]
          exact List.sum_le_sum fun A _ ↦ norm_reflPath_le hQ A w
      _ = (L.map (‖·‖)).sum + ‖w‖ * (L.map fun A ↦ ‖⁅Q, A⁆‖).sum := by
          rw [List.sum_map_add, List.sum_map_mul_left]
      _ ≤ _ := by linarith
  obtain ⟨r, hr, hrb⟩ := exists_det_one_add_mul_list_prod_exp_sub_one_eq_exp_of_sum_norm_le Q hQ
    (hnorm.trans (by linarith))
  refine ⟨r, ?_, hrb.trans ?_⟩
  · rw [remFactor, hr, ← Complex.exp_add]
    ring_nf
  · have : 0 ≤ ((L.map fun A ↦ reflPath Q A w).map (‖·‖)).sum := List.sum_nonneg (by simp)
    gcongr

/-- The second-order expansion when some `Aᵢ` does not commute with `Q`, by Schwarz's lemma for
the logarithm of `remFactor` on the disc of radius `3 s / (2 c)`. -/
private theorem exists_det_one_add_mul_list_prod_exp_sub_one_eq_exp_of_pos
    (hQ : IsStarProjection Q) {L : List (Matrix n n ℂ)} {s : ℝ} (hLs : (L.map (‖·‖)).sum ≤ s)
    (hs : s ≤ 3 / 20) (hc : 0 < (L.map fun A ↦ ‖⁅Q, A⁆‖).sum) :
    ∃ R : ℂ, (1 + Q * ((L.map exp).prod - 1)).det =
        Complex.exp ((Q * L.sum).trace + crossTrace Q L + R) ∧
      ‖R‖ ≤ 125 / 6 * s * (L.map fun A ↦ ‖⁅Q, A⁆‖).sum ^ 2 := by
  set c := (L.map fun A ↦ ‖⁅Q, A⁆‖).sum
  have hcs : c ≤ s := (List.sum_le_sum fun A _ ↦ (norm_half_sub_eq hQ A).symm.trans_le
    (norm_half_sub_le hQ.two_mul_sub_one_mem_unitary A)).trans hLs
  have hs0 : 0 < s := hc.trans_le hcs
  set ρ := 3 * s / (2 * c)
  have hρ : 1 < ρ := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hK : 3 * (5 / 2 * s) ^ 3 ≤ 1 / 4 := by
    have : (5 / 2 * s) ^ 3 ≤ (3 / 8) ^ 3 := by gcongr; linarith
    linarith
  -- on the disc of radius `ρ`, `remFactor` is `exp r` with `r` small, and its logarithm is `r`
  have hball (w : ℂ) (hw : w ∈ ball (0 : ℂ) ρ) :
      ‖Complex.log (remFactor Q L w)‖ ≤ 3 * (5 / 2 * s) ^ 3 ∧
        remFactor Q L w ∈ Complex.slitPlane := by
    have hw' : ‖w‖ * c ≤ 3 / 2 * s := by
      rw [mem_ball_zero_iff, lt_div_iff₀ (by positivity)] at hw
      linarith
    obtain ⟨r, hr, hrK⟩ := exists_remFactor_eq_exp hQ hLs hs hw'
    have him : |r.im| ≤ 1 / 4 := (Complex.abs_im_le_norm r).trans (hrK.trans hK)
    rw [hr, Complex.log_exp (by linarith [abs_le.mp him, Real.two_le_pi])
      (by linarith [abs_le.mp him, Real.two_le_pi])]
    refine ⟨hrK, ?_⟩
    have h1 := Complex.norm_exp_sub_one_le (x := r) (by linarith)
    simpa using Complex.mem_slitPlane_of_norm_lt_one (z := Complex.exp r - 1) (by linarith)
  have hd : DifferentiableOn ℂ (fun w ↦ Complex.log (remFactor Q L w)) (ball 0 ρ) :=
    fun w hw ↦ ((differentiable_remFactor Q L w).clog (hball w hw).2).differentiableWithinAt
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) ρ := by simpa using hρ
  have hS := Complex.norm_le_mul_div_sq_of_even hd
    (fun w ↦ by simp only [remFactor_neg hQ.isIdempotentElem])
    (by simp [remFactor_zero hQ.isIdempotentElem]) (fun w hw ↦ (hball w hw).1) h1
  refine ⟨Complex.log (remFactor Q L 1), ?_, ?_⟩
  · have hne : remFactor Q L 1 ≠ 0 := Complex.slitPlane_ne_zero (hball 1 h1).2
    rw [add_comm _ (Complex.log _), Complex.exp_add, Complex.exp_log hne, remFactor]
    simp only [reflPath_one, List.map_id']
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  · refine hS.trans_eq ?_
    simp only [ρ, norm_one]
    field_simp
    ring

/-- **The compression of a product of exponentials, to second order in the crossing parts.** For
an orthogonal projection `Q` and a list `L = [A₁, …, Aₘ]` of complex matrices with
`∑ ‖Aᵢ‖ ≤ s ≤ 3 / 20` and `∑ ‖[Q, Aᵢ]‖ ≤ c` (Frobenius norms),
`det (1 + Q (exp A₁ ⋯ exp Aₘ - 1)) = exp (tr (Q ∑ Aᵢ) + crossTrace Q L + R)` with
`‖R‖ ≤ 21 s c ²`, whatever the size of the matrices. -/
theorem exists_det_one_add_mul_list_prod_exp_sub_one_eq_exp_of_sum_norm_lie_le
    (Q : Matrix n n ℂ) (hQ : IsStarProjection Q) {L : List (Matrix n n ℂ)} {s c : ℝ}
    (hLs : (L.map (‖·‖)).sum ≤ s) (hs : s ≤ 3 / 20) (hLc : (L.map fun A ↦ ‖⁅Q, A⁆‖).sum ≤ c) :
    ∃ R : ℂ, (1 + Q * ((L.map exp).prod - 1)).det =
        Complex.exp ((Q * L.sum).trace + crossTrace Q L + R) ∧ ‖R‖ ≤ 21 * s * c ^ 2 := by
  have hs0 : 0 ≤ s := (List.sum_nonneg (by simp)).trans hLs
  have hc0 : 0 ≤ (L.map fun A ↦ ‖⁅Q, A⁆‖).sum := List.sum_nonneg (by simp)
  rcases hc0.eq_or_lt with h | h
  · -- every commutator vanishes, and the formula is exact
    have hcomm : ∀ A ∈ L, Commute Q A := fun A hA ↦ by
      have := List.single_le_sum (by simp) _ (List.mem_map_of_mem (f := fun A ↦ ‖⁅Q, A⁆‖) hA)
      rw [← h, norm_le_zero_iff, Ring.lie_def, sub_eq_zero] at this
      exact this
    refine ⟨0, ?_, by simp only [norm_zero]; positivity⟩
    rw [det_one_add_mul_list_prod_exp_sub_one_of_forall_commute Q hQ.isIdempotentElem hcomm,
      ← Complex.exp_eq_exp_ℂ,
      crossTrace_eq_zero_of_forall_commute Q hQ.isIdempotentElem hcomm, add_zero, add_zero]
  · obtain ⟨R, hR, hRb⟩ := exists_det_one_add_mul_list_prod_exp_sub_one_eq_exp_of_pos hQ hLs hs h
    refine ⟨R, hR, hRb.trans ?_⟩
    have : (L.map fun A ↦ ‖⁅Q, A⁆‖).sum ^ 2 ≤ c ^ 2 := by gcongr
    nlinarith

/-- **The compression of a product of three exponentials.** Let `Q` be an orthogonal projection,
`δ ≤ 1 / 20`, and `A₁, A₂, A₃` complex matrices with `‖Aᵢ‖ ≤ δ` and `‖[Q, Aᵢ]‖ ≤ ζ` (Frobenius
norms). Then `det (1 + Q (exp A₁ exp A₂ exp A₃ - 1)) =
exp (∑ᵢ tr (Q Aᵢ) + Σ′_{i ≤ j} tr (Q Aᵢ (1 - Q) Aⱼ) + R)`, where `Σ′` halves the terms with
`i = j`, and `‖R‖ ≤ 10 ⁴ δ ζ ²`. -/
theorem exists_det_one_add_mul_exp_mul_exp_mul_exp_sub_one_eq_exp (Q : Matrix n n ℂ)
    (hQ : IsStarProjection Q) {A₁ A₂ A₃ : Matrix n n ℂ} {δ ζ : ℝ} (hδ : δ ≤ 1 / 20)
    (h₁ : ‖A₁‖ ≤ δ) (h₂ : ‖A₂‖ ≤ δ) (h₃ : ‖A₃‖ ≤ δ) (h₁' : ‖⁅Q, A₁⁆‖ ≤ ζ)
    (h₂' : ‖⁅Q, A₂⁆‖ ≤ ζ) (h₃' : ‖⁅Q, A₃⁆‖ ≤ ζ) :
    ∃ R : ℂ, (1 + Q * (exp A₁ * exp A₂ * exp A₃ - 1)).det =
        Complex.exp ((Q * A₁).trace + (Q * A₂).trace + (Q * A₃).trace +
          ((Q * A₁ * (1 - Q) * A₁).trace / 2 + (Q * A₂ * (1 - Q) * A₂).trace / 2 +
            (Q * A₃ * (1 - Q) * A₃).trace / 2 + (Q * A₁ * (1 - Q) * A₂).trace +
            (Q * A₁ * (1 - Q) * A₃).trace + (Q * A₂ * (1 - Q) * A₃).trace) + R) ∧
      ‖R‖ ≤ 10 ^ 4 * δ * ζ ^ 2 := by
  obtain ⟨R, hR, hRb⟩ := exists_det_one_add_mul_list_prod_exp_sub_one_eq_exp_of_sum_norm_lie_le Q
    hQ (L := [A₁, A₂, A₃]) (s := 3 * δ) (c := 3 * ζ) (by simp; linarith) (by linarith)
    (by simp; linarith)
  refine ⟨R, ?_, ?_⟩
  · convert hR using 2
    · simp [mul_assoc]
    · simp only [crossTrace_cons, crossTrace_nil, List.sum_cons, List.sum_nil, add_zero,
        Matrix.mul_add, trace_add, Matrix.mul_zero, trace_zero]
      ring
  · have hδ0 : 0 ≤ δ := (norm_nonneg _).trans h₁
    refine hRb.trans ?_
    nlinarith [sq_nonneg ζ]

end SecondOrder

end Matrix
