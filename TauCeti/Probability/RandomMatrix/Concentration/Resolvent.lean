/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic

import TauCeti.Analysis.Matrix.Resolvent.RankBound
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.McDiarmid.RCLike

/-!
# Concentration of Hermitian dilation resolvents

A change to one row of a rectangular matrix changes its Hermitian dilation by rank at most two.
The low-rank resolvent bound and McDiarmid's inequality give a tail bound for the normalized trace
of the resolvent about its expectation. For growing square matrices, the tails are summable,
giving almost-sure concentration with arbitrary dependence across sizes.

## References

* C. Bordenave and D. Chafaï, *Around the circular law*, Probab. Surv. 9 (2012), 1–89,
  Lemmas 4.18 and 4.21.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.iIndepFun

/-- For a complex matrix with independent rows, the normalized resolvent trace of its Hermitian
dilation concentrates around its expectation. For an `m × n` matrix the exponent is
`-t² (Im z)² (m + n)² / (8m)`. No entry moment bounds are needed. -/
theorem measureReal_norm_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_ge_le
    {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {P : Measure Ω} {X : Ω → Matrix m n ℂ}
    (hind : iIndepFun (fun i ω ↦ (X ω).row i) P) (hX : AEMeasurable X P)
    (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    let f (A : Matrix m n ℂ) := ((Fintype.card m + Fintype.card n : ℕ) : ℂ)⁻¹ *
      (fromBlocks 0 A Aᴴ 0 - z • 1)⁻¹.trace
    P.real {ω | t ≤ ‖f (X ω) - ∫ w, f (X w) ∂P‖} ≤
      4 * Real.exp (-(t ^ 2 * z.im ^ 2) * (Fintype.card m + Fintype.card n : ℝ) ^ 2 /
        (8 * Fintype.card m)) := by
  intro f
  by_cases hz : z.im = 0
  · have := hind.isProbabilityMeasure
    exact measureReal_le_one.trans (by simp [hz])
  let H (a : m → n → ℂ) := fromBlocks 0 (Matrix.of a) (Matrix.of a)ᴴ 0
  have hH (a) : (H a).IsHermitian := IsHermitian.fromBlocks isHermitian_zero rfl isHermitian_zero
  have hc : Continuous H := by unfold H; fun_prop
  have hf : Measurable (fun a ↦ f (Matrix.of a)) :=
    (continuous_const.mul (hc.matrix_inv_sub_smul_one hH hz).matrix_trace).measurable
  have hrow (i : m) : AEMeasurable (fun ω ↦ (X ω).row i) P :=
    aemeasurable_pi_iff.2 fun _ ↦ Matrix.measurable_apply.comp_aemeasurable hX
  let c := (2 / ((Fintype.card m + Fintype.card n : ℝ) * |z.im|)).toNNReal
  have hcval : (c : ℝ) = 2 / ((Fintype.card m + Fintype.card n : ℝ) * |z.im|) :=
    Real.coe_toNNReal _ (by positivity)
  have hdiff (i : m) (a b : m → n → ℂ) (hab : ∀ j ≠ i, a j = b j) :
      ‖f (Matrix.of a) - f (Matrix.of b)‖ ≤ c := by
    have hrank : (H a - H b).rank ≤ 2 := by
      have hr := rank_sub_le_one_of_row_eq (Matrix.of a) (Matrix.of b) i hab
      have hblock : H a - H b = fromBlocks 0 (Matrix.of a - Matrix.of b)
          (Matrix.of a - Matrix.of b)ᴴ 0 := by
        ext i j
        cases i <;> cases j <;> simp [H]
      rw [hblock, rank_fromBlocks_zero₁₁_zero₂₂, rank_conjTranspose_of_field]
      omega
    have htrace := (hH a).norm_trace_inv_sub_smul_one_sub_le_rank (hH b) hz
    dsimp only [f]
    rw [← mul_sub, norm_mul, norm_inv, Complex.norm_natCast, Nat.cast_add, hcval]
    have hrank' : ((H a - H b).rank : ℝ) ≤ 2 := by exact_mod_cast hrank
    calc
      _ ≤ (Fintype.card m + Fintype.card n : ℝ)⁻¹ * (2 / |z.im|) :=
        mul_le_mul_of_nonneg_left (htrace.trans (div_le_div_of_nonneg_right hrank' (abs_nonneg _)))
          (by positivity)
      _ = _ := by simp only [div_eq_mul_inv, _root_.mul_inv_rev]; ring
  have htail := hind.measureReal_norm_sub_integral_ge_le_of_bounded_differences hrow
    (fun a ↦ f (Matrix.of a)) hf (fun _ ↦ c) hdiff ht
  have hexponent : -(t ^ 2) / (2 * ∑ _ : m, (c : ℝ) ^ 2) =
      -(t ^ 2 * z.im ^ 2) * (Fintype.card m + Fintype.card n : ℝ) ^ 2 /
        (8 * Fintype.card m) := by
    simp only [hcval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_pow, mul_pow, sq_abs]
    by_cases hm : (Fintype.card m : ℝ) = 0
    · simp [hm]
    · have hsize : (Fintype.card m + Fintype.card n : ℝ) ≠ 0 := ne_of_gt
        (add_pos_of_pos_of_nonneg (lt_of_le_of_ne (by positivity) (Ne.symm hm)) (by positivity))
      field_simp [hm, hsize, hz]
      norm_num
  have hmatrix (ω : Ω) : Matrix.of (fun i ↦ (X ω).row i) = X ω := by
    ext i j
    simp only [Matrix.of_apply, Matrix.row_apply]
  simpa only [hexponent, hmatrix] using htail

end ProbabilityTheory.iIndepFun

namespace TauCeti.Probability

/-- For square matrices of size `k + 1` with independent rows at each size, the normalized
Hermitian dilation resolvent trace minus its expectation converges to zero almost surely. -/
theorem ae_tendsto_normalized_trace_inv_fromBlocks_sub_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : (k : ℕ) → Ω → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hind : ∀ k, iIndepFun (fun i ω ↦ (X k ω).row i) P) (hX : ∀ k, AEMeasurable (X k) P)
    {z : ℂ} (hz : z.im ≠ 0) :
    let f (k : ℕ) (ω : Ω) := ((2 : ℂ) * (k + 1))⁻¹ *
      (fromBlocks 0 (X k ω) (X k ω)ᴴ 0 - z • 1)⁻¹.trace
    ∀ᵐ ω ∂P, Tendsto (fun k ↦ f k ω - ∫ w, f k w ∂P) atTop (𝓝 0) := by
  intro f
  have := (hind 0).isProbabilityMeasure
  refine TauCeti.MeasureTheory.ae_tendsto_of_tsum_dist_ge_ne_top (g := 0) fun ε hε ↦ ?_
  simp only [Pi.zero_apply, dist_zero_right]
  have hsum : Summable (fun k : ℕ ↦ 4 * Real.exp (-(ε ^ 2 * z.im ^ 2 / 2) * (k + 1))) := by
    have hrate : 0 < ε ^ 2 * z.im ^ 2 / 2 := by positivity
    exact (Real.summable_exp_nat_mul_of_ge (f := fun k ↦ (k : ℝ) + 1)
      (neg_neg_of_pos hrate) (fun k ↦ by linarith)).mul_left 4
  have htail := hsum.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) fun k ↦ by
    have hk : (k + 1 : ℝ) ≠ 0 := by positivity
    have hrate : -(ε ^ 2 * z.im ^ 2) * ((k + 1) + (k + 1)) ^ 2 / (8 * (k + 1)) =
        -(ε ^ 2 * z.im ^ 2 / 2) * (k + 1) := by
      field_simp
      ring
    simpa only [f, Fintype.card_fin, Nat.cast_add, Nat.cast_one, ← two_mul (k + 1 : ℂ), hrate] using
      (hind k).measureReal_norm_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_ge_le
        (hX k) z hε.le
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
    htail.tsum_ofReal_ne_top

end TauCeti.Probability
