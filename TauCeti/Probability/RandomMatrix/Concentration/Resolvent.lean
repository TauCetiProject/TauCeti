/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import TauCeti.Analysis.Matrix.Resolvent.NormalizedTrace
public import TauCeti.Probability.Independence.Matrix
public import TauCeti.Probability.RandomMatrix.ShiftedMatrix

import TauCeti.Analysis.Matrix.Resolvent.RankBound
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.McDiarmid.RCLike

/-!
# Concentration of Hermitian dilation resolvents

A change to one row of a rectangular matrix changes its Hermitian dilation by rank at most two.
`Matrix.IsHermitian.norm_trace_inv_sub_smul_one_sub_le_rank` and
`ProbabilityTheory.iIndepFun.measureReal_norm_sub_integral_ge_le_of_bounded_differences`
give a tail bound for the normalized resolvent trace about its expectation. At a fixed
nonreal spectral parameter, summable tails give almost-sure concentration via
`TauCeti.MeasureTheory.ae_tendsto_of_tsum_dist_ge_ne_top`, with arbitrary dependence across sizes.

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
`-t² (Im z)² (m + n)² / (8m)` at a threshold `t ≥ 0`. For real `z` or zero rows,
the bound is the trivial bound `4`. No entry moment bounds are needed. -/
theorem measureReal_norm_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_ge_le
    {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {P : Measure Ω} {X : Ω → Matrix m n ℂ}
    (hind : iIndepFun (fun i ω ↦ (X ω).row i) P) (hX : AEMeasurable X P)
    (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    let f (A : Matrix m n ℂ) := (fromBlocks 0 A Aᴴ 0).normalizedResolventTrace z
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
    (hc.matrix_normalizedResolventTrace hH hz).measurable
  have hrow (i : m) : AEMeasurable (fun ω ↦ (X ω).row i) P :=
    aemeasurable_pi_iff.2 fun _ ↦ Matrix.measurable_apply.comp_aemeasurable hX
  let c := (2 / ((Fintype.card m + Fintype.card n : ℝ) * |z.im|)).toNNReal
  have hcval : (c : ℝ) = 2 / ((Fintype.card m + Fintype.card n : ℝ) * |z.im|) :=
    Real.coe_toNNReal _ (by positivity)
  have hdiff (i : m) (a b : m → n → ℂ) (hab : ∀ j ≠ i, a j = b j) :
      ‖f (Matrix.of a) - f (Matrix.of b)‖ ≤ c := by
    have hrank : (H a - H b).rank ≤ 2 := by
      simp only [H, rank_fromBlocks_zero_conjTranspose_zero_sub]
      exact Nat.mul_le_mul_left 2 (rank_sub_le_one_of_row_eq (Matrix.of a) (Matrix.of b) i hab)
    have htrace := (hH a).norm_trace_inv_sub_smul_one_sub_le_rank (hH b) hz
    simp only [f, normalizedResolventTrace_def, Fintype.card_sum]
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

/-- At a fixed nonreal `z`, the normalized Hermitian dilation resolvent trace minus its
expectation converges to zero almost surely for rectangular matrices with independent rows
at each size, provided the exponential row-concentration rates are summable. -/
theorem ae_tendsto_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n : ℕ → Type*} [∀ k, Fintype (m k)] [∀ k, Fintype (n k)]
    [∀ k, DecidableEq (m k)] [∀ k, DecidableEq (n k)]
    {X : (k : ℕ) → Ω → Matrix (m k) (n k) ℂ}
    (hind : ∀ k, iIndepFun (fun i ω ↦ (X k ω).row i) P) (hX : ∀ k, AEMeasurable (X k) P)
    (hsum : ∀ a : ℝ, 0 < a → Summable (fun k ↦
      Real.exp (-a * (Fintype.card (m k) + Fintype.card (n k) : ℝ) ^ 2 / Fintype.card (m k))))
    {z : ℂ} (hz : z.im ≠ 0) :
    let f (k : ℕ) (ω : Ω) := (fromBlocks 0 (X k ω) (X k ω)ᴴ 0).normalizedResolventTrace z
    ∀ᵐ ω ∂P, Tendsto (fun k ↦ f k ω - ∫ w, f k w ∂P) atTop (𝓝 0) := by
  intro f
  have := (hind 0).isProbabilityMeasure
  refine TauCeti.MeasureTheory.ae_tendsto_of_tsum_dist_ge_ne_top (g := 0) fun ε hε ↦ ?_
  simp only [Pi.zero_apply, dist_zero_right]
  have htail := ((hsum (ε ^ 2 * z.im ^ 2 / 8) (by positivity)).mul_left 4).of_nonneg_of_le
    (fun _ ↦ measureReal_nonneg) fun k ↦ by
      have hrate (b c : ℝ) :
          -(ε ^ 2 * z.im ^ 2) * b / (8 * c) = -(ε ^ 2 * z.im ^ 2 / 8) * b / c := by
        simp only [div_eq_mul_inv, _root_.mul_inv_rev]
        ring
      simpa only [f, hrate] using
        (hind k).measureReal_norm_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_ge_le
          (hX k) z hε.le
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
    htail.tsum_ofReal_ne_top

/-- For square matrices of size `k + 1` with a fixed i.i.d. entry law, rescale the entries
by the reciprocal square root of the dimension and add a deterministic shift. At a fixed nonreal
parameter, the resulting normalized Hermitian dilation resolvent trace minus its expectation
converges to zero almost surely, allowing arbitrary dependence across sizes. -/
theorem ae_tendsto_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {X : (k : ℕ) → Ω → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hX : ∀ k, HasLaw (X k) (Measure.pi (fun _ ↦ μ)) P)
    (D : ∀ k, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Z (k : ℕ) := (D k).addInvSqrtCardSmulEntries
    let f (k : ℕ) x := (fromBlocks 0 (Z k x) (Z k x)ᴴ 0).normalizedResolventTrace z
    ∀ᵐ ω ∂P, Tendsto (fun k ↦ f k (X k ω) - ∫ w, f k (X k w) ∂P) atTop (𝓝 0) := by
  intro Z _
  have hentry (k : ℕ) (i j : Fin (k + 1)) : AEMeasurable (fun ω ↦ X k ω (i, j)) P :=
    (measurable_pi_apply _).comp_aemeasurable (hX k).aemeasurable
  have hrows (k : ℕ) : iIndepFun (fun i ω ↦ (Z k (X k ω)).row i) P := by
    have hraw := (hasLaw_pi_iff.mp (hX k)).1.matrix_row
      (X := fun ω ↦ Matrix.of fun i j ↦ X k ω (i, j)) (hentry k)
    let g (i : Fin (k + 1)) (r : Fin (k + 1) → ℂ) (j : Fin (k + 1)) :=
      D k i j + (Real.sqrt (k + 1))⁻¹ • r j
    have heq : (fun i ω ↦ (Z k (X k ω)).row i) =
        (fun i ↦ g i ∘ fun ω ↦ (Matrix.of fun i j ↦ X k ω (i, j)).row i) := by
      funext i ω j
      simp only [Z, addInvSqrtCardSmulEntries_def, Fintype.card_fin, Nat.cast_add,
        Nat.cast_one, g, Function.comp_apply, Matrix.row_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.of_apply]
    rw [heq]
    exact hraw.comp g (fun _ ↦ by fun_prop)
  have hm (k : ℕ) : AEMeasurable (fun ω ↦ Z k (X k ω)) P :=
    (continuous_addInvSqrtCardSmulEntries (D k)).measurable.comp_aemeasurable
      (hX k).aemeasurable
  refine ae_tendsto_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral hrows hm
    (fun a ha ↦ ?_) hz
  have hrate (k : ℕ) : -a * ((k + 1) + (k + 1)) ^ 2 / (k + 1 : ℝ) =
      -(4 * a) * (k + 1) := by
    have hk : (k + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have ha' : -(4 * a) < 0 := by linarith
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, hrate] using
    Real.summable_exp_nat_mul_of_ge (f := fun k ↦ (k : ℝ) + 1) ha' (fun k ↦ by linarith)

end TauCeti.Probability
