/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Probability.Independence.Matrix

import TauCeti.Analysis.Matrix.Resolvent.RankBound
import TauCeti.LinearAlgebra.Matrix.Rank.Block
import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.McDiarmid.RCLike
import TauCeti.Probability.RandomMatrix.CircularLaw.Replacement

/-!
# Concentration of Hermitian dilation resolvents

A change to one row of a rectangular matrix changes its Hermitian dilation by rank at most two.
The low-rank resolvent bound and McDiarmid's inequality thus give summable tails for the
normalized trace of the resolvent about its expectation. This upgrades finite-variance
replacement in expectation to an almost-sure comparison, without any independence across sizes.

## References

* C. Bordenave and D. Chafaï, *Around the circular law*, Probab. Surv. 9 (2012), 1–89,
  Lemmas 4.18 and 4.21 and §5.1.
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

private theorem ae_tendsto_normalized_trace_inv_fromBlocks_sub_integral_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {X : (k : ℕ) → Ω → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hX : ∀ k, HasLaw (X k) (Measure.pi (fun _ ↦ μ)) P)
    (D : ∀ k, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Z (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D k + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let f (k : ℕ) x := ((2 : ℂ) * (k + 1))⁻¹ *
      (fromBlocks 0 (Z k x) (Z k x)ᴴ 0 - z • 1)⁻¹.trace
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
      simp only [Z, g, Function.comp_apply, Matrix.row_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.of_apply]
    rw [heq]
    exact hraw.comp g (fun _ ↦ by fun_prop)
  have hm (k : ℕ) : AEMeasurable (fun ω ↦ Z k (X k ω)) P :=
    (show Measurable (Z k) by unfold Z; fun_prop).comp_aemeasurable (hX k).aemeasurable
  exact ae_tendsto_normalized_trace_inv_fromBlocks_sub_integral hrows hm hz

/-- Almost-sure finite-variance replacement for the normalized resolvent traces of shifted
Hermitian dilations. The two sequences may live on different probability spaces. Within each
matrix the entries have product law, and their laws match in complex mean, complex second
moment and second absolute moment. The same deterministic shift is used in both matrices. -/
theorem ae_ae_tendsto_normalized_trace_inv_fromBlocks_sub_of_hasLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {μ ν : Measure ℂ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : (k : ℕ) → Ω → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    {Y : (k : ℕ) → Ω' → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hX : ∀ k, HasLaw (X k) (Measure.pi (fun _ ↦ μ)) P)
    (hY : ∀ k, HasLaw (Y k) (Measure.pi (fun _ ↦ ν)) Q)
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    (D : ∀ k, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Z (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D k + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let f (k : ℕ) x := ((2 : ℂ) * (k + 1))⁻¹ *
      (fromBlocks 0 (Z k x) (Z k x)ᴴ 0 - z • 1)⁻¹.trace
    ∀ᵐ ω ∂P, ∀ᵐ ω' ∂Q, Tendsto (fun k ↦ f k (X k ω) - f k (Y k ω')) atTop (𝓝 0) := by
  intro Z f
  have hmeanDiff :=
    tendsto_integral_normalized_trace_inv_fromBlocks_sub_smul_one_sub_integral_of_hasLaw
      hX hY hμ hν hmean hsq habs D hz
  filter_upwards [ae_tendsto_normalized_trace_inv_fromBlocks_sub_integral_of_hasLaw hX D hz]
    with ω hω
  filter_upwards [ae_tendsto_normalized_trace_inv_fromBlocks_sub_integral_of_hasLaw hY D hz]
    with ω' hω'
  convert (hω.add hmeanDiff).sub hω' using 1
  · ext k
    ring
  · simp

/-- Almost-sure weak convergence of the spectral measures of shifted Hermitian dilations
transfers between independent entry laws with matching mixed moments through degree two.
The limiting probability measure is deterministic and the two arrays may be realized on
different spaces. -/
theorem ae_tendsto_spectralMeasure_fromBlocks_of_hasLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {μ ν : Measure ℂ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : (k : ℕ) → Ω → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    {Y : (k : ℕ) → Ω' → (Fin (k + 1) × Fin (k + 1) → ℂ)}
    (hX : ∀ k, HasLaw (X k) (Measure.pi (fun _ ↦ μ)) P)
    (hY : ∀ k, HasLaw (Y k) (Measure.pi (fun _ ↦ ν)) Q)
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    (D : ∀ k, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {ρ : ProbabilityMeasure ℝ} :
    let Z (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D k + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let L (k : ℕ) x := (fromBlocks 0 (Z k x) (Z k x)ᴴ 0).spectralMeasure
      (IsHermitian.fromBlocks isHermitian_zero rfl isHermitian_zero)
    (∀ᵐ ω' ∂Q, Tendsto (fun k ↦ L k (Y k ω')) atTop (𝓝 ρ)) →
      ∀ᵐ ω ∂P, Tendsto (fun k ↦ L k (X k ω)) atTop (𝓝 ρ) := by
  intro Z L hlim
  have := (hY 0).isProbabilityMeasure
  apply ProbabilityMeasure.ae_tendsto_of_ae_tendsto_resolventTransform
  intro z hz
  have htrace (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :
      resolventTransform (L k x : Measure ℝ) z =
        ((2 : ℂ) * (k + 1))⁻¹ * (fromBlocks 0 (Z k x) (Z k x)ᴴ 0 - z • 1)⁻¹.trace := by
    have hH : (fromBlocks 0 (Z k x) (Z k x)ᴴ 0).IsHermitian :=
      IsHermitian.fromBlocks isHermitian_zero rfl isHermitian_zero
    simpa only [L, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
      ← two_mul (k + 1 : ℂ)] using
      resolventTransform_spectralMeasure _ hH (hH.notMem_spectrum_of_im_ne_zero hz.ne')
  have hreplace :=
    ae_ae_tendsto_normalized_trace_inv_fromBlocks_sub_of_hasLaw hX hY hμ hν hmean hsq habs D hz.ne'
  filter_upwards [hreplace] with ω hω
  obtain ⟨ω', hω', hdiff⟩ := (hlim.and hω).exists
  have hRef := ProbabilityMeasure.tendsto_resolventTransform_of_tendsto hω' hz.ne'
  have hdiff' : Tendsto (fun k ↦ resolventTransform (L k (X k ω) : Measure ℝ) z -
      resolventTransform (L k (Y k ω') : Measure ℝ) z) atTop (𝓝 0) := by
    simp only [htrace]
    exact hdiff
  simpa only [sub_add_cancel, zero_add] using hdiff'.add hRef

end TauCeti.Probability
