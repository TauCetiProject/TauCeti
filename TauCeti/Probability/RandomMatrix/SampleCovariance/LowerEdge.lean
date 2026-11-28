/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.Analysis.Matrix.SampleCovariance.Eigenvalues
public import TauCeti.Analysis.Matrix.SampleCovariance.NonBacktracking
public import TauCeti.Probability.Moments.CenteredTruncation
import TauCeti.Analysis.Matrix.SpectralMeasure.Standardization
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.Probability.HasLaw
import TauCeti.Probability.RandomMatrix.ExtremeEigenvalues
import TauCeti.Probability.RandomMatrix.SampleCovariance.Degrees
import TauCeti.Probability.RandomMatrix.SampleCovariance.MarchenkoPastur
import TauCeti.Probability.RandomMatrix.SampleCovariance.Truncation

/-!
# The lower edge of a sample covariance matrix

When the aspect ratio is one, the almost-sure Marchenko–Pastur law and positive
semidefiniteness give convergence of the least eigenvalue to zero, after centering and
rescaling an entry law with finite second moment. Below aspect ratio one,
a lower bound for the covariance of the centered truncated data transfers to the original
covariance by perturbing the singular values. The non-backtracking estimate gives this
bound once the walk blocks of the normalized truncated data have controlled growth.
Above aspect ratio one, applying the estimate to the adjoint yields a bound for the
positive eigenvalues. The rank bound accounts for the remaining zero eigenvalues.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the Smallest Eigenvalue of a Large Dimensional Sample
  Covariance Matrix*, Ann. Probab. 21 (1993), 1275–1294.
-/

public section

open Filter MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {x : ℕ × ℕ → Ω → ℂ}
  {ν : Measure ℂ} {p : ℕ → ℕ} [∀ n, NeZero (p n)] {y : ℝ≥0}

omit [∀ n, NeZero (p n)] in
private theorem ae_degrees_and_norm_sub_centeredTruncation
    (hx : ∀ ij, HasLaw (x ij) ν P) (hindep : iIndepFun x P)
    (hmean : ∫ z, z ∂ν = 0) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1) (h4 : MemLp id 4 ν)
    (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 (y : ℝ)))
    {a : ℝ} (ha : 1 / 4 < a) (ha' : a < 1 / 2) :
    let X (n : ℕ) (ω : Ω) : Matrix (Fin (p n)) (Fin n) ℂ := Matrix.of fun i j ↦ x (i, j) ω
    let T (n : ℕ) (ω : Ω) : Matrix (Fin (p n)) (Fin n) ℂ := Matrix.of fun i j ↦
      centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω
    let Y (n : ℕ) (ω : Ω) := (√(n : ℝ))⁻¹ • T n ω
    ∀ᵐ ω ∂P, (∀ ε > 0, ∀ᶠ n in atTop, (∀ i j, ‖Y n ω i j‖ ≤ ε) ∧
        (∀ i, |∑ j, ‖Y n ω i j‖ ^ 2 - 1| ≤ ε) ∧ (∀ j, |∑ i, ‖Y n ω i j‖ ^ 2 - y| ≤ ε)) ∧
      Tendsto (fun n ↦ ‖X n ω - T n ω‖ / √(n : ℝ)) atTop (𝓝 0) := by
  have hrow (i : ℕ) := hindep.precomp (Prod.mk_right_injective i)
  have hcol (j : ℕ) := hindep.precomp (Prod.mk_left_injective j)
  have hsize : ∀ᶠ n in atTop, (p n : ℝ) ≤ (y + 1) * n := by
    filter_upwards [hp.eventually (gt_mem_nhds (lt_add_one (y : ℝ))), eventually_gt_atTop 0]
      with n hn hn₀
    exact (div_le_iff₀ (Nat.cast_pos.mpr hn₀)).mp hn.le
  filter_upwards [SampleCovariance.ae_eventually_row_col_norm_sq_centeredTruncation hx hrow hcol
    hmean hvar hp (by linarith) ha',
    SampleCovariance.ae_tendsto_l2_opNorm_sub_centeredTruncation_div_sqrt hx hrow hcol h4 hmean
      hsize ha] with ω hdeg hnorm
  exact ⟨hdeg, hnorm⟩

/-- When the aspect ratio tends to one, the least eigenvalue of the sample covariance converges
almost surely to zero for an i.i.d. array of finite second moment. -/
theorem ae_tendsto_eigenvalues₀_card_sub_one_sampleCovariance_of_ratio_one
    (hx : ∀ ij, HasLaw (x ij) ν P) (hindep : iIndepFun x P) (h2 : MemLp id 2 ν)
    (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 1)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (isHermitian_sampleCovariance
      (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω)).eigenvalues₀
        ⟨Fintype.card (Fin (p n)) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have : IsProbabilityMeasure ν := (hx (0, 0)).isProbabilityMeasure_iff.1 ‹_›
  have hdim : Tendsto p atTop atTop := (tendsto_natCast_atTop_iff (R := ℝ)).1
    ((tendsto_atTop_iff_of_tendsto_div_nhds_one hp).2 tendsto_natCast_atTop_atTop)
  let b := ∫ z, z ∂ν
  let v := ∫ z, ‖z - b‖ ^ 2 ∂ν
  by_cases hv : 0 < v
  · have hzero : 0 ∈ (marchenkoPastur 1).support := by simp
    have hcont : Continuous (v * ·) := continuous_const.mul continuous_id
    have hsupp : 0 ∈ (((marchenkoPastur 1).toProbabilityMeasure.map (v * ·)) :
        Measure ℝ).support := by
      have h := Measure.mem_support_map_of_continuousAt hcont.measurable.aemeasurable
        hcont.continuousAt hzero
      simpa only [ProbabilityMeasure.toMeasure_map, Measure.coe_toProbabilityMeasure, mul_zero]
        using h
    filter_upwards [ae_tendsto_spectralMeasure_centered_sampleCovariance_of_pos_variance
      hx hindep (y := 1) one_pos (by simpa using hp) hv] with ω hω
    let X (n : ℕ) := Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω
    have hMP := (tendsto_spectralMeasure_sampleCovariance_sub_const_iff X (fun _ _ ↦ b)
      (by simpa only [Fintype.card_fin] using hdim)).1 hω
    exact tendsto_order.2 ⟨fun c hc ↦ .of_forall fun _ ↦
      hc.trans_le ((posSemidef_sampleCovariance _).eigenvalues₀_nonneg _), fun c hc ↦
      eventually_eigenvalues₀_card_sub_one_lt_of_tendsto_spectralMeasure hMP hsupp hc⟩
  · have hv₀ : v = 0 := le_antisymm (le_of_not_gt hv) (integral_nonneg fun _ ↦ sq_nonneg _)
    have hmem : MemLp (fun z ↦ z - b) 2 ν := h2.sub (memLp_const b)
    have hz := (integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _)
      (hmem.integrable_norm_pow two_ne_zero)).1 hv₀
    have hconst : ∀ᵐ z ∂ν, z = b := by
      filter_upwards [hz] with z hz
      have hn : ‖z - b‖ = 0 := by simpa only [sq_eq_zero_iff, Pi.zero_apply] using hz
      exact sub_eq_zero.mp (norm_eq_zero.mp hn)
    filter_upwards [ae_all_iff.2 fun ij ↦ (hx ij).ae hconst] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hdim.eventually_gt_atTop 1] with n hn
    let X : Matrix (Fin (p n)) (Fin n) ℂ := Matrix.of fun i j ↦ x (i, j) ω
    have hX : X = vecMulVec (fun _ ↦ b) (fun _ ↦ 1) := by
      ext i j
      simp only [X, Matrix.of_apply, hω (i, j), vecMulVec_apply, mul_one]
    have hrank : (sampleCovariance X).rank ≤ 1 := by
      rw [rank_sampleCovariance, hX]
      exact rank_vecMulVec_le _ _
    exact ((posSemidef_sampleCovariance X).eigenvalues₀_eq_zero_of_rank_le hrank _
      (by simpa only [Fintype.card_fin] using Nat.le_sub_one_of_lt hn)).symm

/-- Under the fourth-moment hypotheses for the lower covariance edge, suppose the normalized
centered truncations at `n ^ a`, with `1 / 4 < a < 1 / 2`, satisfy the almost-sure growth bound
on row blocks of non-backtracking walk matrices. Then, for an aspect ratio `0 < y ≤ 1`, the least
eigenvalue of the original sample covariance converges almost surely to `(1 - √y) ^ 2`. -/
theorem ae_tendsto_eigenvalues₀_card_sub_one_sampleCovariance_of_nonbacktracking
    (hx : ∀ ij, HasLaw (x ij) ν P) (hindep : iIndepFun x P)
    (hmean : ∫ z, z ∂ν = 0) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1) (h4 : MemLp id 4 ν)
    (hy : 0 < y) (hy₁ : y ≤ 1) (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 (y : ℝ)))
    {a : ℝ} (ha : 1 / 4 < a) (ha' : a < 1 / 2)
    (hwalk :
      let Y (n : ℕ) (ω : Ω) : Matrix (Fin (p n)) (Fin n) ℂ := (√(n : ℝ))⁻¹ •
        Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦
          centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω
      ∀ᵐ ω ∂P, ∃ (C : ℝ) (d : ℕ), ∀ l : ℕ, ∀ᶠ n in atTop,
        ‖(nonbacktrackingPow (fromBlocks 0 (Y n ω) (Y n ω)ᴴ 0) (2 * l)).toBlocks₁₁‖ ≤
          C * ((l : ℝ) + 1) ^ d * √y ^ l) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (isHermitian_sampleCovariance
      (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω)).eigenvalues₀
        ⟨Fintype.card (Fin (p n)) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩)
      atTop (𝓝 ((1 - √y) ^ 2)) := by
  filter_upwards [marchenkoPastur_ae hx hindep hmean hvar hy hp, hwalk,
    ae_degrees_and_norm_sub_centeredTruncation hx hindep hmean hvar h4 hp ha ha'] with ω hMP hw
    ⟨hd, hnorm⟩
  let X (n : ℕ) : Matrix (Fin (p n)) (Fin n) ℂ := Matrix.of fun i j ↦ x (i, j) ω
  let T (n : ℕ) : Matrix (Fin (p n)) (Fin n) ℂ := Matrix.of fun i j ↦
    centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω
  have hlow := eventually_lt_eigenvalues₀_sampleCovariance_of_nonbacktracking
    (X := X) (T := T) hy₁ (by simpa only [X, T, Fintype.card_fin] using hnorm)
    (by simpa only [T, Fintype.card_fin] using hd) (by simpa only [T, Fintype.card_fin] using hw)
  exact (tendsto_eigenvalues₀_card_sub_one_iff_of_tendsto_marchenkoPastur hMP).2
    fun c hc ↦ (hlow c hc).mono fun _ h ↦ h _

section ConjTranspose

/-- Under the fourth-moment hypotheses for the lower covariance edge and aspect ratio `y > 1`,
normalize the adjoints of the centered truncated corners by `√(p n)`. Suppose the row blocks of
their non-backtracking walk matrices satisfy the almost-sure growth bound for aspect ratio
`y⁻¹`. Almost surely the least eigenvalue is eventually zero, the least positive eigenvalue
is eventually defined, and the latter converges to `(√y - 1) ^ 2`. -/
theorem ae_tendsto_sInf_pos_eigenvalues₀_sampleCovariance_of_nonbacktracking
    (hx : ∀ ij, HasLaw (x ij) ν P) (hindep : iIndepFun x P)
    (hmean : ∫ z, z ∂ν = 0) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1) (h4 : MemLp id 4 ν)
    (hy : 1 < y) (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 (y : ℝ)))
    {a : ℝ} (ha : 1 / 4 < a) (ha' : a < 1 / 2)
    (hwalk :
      let Z (n : ℕ) (ω : Ω) : Matrix (Fin n) (Fin (p n)) ℂ := (√(p n : ℝ))⁻¹ •
        (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦
          centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω)ᴴ
      ∀ᵐ ω ∂P, ∃ (C : ℝ) (d : ℕ), ∀ l : ℕ, ∀ᶠ n in atTop,
        ‖(nonbacktrackingPow (fromBlocks 0 (Z n ω) (Z n ω)ᴴ 0) (2 * l)).toBlocks₁₁‖ ≤
          C * ((l : ℝ) + 1) ^ d * √(↑(y⁻¹) : ℝ) ^ l) :
    let X (n : ℕ) (ω : Ω) : Matrix (Fin (p n)) (Fin n) ℂ := Matrix.of fun i j ↦ x (i, j) ω
    let S (n : ℕ) (ω : Ω) := {s | 0 < s} ∩
      Set.range (isHermitian_sampleCovariance (X n ω)).eigenvalues₀
    ∀ᵐ ω ∂P, (∀ᶠ n in atTop, (isHermitian_sampleCovariance (X n ω)).eigenvalues₀
        ⟨Fintype.card (Fin (p n)) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩ = 0 ∧
        IsLeast (S n ω) (sInf (S n ω))) ∧
      Tendsto (fun n ↦ sInf (S n ω)) atTop (𝓝 ((√y - 1) ^ 2)) := by
  have hy₀ : 0 < y := zero_lt_one.trans hy
  have hy' : (1 : ℝ) < y := by exact_mod_cast hy
  have hratio : Tendsto (fun n : ℕ ↦ (n : ℝ) / p n) atTop (𝓝 ((y : ℝ)⁻¹)) := by
    simpa only [inv_div] using hp.inv₀ (by exact_mod_cast hy₀.ne')
  filter_upwards [marchenkoPastur_ae hx hindep hmean hvar hy₀ hp, hwalk,
    ae_degrees_and_norm_sub_centeredTruncation hx hindep hmean hvar h4 hp ha ha'] with ω hMP hw
    ⟨hd, hnorm⟩
  let X (n : ℕ) : Matrix (Fin (p n)) (Fin n) ℂ := Matrix.of fun i j ↦ x (i, j) ω
  let T (n : ℕ) : Matrix (Fin (p n)) (Fin n) ℂ := Matrix.of fun i j ↦
    centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω
  let Y (n : ℕ) := (√(n : ℝ))⁻¹ • T n
  let Z (n : ℕ) := (√(p n : ℝ))⁻¹ • (T n)ᴴ
  have hscale (n : ℕ) (hn : 0 < n) : √((n : ℝ) / p n) * (√(n : ℝ))⁻¹ = (√(p n : ℝ))⁻¹ := by
    rw [Real.sqrt_div (by positivity), div_eq_mul_inv, mul_right_comm,
      mul_inv_cancel₀ (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)).ne', one_mul]
  have hz : ∀ᶠ n in atTop, Z n = √((n : ℝ) / p n) • (Y n)ᴴ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Y, Z, conjTranspose_smul, star_trivial, smul_smul, hscale n hn]
  have hdeg := eventually_row_col_norm_sq_normalized_conjTranspose (Y := Y) hy₀.ne'
    (by simpa only [Fintype.card_fin] using hratio) hd
  have hnorm' : Tendsto (fun n ↦ ‖(X n)ᴴ - (T n)ᴴ‖ / √(p n : ℝ)) atTop (𝓝 0) := by
    have h := hratio.sqrt.mul hnorm
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    calc
      √((n : ℝ) / p n) * (‖X n - T n‖ / √(n : ℝ)) =
          ‖X n - T n‖ * (√((n : ℝ) / p n) * (√(n : ℝ))⁻¹) := by
        rw [div_eq_mul_inv ‖X n - T n‖, mul_left_comm]
      _ = _ := by
        rw [hscale n hn, ← conjTranspose_sub, l2_opNorm_conjTranspose, div_eq_mul_inv]
  have hlow := eventually_lt_eigenvalues₀_sampleCovariance_of_nonbacktracking
    (X := fun n ↦ (X n)ᴴ) (T := fun n ↦ (T n)ᴴ) ((inv_le_one₀ hy₀).2 hy.le)
    (by simpa only [Fintype.card_fin] using hnorm')
    (fun ε hε ↦ by
      filter_upwards [hz, hdeg ε hε] with n hn hd'
      simp only [Fintype.card_fin] at hd'
      rw [← hn] at hd'
      simpa only [Fintype.card_fin, NNReal.coe_inv] using hd')
    (by simpa only [Fintype.card_fin] using hw)
  obtain ⟨hleast, hlim⟩ := tendsto_sInf_pos_eigenvalues₀_sampleCovariance_of_tendsto_marchenkoPastur
    hMP (eventually_lt_eigenvalues₀_sampleCovariance_of_conjTranspose
      (by simpa only [Fintype.card_fin] using hp) hlow)
  exact ⟨(eventually_eigenvalues₀_card_sub_one_sampleCovariance_eq_zero_of_one_lt_ratio X hy'
    (by simpa only [Fintype.card_fin] using hp)).and hleast, hlim⟩

end ConjTranspose

end TauCeti.Probability
