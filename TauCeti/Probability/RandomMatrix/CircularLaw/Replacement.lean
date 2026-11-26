/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.ResolventReplacement

import TauCeti.Analysis.Matrix.L2OpNorm.Single
import TauCeti.Data.Matrix.Basis
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.MeasureTheory.Integral.TruncatedMoment

/-!
# Finite-variance replacement for Hermitian block resolvents

Replacing independent complex entries with entries having the same first and second moments
preserves the asymptotic expected normalized resolvent trace of a shifted Hermitian dilation.
The entries are scaled by the reciprocal square root of the matrix dimension. Each entry and
its conjugate are replaced together, so its real and imaginary parts may be dependent. The
moment hypotheses match the complex mean, the complex second moment, and the second absolute
moment.

## References

* T. Tao, *Topics in Random Matrix Theory*, AMS, 2012, §2.2.4 (Lindeberg swapping).
* C. Bordenave and D. Chafaï, *Around the circular law*, Probab. Surv. 9 (2012), 1–89, §5.
-/

public section

noncomputable section

open Filter Finset MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace Matrix

private theorem fromBlocks_add_sum_complexPerturbation_single
    {k : Type*} [Fintype k] [DecidableEq k] (D : Matrix k k ℂ)
    (a : ℝ) (x : k × k → ℂ) :
    fromBlocks 0 D Dᴴ 0 +
        ∑ i : k × k, (x i • single (Sum.inl i.1) (Sum.inr i.2) (a : ℂ) +
          conj (x i) • (single (Sum.inl i.1) (Sum.inr i.2) (a : ℂ))ᴴ) =
      fromBlocks 0 (D + a • Matrix.of (fun i j ↦ x (i, j)))
        (D + a • Matrix.of (fun i j ↦ x (i, j)))ᴴ 0 := by
  have hsum :
      ∑ i : k × k, (x i • single (Sum.inl i.1) (Sum.inr i.2) (a : ℂ) +
        conj (x i) • (single (Sum.inl i.1) (Sum.inr i.2) (a : ℂ))ᴴ) =
        fromBlocks 0 (a • Matrix.of (fun i j ↦ x (i, j)))
          (a • Matrix.of (fun i j ↦ x (i, j)))ᴴ 0 := by
    ext (i | i) (j | j)
    · simp [Matrix.sum_apply, conjTranspose_single]
    · simp [Matrix.sum_apply, conjTranspose_single, Matrix.single_apply,
        Complex.real_smul, mul_comm, ← Prod.mk.injEq]
    · simp [Matrix.sum_apply, conjTranspose_single, Matrix.single_apply,
        Complex.real_smul, mul_comm, ← Prod.mk.injEq, and_comm]
    · simp [Matrix.sum_apply, conjTranspose_single]
  simp only [hsum, fromBlocks_add, conjTranspose_add, zero_add]

private theorem normalized_rank_factor (k : ℕ) (b : ℝ) :
    ‖((2 : ℂ) * (k + 1))⁻¹‖ * ((k + 1 : ℝ) ^ 2 * 2) *
      b ^ 3 * (2 * (Real.sqrt (k + 1))⁻¹) ^ 2 = 4 * b ^ 3 := by
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hsize : ‖(k + 1 : ℂ)‖ = (k : ℝ) + 1 := by
    exact_mod_cast Complex.norm_natCast (k + 1)
  have ha : (Real.sqrt (k + 1))⁻¹ ^ 2 = ((k : ℝ) + 1)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ) + 1)]
  rw [norm_inv, norm_mul, htwo, hsize, mul_pow, ha]
  field_simp
  ring

private theorem norm_sub_integral_normalized_trace_inv_fromBlocks_le
    (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    (k : ℕ) (D : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Y (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let f x := ((2 : ℂ) * (k + 1))⁻¹ * (fromBlocks 0 (Y x) (Y x)ᴴ 0 - z • 1)⁻¹.trace
    let b := |z.im|⁻¹
    let c := 2 * (Real.sqrt (k + 1))⁻¹
    ‖(∫ x, f x ∂Measure.pi (fun _ ↦ μ)) - ∫ x, f x ∂Measure.pi (fun _ ↦ ν)‖ ≤
      4 * b ^ 3 *
        ((∫ w, ‖w‖ ^ 2 * min (b * c * ‖w‖) 1 ∂μ) +
          ∫ w, ‖w‖ ^ 2 * min (b * c * ‖w‖) 1 ∂ν) := by
  dsimp only
  let b := |z.im|⁻¹
  let c := 2 * (Real.sqrt (k + 1))⁻¹
  let a : ℝ := (Real.sqrt (k + 1))⁻¹
  let B (i : Fin (k + 1) × Fin (k + 1)) :
      Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) ℂ :=
    single (Sum.inl i.1) (Sum.inr i.2) (a : ℂ)
  let A := fromBlocks 0 D Dᴴ 0
  have hA : A.IsHermitian := by simp [A, IsHermitian, fromBlocks_conjTranspose]
  have h := hA.norm_integral_pi_trace_inv_add_sum_smul_add_conj_smul_sub_le
    B hz (fun _ ↦ μ) (fun _ ↦ ν) (fun _ ↦ hμ) (fun _ ↦ hν)
    (fun _ ↦ hmean) (fun _ ↦ hsq) (fun _ ↦ habs)
  have hnorm (i) : ‖B i‖ = a := by
    have ha : 0 ≤ a := by positivity
    simp only [B, l2_opNorm_single, Complex.norm_real, Real.norm_of_nonneg ha]
  have hrank (i) : (B i).rank ≤ 1 := by
    dsimp only [B]
    rw [single_eq_smul_single_one _ _ (a : ℂ), smul_eq_diagonal_mul,
      single_eq_single_vecMulVec_single]
    exact (rank_mul_le_right _ _).trans (rank_vecMulVec_le _ _)
  have heq (x : Fin (k + 1) × Fin (k + 1) → ℂ) :
      A + ∑ i, (x i • B i + conj (x i) • (B i)ᴴ) =
        fromBlocks 0 (D + a • Matrix.of (fun i j ↦ x (i, j)))
          (D + a • Matrix.of (fun i j ↦ x (i, j)))ᴴ 0 :=
    fromBlocks_add_sum_complexPerturbation_single D a x
  simp only [heq, hnorm] at h
  rw [← sum_mul, ← sum_mul, ← sum_mul] at h
  rw [integral_const_mul, integral_const_mul, ← mul_sub, norm_mul]
  refine (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans ?_
  -- There are (k + 1)² entries and each changes only two rows of the dilation.
  have hsum : (∑ i : Fin (k + 1) × Fin (k + 1), (2 * (B i).rank : ℝ)) ≤
      (k + 1 : ℝ) ^ 2 * 2 := by
    calc
      _ ≤ ∑ _i : Fin (k + 1) × Fin (k + 1), (2 : ℝ) := by
        refine sum_le_sum fun i _ ↦ ?_
        have hi : ((B i).rank : ℝ) ≤ 1 := by exact_mod_cast hrank i
        linarith
      _ = _ := by simp [Fintype.card_prod, sq]
  let E := (∫ w, ‖w‖ ^ 2 * min (b * c * ‖w‖) 1 ∂μ) + ∫ w, ‖w‖ ^ 2 * min (b * c * ‖w‖) 1 ∂ν
  have hE : 0 ≤ E :=
    add_nonneg (integral_nonneg fun _ ↦ by positivity)
      (integral_nonneg fun _ ↦ by positivity)
  calc
    _ ≤ ‖((2 : ℂ) * (k + 1))⁻¹‖ * (((k + 1 : ℝ) ^ 2 * 2) * b ^ 3 * (2 * a) ^ 2 * E) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum (by positivity))
          (sq_nonneg _)) hE
    _ = (‖((2 : ℂ) * (k + 1))⁻¹‖ * ((k + 1 : ℝ) ^ 2 * 2) * b ^ 3 * (2 * a) ^ 2) * E := by ring
    _ = _ := by rw [normalized_rank_factor k b]

end Matrix

namespace MeasureTheory.Measure

open Matrix

/-- For two i.i.d. complex entry product laws of finite second moment whose mixed moments
match through degree two, the expected normalized resolvent traces of their Hermitian
dilations have vanishing difference. The matrices are scaled by the reciprocal square root
of their dimension before adding the same arbitrary deterministic matrix. -/
theorem tendsto_sub_integral_normalized_trace_inv_fromBlocks
    (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) μ)
    (hν : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) ν)
    (hmean : (∫ w : ℂ, w ∂μ) = ∫ w : ℂ, w ∂ν)
    (hsq : (∫ w : ℂ, w ^ 2 ∂μ) = ∫ w : ℂ, w ^ 2 ∂ν)
    (habs : (∫ w : ℂ, ‖w‖ ^ 2 ∂μ) = ∫ w : ℂ, ‖w‖ ^ 2 ∂ν)
    (D : ∀ k : ℕ, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Y (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D k + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let f (k : ℕ) x := ((2 : ℂ) * (k + 1))⁻¹ *
      (fromBlocks 0 (Y k x) (Y k x)ᴴ 0 - z • 1)⁻¹.trace
    Tendsto (fun k : ℕ ↦ (∫ x, f k x ∂Measure.pi (fun _ ↦ μ)) -
      ∫ x, f k x ∂Measure.pi (fun _ ↦ ν)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦
    norm_sub_integral_normalized_trace_inv_fromBlocks_le μ ν hμ hν hmean hsq habs k (D k) hz) ?_
  have hc : Tendsto (fun k : ℕ ↦ (Real.sqrt ((k : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
  have hscale : Tendsto (fun k : ℕ ↦ |z.im|⁻¹ * (2 * (Real.sqrt (k + 1))⁻¹))
      atTop (𝓝[Set.Ici 0] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k ↦ ?_⟩
    · simpa only [mul_zero] using (hc.const_mul (2 : ℝ)).const_mul |z.im|⁻¹
    · exact Set.mem_Ici.mpr (by positivity)
  have hsum := (hμ.tendsto_integral_norm_sq_mul_min_mul_one.comp hscale).add
    (hν.tendsto_integral_norm_sq_mul_min_mul_one.comp hscale)
  have hlim := hsum.const_mul (4 * |z.im|⁻¹ ^ (3 : ℕ))
  simpa only [Function.comp_apply, add_zero, mul_zero] using hlim

end MeasureTheory.Measure

namespace ProbabilityTheory.HasLaw

open Matrix

/-- Finite-variance replacement for the expected normalized resolvent traces of shifted
Hermitian dilations on arbitrary sample spaces. The joint product laws encode independence
of the entries within each matrix, with no restriction on coupling across dimensions. -/
theorem tendsto_sub_integral_normalized_trace_inv_fromBlocks
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
    (D : ∀ k : ℕ, Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    let Z (k : ℕ) (x : Fin (k + 1) × Fin (k + 1) → ℂ) :=
      D k + (Real.sqrt (k + 1))⁻¹ • Matrix.of (fun i j ↦ x (i, j))
    let f (k : ℕ) x := ((2 : ℂ) * (k + 1))⁻¹ *
      (fromBlocks 0 (Z k x) (Z k x)ᴴ 0 - z • 1)⁻¹.trace
    Tendsto (fun k ↦ (∫ ω, f k (X k ω) ∂P) - ∫ ω, f k (Y k ω) ∂Q) atTop (𝓝 0) := by
  intro Z f
  have hc (k : ℕ) : Continuous (f k) := by
    have hZ : Continuous (Z k) := by
      unfold Z
      fun_prop
    let H x := fromBlocks 0 (Z k x) (Z k x)ᴴ 0
    have hH : Continuous H :=
      continuous_const.matrix_fromBlocks hZ hZ.matrix_conjTranspose continuous_const
    have hh (x) : (H x).IsHermitian := by simp [H, IsHermitian, fromBlocks_conjTranspose]
    exact continuous_const.mul (hH.matrix_trace_inv_sub_smul_one hh hz)
  have hx (k) := (hX k).integral_comp (hc k).aestronglyMeasurable
  have hy (k) := (hY k).integral_comp (hc k).aestronglyMeasurable
  simp only [Function.comp_def] at hx hy
  simp_rw [hx, hy]
  exact μ.tendsto_sub_integral_normalized_trace_inv_fromBlocks ν hμ hν hmean hsq habs D hz

end ProbabilityTheory.HasLaw
