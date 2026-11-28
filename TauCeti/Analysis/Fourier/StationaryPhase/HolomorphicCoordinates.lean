/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.StationaryPhase.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.Analysis.Normed.Operator.Basic

/-! # The averaged complex Hessian -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff

namespace TauCeti

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private local instance : NormedAddCommGroup (E →L[ℂ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℂ (E →L[ℂ] ℂ) :=
  ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℂ] E →L[ℂ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℂ (E →L[ℂ] E →L[ℂ] ℂ) :=
  ContinuousLinearMap.toNormedSpace
private local instance : NormedSpace ℝ (E →L[ℂ] E →L[ℂ] ℂ) :=
  NormedSpace.complexToReal

private theorem smul_mem_ball_zero {x : E} {r : ℝ}
    (hx : x ∈ ball 0 r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • x ∈ ball 0 r := by
  rw [mem_ball_zero_iff] at hx ⊢
  rw [norm_smul, Real.norm_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hx

variable [FiniteDimensional ℂ E]

private noncomputable def averagedHessian (g : E → ℂ) (x : E) : E →L[ℂ] E →L[ℂ] ℂ :=
  ∫ t in Icc (0 : ℝ) 1, (2 * (1 - t)) • fderiv ℂ (fderiv ℂ g) (t • x)

omit [FiniteDimensional ℂ E] in
private theorem continuousOn_averagedHessian_integrand {g : E → ℂ} {r : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball 0 r)) {x : E} (hx : x ∈ ball 0 r) :
    ContinuousOn (fun t : ℝ ↦ (2 * (1 - t)) • fderiv ℂ (fderiv ℂ g) (t • x)) (Icc 0 1) :=
  (by fun_prop : Continuous fun t : ℝ ↦ 2 * (1 - t)).continuousOn.smul
    ((hg.fderiv_of_isOpen isOpen_ball |>.fderiv_of_isOpen isOpen_ball).continuousOn.comp
      ((continuous_id.smul continuous_const).continuousOn) (fun _ ht ↦ smul_mem_ball_zero hx ht))

omit [FiniteDimensional ℂ E] in
private theorem averagedHessian_apply {g : E → ℂ} {r : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball 0 r)) {x : E} (hx : x ∈ ball 0 r) (u v : E) :
    averagedHessian g x u v =
      ∫ t in Icc (0 : ℝ) 1, (2 * (1 - t)) • fderiv ℂ (fderiv ℂ g) (t • x) u v := by
  let D := fun t : ℝ ↦ (2 * (1 - t)) • fderiv ℂ (fderiv ℂ g) (t • x)
  have hi : IntegrableOn D (Icc 0 1) :=
    (continuousOn_averagedHessian_integrand hg hx).integrableOn_compact isCompact_Icc
  change ((∫ t in Icc (0 : ℝ) 1, D t) u) v = _
  rw [ContinuousLinearMap.integral_apply hi]
  rw [ContinuousLinearMap.integral_apply]
  · rfl
  · exact ((ContinuousLinearMap.apply ℂ (E →L[ℂ] ℂ) u).integrable_comp hi)

private theorem analyticOnNhd_averagedHessian {g : E → ℂ} {r : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball 0 r)) {M : ℝ}
    (hM : ∀ x ∈ ball 0 r, ‖fderiv ℂ (fderiv ℂ g) x‖ ≤ M) :
    AnalyticOnNhd ℂ (averagedHessian g) (ball 0 r) := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have hAE : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  apply analyticOnNhd_integral_of_dominated (μ := μ) (F := fun x t ↦
    (2 * (1 - t)) • fderiv ℂ (fderiv ℂ g) (t • x)) isOpen_ball
  · intro x hx
    exact (continuousOn_averagedHessian_integrand hg hx).aestronglyMeasurable measurableSet_Icc
  · intro x hx
    refine ⟨ball 0 r, isOpen_ball.mem_nhds hx, fun _ ↦ 2 * M, integrable_const _, ?_⟩
    filter_upwards [hAE] with t ht y hy
    rw [norm_smul, Real.norm_of_nonneg (by linarith [ht.2])]
    exact mul_le_mul (by linarith [ht.1]) (hM _ (smul_mem_ball_zero hy ht))
      (norm_nonneg _) (by positivity)
  · filter_upwards [hAE] with t ht
    have hlin : DifferentiableOn ℂ (fun x : E ↦ t • x) (ball 0 r) := by
      have heq : (fun x : E ↦ t • x) = (t : ℂ) • id := by
        funext x
        exact RCLike.real_smul_eq_coe_smul (K := ℂ) t x
      rw [heq]
      exact differentiableOn_id.const_smul (t : ℂ)
    have hD := ((hg.fderiv_of_isOpen isOpen_ball).fderiv_of_isOpen isOpen_ball).differentiableOn
    have hcomp := hD.comp hlin (fun _ hx ↦ smul_mem_ball_zero hx ht)
    exact hcomp.const_smul (2 * (1 - t))

omit [FiniteDimensional ℂ E] in
private theorem averagedHessian_zero (g : E → ℂ) :
    averagedHessian g 0 = fderiv ℂ (fderiv ℂ g) 0 := by
  have h : (∫ t in Icc (0 : ℝ) 1, 2 * (1 - t)) = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub
        (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun t : ℝ ↦ t)
        intervalIntegrable_const
        ((continuous_id' : Continuous (fun t : ℝ ↦ t)).intervalIntegrable 0 1),
      intervalIntegral.integral_const, integral_id]
    norm_num
  rw [averagedHessian]
  simp only [smul_zero]
  rw [integral_smul_const, h, one_smul]

omit [FiniteDimensional ℂ E] in
private theorem averagedHessian_symmetric {g : E → ℂ} {r : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball 0 r)) {x : E} (hx : x ∈ ball 0 r) (u v : E) :
    averagedHessian g x u v = averagedHessian g x v u := by
  rw [averagedHessian_apply hg hx, averagedHessian_apply hg hx]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have h : ContDiffAt ℂ ω g (t • x) :=
    (hg _ (smul_mem_ball_zero hx ht)).contDiffAt
  exact congrArg ((2 * (1 - t)) • ·) (h.isSymmSndFDerivAt_of_omega u v)

omit [FiniteDimensional ℂ E] in
private theorem taylor_averagedHessian {g : E → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (ball 0 r)) {x : E} (hx : x ∈ ball 0 r) :
    g x = g 0 + fderiv ℂ g 0 x + (2 : ℝ)⁻¹ • averagedHessian g x x x := by
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : AnalyticAt ℂ g (0 + t • x) :=
    hg _ (by simpa only [zero_add] using smul_mem_ball_zero hx ht)
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (x := 0) (y := x)
    (fun t ht ↦ ((hseg t ht).restrictScalars (𝕜 := ℝ)).contDiffAt)
  simp only [zero_add, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply,
    iteratedFDeriv_one_apply, zero_add, pow_one] at h
  rw [averagedHessian_apply hg hx]
  rw [← integral_smul]
  calc
    g x = g 0 + fderiv ℝ g 0 x +
        ∫ t in (0 : ℝ)..1, (1 - t) • iteratedFDeriv ℝ 2 g (t • x) (fun _ ↦ x) := h
    _ = _ := by
      have hg₀ := (hg 0 (mem_ball_self hr)).differentiableAt
      rw [hg₀.fderiv_restrictScalars (𝕜 := ℝ),
        intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
      congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      have hdiff : ContDiffAt ℂ 2 g (t • x) :=
        (hg _ (smul_mem_ball_zero hx ht)).contDiffAt
      dsimp only
      rw [← hdiff.restrictScalars_iteratedFDeriv (𝕜 := ℝ), smul_smul]
      change (1 - t) • iteratedFDeriv ℂ 2 g (t • x) (fun _ ↦ x) =
        (2⁻¹ * (2 * (1 - t)) : ℝ) • fderiv ℂ (fderiv ℂ g) (t • x) x x
      rw [iteratedFDeriv_two_apply]
      congr 1
      ring

end

noncomputable section

private local instance {n : ℕ} : NormedAddCommGroup ((Fin n → ℂ) →L[ℂ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance {n : ℕ} : NormedSpace ℂ ((Fin n → ℂ) →L[ℂ] ℂ) :=
  ContinuousLinearMap.toNormedSpace
private local instance {n : ℕ} : NormedAddCommGroup ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ) →L[ℂ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance {n : ℕ} : NormedSpace ℂ ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ) →L[ℂ] ℂ) :=
  ContinuousLinearMap.toNormedSpace

open scoped Matrix.Norms.Operator in
private def matrixOfContinuousBilin (n : ℕ) :
    ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ) →L[ℂ] ℂ) →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (show ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ from
    { toFun := fun B ↦ B.toBilinForm.toMatrix'
      map_add' := by intro B C; ext i j; simp [LinearMap.BilinForm.toMatrix'_apply]
      map_smul' := by intro c B; ext i j; simp [LinearMap.BilinForm.toMatrix'_apply] }
    ).toContinuousLinearMap

open scoped Matrix.Norms.Operator in
/-- A bounded holomorphic phase has a uniformly bounded, analytic matrix in its quadratic Taylor
formula. At zero the matrix is the Hessian of the phase. -/
theorem exists_bounded_analytic_taylor_matrix (n : ℕ) {r : ℝ} (hr : 0 < r) (Λ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : (Fin n → ℂ) → ℂ),
      AnalyticOnNhd ℂ g (ball 0 (2 * r)) → (∀ x ∈ ball 0 (2 * r), ‖g x‖ ≤ Λ) →
      ∃ B : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ,
        AnalyticOnNhd ℂ B (ball 0 r) ∧ (∀ x ∈ ball 0 r, ‖B x‖ ≤ M) ∧
        B 0 = (Matrix.of fun i j : Fin n ↦
          iteratedFDeriv ℂ 2 g 0 ![Pi.single i 1, Pi.single j 1]) ∧
        (∀ x ∈ ball 0 r, (B x).IsSymm) ∧
        (∀ x ∈ ball 0 r, g x = g 0 + fderiv ℂ g 0 x + (2⁻¹ : ℂ) * (B x).toBilin' x x) := by
  let T := matrixOfContinuousBilin n
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedFDeriv_le_of_analyticOnNhd_ball
    (E := Fin n → ℂ) (F := ℂ) 2 (c := 0) (show r < 2 * r by linarith)
  let D := max 0 (C * Λ)
  have hD : 0 ≤ D := le_max_left ..
  refine ⟨n * (2 * D), mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hD), ?_⟩
  intro g hg hob
  have hnorm (x : Fin n → ℂ) (hx : x ∈ ball 0 r) : ‖fderiv ℂ (fderiv ℂ g) x‖ ≤ D := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℂ), norm_iteratedFDeriv_fderiv]
    exact (hC g Λ hg hob x (ball_subset_closedBall hx)).trans (le_max_right ..)
  let B := averagedHessian g
  have hlocal := hg.mono (ball_subset_ball (show r ≤ 2 * r by linarith))
  have hb := analyticOnNhd_averagedHessian hlocal hnorm
  have heq (Q : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) →L[ℂ] ℂ) :
      (T Q).toBilin' = Q.toBilinForm :=
    Matrix.toBilin'_toMatrix' Q.toBilinForm
  refine ⟨T ∘ B, fun x hx ↦ (T.analyticAt (B x)).comp (hb x hx), ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hB : ‖B x‖ ≤ 2 * D := by
      dsimp only [B, averagedHessian]
      apply (norm_setIntegral_le_of_norm_le_const (C := 2 * D) (s := Icc (0 : ℝ) 1)
        (isCompact_Icc.measure_lt_top) fun t ht ↦ ?_).trans_eq
        (by simp [Real.volume_real_Icc])
      rw [norm_smul, Real.norm_of_nonneg (by linarith [ht.2])]
      exact mul_le_mul (by linarith [ht.1]) (hnorm (t • x) (smul_mem_ball_zero hx ht))
        (norm_nonneg _) (by norm_num)
    have hentry (i j : Fin n) : ‖T (B x) i j‖ ≤ 2 * D := by
      change ‖(B x).toBilinForm.toMatrix' i j‖ ≤ 2 * D
      rw [LinearMap.BilinForm.toMatrix'_apply, ContinuousLinearMap.toBilinForm_apply]
      exact ((ContinuousLinearMap.le_opNorm _ _).trans (by
        rw [Pi.norm_single, norm_one, mul_one]
        exact (ContinuousLinearMap.le_opNorm _ _).trans_eq
          (by rw [Pi.norm_single, norm_one, mul_one]))).trans hB
    let P : NNReal := ⟨n * (2 * D), by positivity⟩
    change (‖T (B x)‖₊ : ℝ) ≤ (P : ℝ)
    rw [NNReal.coe_le_coe, Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ ↦ NNReal.coe_le_coe.mp ?_
    rw [NNReal.coe_sum]
    change (∑ j : Fin n, ‖T (B x) i j‖) ≤ n * (2 * D)
    exact (Finset.sum_le_sum fun j _ ↦ hentry i j).trans_eq (by simp)
  · ext i j
    change (B 0).toBilinForm.toMatrix' i j = _
    rw [LinearMap.BilinForm.toMatrix'_apply, ContinuousLinearMap.toBilinForm_apply]
    simp [B, averagedHessian_zero, iteratedFDeriv_two_apply]
  · intro x hx
    rw [← Matrix.isSymm_toBilin'_iff_isSymm, Function.comp_apply, heq]
    exact ⟨fun u v ↦ averagedHessian_symmetric hlocal hx u v⟩
  · intro x hx
    change g x = g 0 + fderiv ℂ g 0 x + (2⁻¹ : ℂ) * (T (B x)).toBilin' x x
    rw [heq]
    change g x = g 0 + fderiv ℂ g 0 x + (2⁻¹ : ℂ) * averagedHessian g x x x
    rw [← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_inv]
    exact taylor_averagedHessian hr hlocal hx

end

end TauCeti
