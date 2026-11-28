/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Fourier.StationaryPhase.SmoothCutoff
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-! # Integration by parts with a normalized phase derivative -/

public section

open Complex MeasureTheory Set
open scoped ContDiff

namespace TauCeti

noncomputable section

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ι : Type*} [Fintype ι]

private def divergenceAmplitude (w : ι → E) (v : ι → E → ℝ) (a : E → V) (x : E) : V :=
  ∑ i, fderiv ℝ (fun y ↦ v i y • a y) x (w i)

private theorem divergenceAmplitude_eq_zero {K : Set E} (hK : IsClosed K)
    (w : ι → E) (v : ι → E → ℝ) {a : E → V} (haK : ∀ x ∉ K, a x = 0) {x : E} (hx : x ∉ K) :
    divergenceAmplitude w v a x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have he : (fun y ↦ v i y • a y) =ᶠ[nhds x] fun _ ↦ 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    simp [haK y hy]
  simp [he.fderiv_eq]

private theorem contDiff_divergenceAmplitude {N : ℕ} (w : ι → E) {v : ι → E → ℝ} {a : E → V}
    (hv : ∀ i, ContDiff ℝ (N + 1 : ℕ) (v i)) (ha : ContDiff ℝ (N + 1 : ℕ) a) :
    ContDiff ℝ N (divergenceAmplitude w v a) := by
  apply ContDiff.sum
  intro i _
  exact (((hv i).smul ha).fderiv_right (m := N) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

private theorem norm_iteratedFDeriv_divergenceAmplitude_le {N j : ℕ} (hj : j ≤ N)
    {w : ι → E} (hw : ∀ i, ‖w i‖ ≤ 1) {v : ι → E → ℝ} {a : E → V}
    (hv : ∀ i, ContDiff ℝ (N + 1 : ℕ) (v i)) (ha : ContDiff ℝ (N + 1 : ℕ) a)
    {B S : ℝ} (x : E)
    (hvb : ∀ i k, k ≤ N + 1 → ‖iteratedFDeriv ℝ k (v i) x‖ ≤ B)
    (hab : ∀ k ≤ N + 1, ‖iteratedFDeriv ℝ k a x‖ ≤ S) :
    ‖iteratedFDeriv ℝ j (divergenceAmplitude w v a) x‖ ≤ Fintype.card ι * 2 ^ (N + 1) * B * S := by
  have hle : (j : ℕ∞ω) ≤ N := by exact_mod_cast hj
  have hc := fun i ↦ (((hv i).smul ha).fderiv_right (m := N)
    (by exact_mod_cast le_rfl)).clm_apply (contDiff_const (c := w i))
  change ‖iteratedFDeriv ℝ j
    (fun x ↦ ∑ i, fderiv ℝ (v i • a) x (w i)) x‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦ ((hc i).of_le hle).contDiffAt)]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i : ι, 2 ^ (N + 1) * B * S := Finset.sum_le_sum fun i _ ↦ by
      have hcd := ((hv i).smul ha).fderiv_right (m := N) (by exact_mod_cast le_rfl)
      refine (norm_iteratedFDeriv_clm_apply_const (c := w i) hcd.contDiffAt hle).trans ?_
      rw [norm_iteratedFDeriv_fderiv]
      refine (mul_le_of_le_one_left (norm_nonneg _) (hw i)).trans ?_
      exact norm_iteratedFDeriv_smul_le_of_uniform_bounds isOpen_univ (mem_univ x)
        (hv i).contDiffOn ha.contDiffOn (hvb i) hab (j + 1) (Nat.succ_le_succ hj)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

private def oscillation (φ : E → ℝ) (s : ℝ) (x : E) : ℂ :=
  exp (I * ((φ x / s : ℝ) : ℂ))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem norm_oscillation (φ : E → ℝ) (s : ℝ) (x : E) : ‖oscillation φ s x‖ = 1 := by
  simp [oscillation, norm_exp]

private theorem fderiv_oscillation_apply {φ : E → ℝ} (hφ : Differentiable ℝ φ) (s : ℝ)
    (x w : E) :
    fderiv ℝ (oscillation φ s) x w = (I / (s : ℂ)) * fderiv ℝ φ x w * oscillation φ s x := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x
    ((hφ x).hasFDerivAt.const_mul s⁻¹)).const_smul I |>.cexp
  simp only [← div_eq_inv_mul] at h
  rw [show fderiv ℝ (oscillation φ s) x = _ from h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, Pi.smul_apply, Function.comp_apply,
    ofRealCLM_apply, smul_eq_mul, oscillation]
  push_cast
  ring

private theorem contDiff_oscillation {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (s : ℝ) :
    ContDiff ℝ 1 (oscillation φ s) :=
  ((Complex.ofRealCLM.contDiff.comp (hφ.div_const s)).const_smul I).cexp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] [CompleteSpace V]

omit [CompleteSpace V] in
private theorem integral_oscillation_divergenceAmplitude {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) {K : Set E} (hK : IsCompact K)
    (w : ι → E) {v : ι → E → ℝ} (hv : ∀ i, ContDiff ℝ 1 (v i))
    (hone : ∀ x ∈ K, ∑ i, v i x * fderiv ℝ φ x (w i) = 1)
    {a : E → V} (ha : ContDiff ℝ 1 a) (haK : ∀ x ∉ K, a x = 0) (s : ℝ) :
    (I / (s : ℂ)) • (∫ x, oscillation φ s x • a x ∂μ) =
      -(∫ x, oscillation φ s x • divergenceAmplitude w v a x ∂μ) := by
  let f : ι → E → V := fun i x ↦ v i x • a x
  have hf (i) : ContDiff ℝ 1 (f i) := (hv i).smul ha
  have hfc (i) : HasCompactSupport (f i) :=
    HasCompactSupport.intro hK fun x hx ↦ by simp [f, haK x hx]
  have ho := contDiff_oscillation hφ s
  have hdf (i) : Continuous (fun x ↦ fderiv ℝ (f i) x (w i)) :=
    ((hf i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdo (i) : Continuous (fun x ↦ fderiv ℝ (oscillation φ s) x (w i)) :=
    (ho.continuous_fderiv (by simp)).clm_apply continuous_const
  have hA (i) : Integrable (fun x ↦ oscillation φ s x • fderiv ℝ (f i) x (w i)) μ :=
    (ho.continuous.smul (hdf i)).integrable_of_hasCompactSupport
      ((hfc i).fderiv_apply (𝕜 := ℝ) (w i)).smul_left
  have hB (i) : Integrable (fun x ↦ fderiv ℝ (oscillation φ s) x (w i) • f i x) μ :=
    ((hdo i).smul (hf i).continuous).integrable_of_hasCompactSupport (hfc i).smul_left
  have hIBP (i) := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := μ)
    (hB i) (hA i) ((ho.continuous.smul (hf i).continuous).integrable_of_hasCompactSupport
      (hfc i).smul_left)
    (fun x _ ↦ ho.differentiable (by simp) x) (fun x _ ↦ (hf i).differentiable (by simp) x)
  have hpt (x : E) : ∑ i, fderiv ℝ (oscillation φ s) x (w i) • f i x =
      (I / (s : ℂ)) • (oscillation φ s x • a x) := by
    by_cases hx : x ∈ K
    · simp_rw [f, fderiv_oscillation_apply (hφ.differentiable (by simp))]
      simp_rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      rw [← Finset.sum_smul]
      apply congrArg (fun c : ℂ ↦ c • a x)
      have he (i : ι) : I / (s : ℂ) * (fderiv ℝ φ x) (w i) * oscillation φ s x *
          v i x = (I / (s : ℂ) * oscillation φ s x) *
            (((v i x * fderiv ℝ φ x (w i) : ℝ)) : ℂ) := by push_cast; ring
      calc
        _ = ∑ i, (I / (s : ℂ) * oscillation φ s x) *
            (((v i x * fderiv ℝ φ x (w i) : ℝ)) : ℂ) := Finset.sum_congr rfl fun i _ ↦ he i
        _ = _ := by rw [← Finset.mul_sum, ← ofReal_sum, hone x hx, ofReal_one, mul_one]
    · simp [f, haK x hx]
  rw [← integral_smul]
  simp_rw [← hpt, divergenceAmplitude, Finset.smul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hA i)]
  rw [integral_finsetSum _ (fun i _ ↦ hB i), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hIBP i, neg_neg]

omit [CompleteSpace V] in
/-- Repeated integration by parts against a real phase with directional coefficients whose
pairing with the phase derivative equals one on the compact support of the amplitude. -/
theorem norm_integral_oscillation_le_of_directional_coefficients
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) {K : Set E} (hK : IsCompact K)
    {w : ι → E} (hw : ∀ i, ‖w i‖ ≤ 1) {v : ι → E → ℝ}
    (hone : ∀ x ∈ K, ∑ i, v i x * fderiv ℝ φ x (w i) = 1)
    (N : ℕ) (B : ℝ) (hB : 0 ≤ B) (hv : ∀ i, ContDiff ℝ N (v i))
    (hvb : ∀ i j, j ≤ N → ∀ x ∈ K, ‖iteratedFDeriv ℝ j (v i) x‖ ≤ B)
    {a : E → V} (ha : ContDiff ℝ N a) (haK : ∀ x ∉ K, a x = 0)
    {S : ℝ} (hS : 0 ≤ S) (hab : ∀ j ≤ N, ∀ x ∈ K, ‖iteratedFDeriv ℝ j a x‖ ≤ S)
    {s : ℝ} (hs : s ≠ 0) :
    ‖∫ x, Complex.exp (Complex.I * ((φ x / s : ℝ) : ℂ)) • a x ∂μ‖ ≤
      (Fintype.card ι * 2 ^ N * B) ^ N * μ.real K * S * |s| ^ N := by
  change ‖∫ x, oscillation φ s x • a x ∂μ‖ ≤ _
  induction N generalizing a S with
  | zero =>
    simp only [pow_zero, one_mul, mul_one]
    rw [mul_comm (μ.real K),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun x hx ↦ by simp [haK x hx]]
    refine norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun x hx ↦ ?_
    simpa [norm_smul, norm_oscillation, norm_iteratedFDeriv_zero] using hab 0 le_rfl x hx
  | succ N ih =>
    let D : ℝ := Fintype.card ι * 2 ^ (N + 1) * B
    have hN (i : ι) : ContDiff ℝ N (v i) := (hv i).of_le (by exact_mod_cast Nat.le_succ N)
    have h1 : (1 : ℕ∞ω) ≤ (↑(N + 1) : ℕ∞ω) := by exact_mod_cast Nat.succ_pos N
    have he := integral_oscillation_divergenceAmplitude (μ := μ) hφ hK w
      (fun i ↦ (hv i).of_le h1) hone (ha.of_le h1) haK s
    have heen := congrArg norm he
    rw [norm_smul, norm_div, norm_I, Complex.norm_real, Real.norm_eq_abs, one_div, norm_neg] at heen
    have hstep := ih hN (fun i j hj x hx ↦ hvb i j (by omega) x hx)
      (contDiff_divergenceAmplitude w hv ha)
      (fun x hx ↦ divergenceAmplitude_eq_zero hK.isClosed w v haK hx)
      (show 0 ≤ D * S by dsimp [D]; positivity)
      (fun j hj x hx ↦ norm_iteratedFDeriv_divergenceAmplitude_le hj hw hv ha x
        (fun i k hk ↦ hvb i k hk x hx) (fun k hk ↦ hab k hk x hx))
    have hD : (Fintype.card ι * 2 ^ N * B : ℝ) ≤ D := by
      dsimp [D]
      gcongr <;> norm_num
    rw [← heen] at hstep
    have hsabs := abs_pos.mpr hs
    calc
      _ ≤ |s| * ((Fintype.card ι * 2 ^ N * B) ^ N * μ.real K * (D * S) * |s| ^ N) := by
        simpa only [mul_inv_cancel_left₀ hsabs.ne'] using
          mul_le_mul_of_nonneg_left hstep hsabs.le
      _ ≤ |s| * (D ^ N * μ.real K * (D * S) * |s| ^ N) := by gcongr
      _ = _ := by change _ = D ^ (N + 1) * μ.real K * S * |s| ^ (N + 1); ring

section Gradient

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

private theorem exists_directional_coefficients {δ : ℝ} (hδ : 0 < δ) :
    ∃ (w : Fin (Module.finrank ℝ H) → H) (q : Fin (Module.finrank ℝ H) → (H →L[ℝ] ℝ) → ℝ),
      (∀ i, ‖w i‖ ≤ 1) ∧ (∀ i, ContDiff ℝ ∞ (q i)) ∧
        ∀ ℓ : H →L[ℝ] ℝ, δ ≤ ‖ℓ‖ → ∑ i, q i ℓ * ℓ (w i) = 1 := by
  classical
  let b := Module.finBasis ℝ H
  let a (i : Fin (Module.finrank ℝ H)) := max 1 ‖b i‖
  have ha (i) : 0 < a i := zero_lt_one.trans_le (le_max_left ..)
  let w (i : Fin (Module.finrank ℝ H)) := (a i)⁻¹ • b i
  have hw (i) : ‖w i‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (ha i).le), ← div_eq_inv_mul]
    exact (div_le_one (ha i)).2 (le_max_right ..)
  let ev (i : Fin (Module.finrank ℝ H)) : (H →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (w i)
  let ener (ℓ : H →L[ℝ] ℝ) := ∑ i, ev i ℓ ^ 2
  have he : ContDiff ℝ ∞ ener := by
    dsimp [ener]
    exact ContDiff.sum fun i _ ↦ (ev i).contDiff.pow 2
  let A := 1 + ∑ i, a i * ‖(b.coord i).toContinuousLinearMap‖
  have hA : 0 < A := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ ↦
    mul_nonneg (ha i).le (norm_nonneg _))
  let d := (δ / A) ^ 2
  have hd : 0 < d := pow_pos (div_pos hδ hA) _
  let q (i : Fin (Module.finrank ℝ H)) (ℓ : H →L[ℝ] ℝ) :=
    ev i ℓ * (smoothLowerTruncation (d / 2) d (ener ℓ))⁻¹
  refine ⟨w, q, hw, fun i ↦ (ev i).contDiff.mul
    (((contDiff_smoothLowerTruncation _ _).comp he).inv fun ℓ ↦
      (lt_of_lt_of_le (by linarith) (le_smoothLowerTruncation (by linarith) _)).ne'), ?_⟩
  intro ℓ hℓ
  have he0 : 0 ≤ ener ℓ := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hev (i) : ‖ev i ℓ‖ ≤ Real.sqrt (ener ℓ) := by
    have hi : ev i ℓ ^ 2 ≤ ener ℓ :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (ev j ℓ)) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hi
  have hn : ‖ℓ‖ ≤ A * Real.sqrt (ener ℓ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    have hsum : ℓ x = ∑ i, (a i * b.repr x i) * ev i ℓ := by
      nth_rw 1 [← b.sum_repr x]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      change ℓ (b.repr x i • b i) = (a i * b.repr x i) * ℓ ((a i)⁻¹ • b i)
      simp only [map_smul, smul_eq_mul]
      field_simp [(ha i).ne']
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ i, a i * ‖(b.coord i).toContinuousLinearMap‖ *
          (Real.sqrt (ener ℓ) * ‖x‖) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (ha i).le]
        have hh : ‖b.repr x i‖ ≤ ‖(b.coord i).toContinuousLinearMap‖ * ‖x‖ :=
          (b.coord i).toContinuousLinearMap.le_opNorm x
        calc
          _ ≤ (a i * (‖(b.coord i).toContinuousLinearMap‖ * ‖x‖)) * Real.sqrt (ener ℓ) := by
            gcongr
            exact hev i
          _ = _ := by ring
      _ ≤ _ := by
        rw [← Finset.sum_mul, mul_assoc]
        gcongr
        exact le_add_of_nonneg_left zero_le_one
  have hδA : δ / A ≤ Real.sqrt (ener ℓ) :=
    (div_le_iff₀ hA).2 (by simpa only [mul_comm A] using hℓ.trans hn)
  have hener : d ≤ ener ℓ := by
    rw [← Real.sq_sqrt he0]
    exact pow_le_pow_left₀ (div_nonneg hδ.le hA.le) hδA _
  calc
    _ = ∑ i, ev i ℓ ^ 2 * (ener ℓ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      change q i ℓ * ev i ℓ = _
      dsimp [q]
      rw [smoothLowerTruncation_of_right_le (by linarith) hener]
      ring
    _ = 1 := by
      rw [← Finset.sum_mul]
      exact mul_inv_cancel₀ (hd.trans_le hener).ne'

variable [MeasurableSpace H] [BorelSpace H] {ν : Measure H} [ν.IsAddHaarMeasure]

/-- A (C^{N+1}) phase with gradient bounded away from zero on a fixed compact set gives an
(O(|s|^N)) bound for (C^N) complex Banach-valued amplitudes supported there. The constant is
uniform under bounds on the derivatives of the phase and is independent of the amplitude. -/
theorem exists_norm_integral_oscillation_le_of_fderiv_lower (K : Set H) (hK : IsCompact K)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : H → ℝ), ContDiff ℝ (N + 1 : ℕ) φ →
      (∀ x ∈ K, δ ≤ ‖fderiv ℝ φ x‖) →
      (∀ j ≤ N, ∀ x ∈ K, ‖iteratedFDeriv ℝ (j + 1) φ x‖ ≤ M) →
      ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
        (a : H → V) (S : ℝ), 0 ≤ S → ContDiff ℝ N a →
        (∀ x ∉ K, a x = 0) →
        (∀ j ≤ N, ∀ x ∈ K, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ∀ s : ℝ, s ≠ 0 →
          ‖∫ x, Complex.exp (Complex.I * ((φ x / s : ℝ) : ℂ)) • a x ∂ν‖ ≤ C * S * |s| ^ N := by
  classical
  obtain ⟨w, q, hw, hq, hqone⟩ := exists_directional_coefficients (H := H) hδ
  let D := max 1 M
  have hcomp : IsCompact (Metric.closedBall (0 : H →L[ℝ] ℝ) D) := isCompact_closedBall ..
  have hqN (i) : ContDiff ℝ N (q i) := (hq i).of_le (by simp)
  choose B hB hqb using fun i ↦
    ((hqN i).contDiffOn (s := univ)).exists_nonneg_bound_iteratedFDeriv_of_isOpen
      isOpen_univ hcomp (subset_univ _)
  let A := ∑ i, B i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ ↦ hB i
  let P : ℝ := N.factorial * A * D ^ N
  refine ⟨(Module.finrank ℝ H * 2 ^ N * P) ^ N * ν.real K, by
    have : 1 ≤ D := le_max_left _ _
    dsimp [P]; positivity, ?_⟩
  intro φ hφ hlo hhi V _ _ _ a S hS ha haK hab s hs
  let v := fun i x ↦ q i (fderiv ℝ φ x)
  have hD : 1 ≤ D := le_max_left _ _
  have hf : ContDiff ℝ N (fderiv ℝ φ) := hφ.fderiv_right (by exact_mod_cast le_rfl)
  have hv (i) : ContDiff ℝ N (v i) := (hqN i).comp hf
  have hvb (i) (j : ℕ) (hj : j ≤ N) (x : H) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ j (v i) x‖ ≤ P := by
    have hmem : fderiv ℝ φ x ∈ Metric.closedBall (0 : H →L[ℝ] ℝ) D := by
      rw [Metric.mem_closedBall, dist_zero_right, ← norm_iteratedFDeriv_one (𝕜 := ℝ)]
      exact (hhi 0 (Nat.zero_le N) x hx).trans (le_max_right ..)
    have hBi : B i ≤ A := Finset.single_le_sum (fun k _ ↦ hB k) (Finset.mem_univ _)
    calc
      _ ≤ j.factorial * A * D ^ j :=
        norm_iteratedFDeriv_comp_le (hqN i) hf (by exact_mod_cast hj) x
          (fun k hk ↦ (hqb i k (by exact_mod_cast (hk.trans hj)) _ hmem).trans hBi)
          (fun k hk hk' ↦ by
            rw [norm_iteratedFDeriv_fderiv]
            exact (hhi k (hk'.trans hj) x hx).trans
              ((le_max_right _ _).trans (le_self_pow₀ hD (Nat.ne_of_gt hk))))
      _ ≤ P := by
        dsimp [P]
        gcongr
  simpa only [Fintype.card_fin] using
    norm_integral_oscillation_le_of_directional_coefficients (μ := ν)
      (hφ.of_le (by exact_mod_cast Nat.succ_pos N)) hK hw
      (fun x hx ↦ hqone _ (hlo x hx)) N P (by dsimp [P]; positivity)
      hv hvb ha haK hS hab hs

end Gradient

end

end TauCeti
