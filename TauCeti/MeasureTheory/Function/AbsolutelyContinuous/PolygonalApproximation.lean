/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing
import TauCeti.MeasureTheory.Function.IntervalStep
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Polygonal approximation of absolutely continuous curves

Absolutely continuous curves in finite-dimensional real normed spaces admit polygonal
approximations with the same endpoints, converging uniformly and with their derivatives in `L¹`.
The construction integrates finite interval step functions and corrects their average velocity.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace AbsolutelyContinuousOnInterval

variable [CompleteSpace E] {a b : ℝ}

private theorem integral_intervalStep_eq {δ : ℝ} (hδ : 0 < δ)
    (g : ℝ → E) (c : E) (i : ℕ) {t : ℝ}
    (ht : t ∈ Icc (a + i * δ) (a + (i + 1) * δ)) :
    (∫ v in (a + i * δ)..t, intervalStep a δ g v + c) =
      (t - (a + i * δ)) • (g (a + i * δ) + c) := by
  rw [← intervalIntegral.integral_const]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (a + (i + 1) * δ)] with v hv hmem
  rw [uIoc_of_le ht.1] at hmem
  have hv' : v ∈ Ico (a + i * δ) (a + (i + 1) * δ) :=
    ⟨hmem.1.le, lt_of_le_of_ne (hmem.2.trans ht.2) hv⟩
  rw [intervalStep_eq hδ g i hv']

private theorem polygonal_primitive (hab : a < b) (N : ℕ) (hN : 0 < N)
    (g : ℝ →ᵇ E) (x c : E) :
    TauCeti.IsPolygonalOnInterval
      (fun t ↦ x + ∫ v in a..t, intervalStep a ((b - a) / N) g v + c) a b := by
  let δ := (b - a) / N
  have hδ : 0 < δ := div_pos (sub_pos.mpr hab) (Nat.cast_pos.mpr hN)
  let s : Fin (N + 1) → ℝ := fun i ↦ a + i * δ
  have hs : StrictMono s := by
    intro i j hij
    dsimp [s]
    exact add_lt_add_right (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hij) hδ) a
  have hlast : s (Fin.last N) = b := by
    dsimp [s, δ]
    field_simp [Nat.cast_ne_zero.mpr hN.ne']
    ring
  have hint : IntervalIntegrable (fun v ↦ intervalStep a δ g v + c) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab.le]
    exact (integrableOn_intervalStep a b δ g).add (integrable_const c)
  refine ⟨N, hN, s, hs, by simp [s], hlast, fun i t ht ↦ ?_⟩
  have hnode (j : Fin (N + 1)) : s j ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]
    constructor
    · simpa only [show s 0 = a from by simp [s]] using hs.monotone (Fin.zero_le _)
    · simpa only [hlast] using hs.monotone (Fin.le_last _)
  have hleft := hnode i.castSucc
  have hright := hnode i.succ
  have heq (u : ℝ) (hu : u ∈ Icc (s i.castSucc) (s i.succ)) :
      (∫ v in a..u, intervalStep a δ g v + c) =
        (∫ v in a..s i.castSucc, intervalStep a δ g v + c) +
          (u - s i.castSucc) • (g (s i.castSucc) + c) := by
    have hu' : u ∈ uIcc a b := by
      rw [uIcc_of_le hab.le] at hleft hright ⊢
      exact ⟨hleft.1.trans hu.1, hu.2.trans hright.2⟩
    have h := intervalIntegral.integral_interval_sub_left
      (hint.mono_set (uIcc_subset_uIcc (left_mem_uIcc) hu'))
      (hint.mono_set (uIcc_subset_uIcc (left_mem_uIcc) hleft))
    have hc := integral_intervalStep_eq hδ g c i.val
      (by simpa only [s, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hu)
    dsimp only [s, Fin.val_castSucc] at h ⊢
    rw [hc] at h
    exact eq_add_of_sub_eq' h
  have hr := heq (s i.succ) (right_mem_Icc.mpr (hs.monotone (by exact Nat.le_succ i.val)))
  have htq := heq t ht
  dsimp only [δ] at hr htq
  simp only [htq, hr, add_sub_add_left_eq_sub, add_sub_cancel_left]
  rw [smul_smul, div_mul_cancel₀ _ (sub_pos.mpr (hs (by exact Nat.lt_succ_self i.val))).ne']
  abel

private theorem ae_deriv_const_add_integral {v : ℝ → E} (hv : IntervalIntegrable v volume a b)
    (hab : a ≤ b) (x : E) :
    deriv (fun t ↦ x + ∫ u in a..t, v u) =ᵐ[volume.restrict (Ioc a b)] v := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hv.ae_hasDerivAt_integral] with t ht hmem
  exact ((ht ((uIcc_of_le hab).symm ▸ Ioc_subset_Icc_self hmem) a
    left_mem_uIcc).const_add x).deriv

omit [CompleteSpace E] in
private theorem exists_polygonal_error_le [FiniteDimensional ℝ E] {γ : ℝ → E}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ → E, TauCeti.IsPolygonalOnInterval p a b ∧
      p a = γ a ∧ p b = γ b ∧ (∀ t ∈ Icc a b, ‖p t - γ t‖ ≤ 2 * ε) ∧
      (∫ t in a..b, ‖deriv p t - deriv γ t‖) ≤ 2 * ε := by
  have hγi := hγ.intervalIntegrable_deriv_of_finiteDimensional
  have hγi' : IntegrableOn (deriv γ) (Ioc a b) := by
    simpa only [uIoc_of_le hab.le] using hγi.def'
  -- Approximate the velocity by a step function on a uniform subdivision.
  obtain ⟨N, hN, g, hg⟩ := hγi'.exists_intervalStep_integral_norm_sub_le hab hε
  let δ := (b - a) / N
  let s := intervalStep a δ g
  have hsi' : IntegrableOn s (Ioc a b) := integrableOn_intervalStep a b δ g
  have hsi : IntervalIntegrable s volume a b := by
    rwa [intervalIntegrable_iff, uIoc_of_le hab.le]
  -- Correct the average velocity so its primitive has both prescribed endpoints.
  let D := γ b - γ a - ∫ t in a..b, s t
  let c := (b - a)⁻¹ • D
  let v := fun t ↦ s t + c
  let p := fun t ↦ γ a + ∫ t in a..t, v t
  have hvi' : IntegrableOn v (Ioc a b) := hsi'.add (integrable_const c)
  have hvi : IntervalIntegrable v volume a b := by
    rwa [intervalIntegrable_iff, uIoc_of_le hab.le]
  have hpa : p a = γ a := by simp [p]
  have hpb : p b = γ b := by
    dsimp [p, v]
    rw [intervalIntegral.integral_add hsi (intervalIntegrable_const),
      intervalIntegral.integral_const]
    dsimp [c]
    rw [smul_smul, mul_inv_cancel₀ (sub_pos.mpr hab).ne', one_smul]
    dsimp [D]
    abel
  have hpPoly : TauCeti.IsPolygonalOnInterval p a b := polygonal_primitive hab N hN g (γ a) c
  have hpAC := hpPoly.absolutelyContinuousOnInterval
  have hpderiv : deriv p =ᵐ[volume.restrict (Ioc a b)] v :=
    ae_deriv_const_add_integral hvi hab.le (γ a)
  -- The mean correction costs at most the original velocity approximation error.
  have hD : ‖D‖ ≤ ε := by
    have hEq : D = ∫ t in a..b, deriv γ t - s t := by
      rw [intervalIntegral.integral_sub hγi hsi,
        hγ.integral_deriv_eq_sub_of_finiteDimensional]
    rw [hEq]
    apply (intervalIntegral.norm_integral_le_integral_norm hab.le).trans
    simpa only [intervalIntegral.integral_of_le hab.le, norm_sub_rev] using hg
  have hc : (∫ _ in Ioc a b, ‖c‖) ≤ ε := by
    have hEq : (∫ _ in Ioc a b, ‖c‖) = ‖D‖ := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
      simp only [c, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos (sub_pos.mpr hab), smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (sub_pos.mpr hab).ne', one_mul]
    exact hEq ▸ hD
  have herror : (∫ t in Ioc a b, ‖v t - deriv γ t‖) ≤ 2 * ε := by
    calc
      _ ≤ ∫ t in Ioc a b, ‖s t - deriv γ t‖ + ‖c‖ := by
        apply integral_mono (hvi'.sub hγi').norm ((hsi'.sub hγi').norm.add (integrable_const _))
        intro t
        simp only [v, Pi.sub_apply, Pi.add_apply]
        have he : s t + c - deriv γ t = (s t - deriv γ t) + c := by abel
        rw [he]
        exact norm_add_le _ _
      _ = (∫ t in Ioc a b, ‖s t - deriv γ t‖) + ∫ _ in Ioc a b, ‖c‖ :=
        integral_add (hsi'.sub hγi').norm (integrable_const _)
      _ ≤ 2 * ε := by linarith
  -- Velocity convergence implies uniform convergence through the AC fundamental theorem.
  have hderiv : (∫ t in a..b, ‖deriv p t - deriv γ t‖) ≤ 2 * ε := by
    rw [intervalIntegral.integral_of_le hab.le]
    apply le_trans (integral_congr_ae (hpderiv.mono fun t ht ↦ by rw [ht])).le herror
  have hunif : ∀ t ∈ Icc a b, ‖p t - γ t‖ ≤ 2 * ε := fun t ht ↦
    (hpAC.norm_sub_le_integral_norm_deriv_sub hγ hpa ht).trans hderiv
  exact ⟨p, hpPoly, hpa, hpb, hunif, hderiv⟩

omit [CompleteSpace E] in
/-- Every absolutely continuous curve in a finite-dimensional real normed space admits polygonal
approximations with the same endpoints, converging uniformly and with their derivatives in `L¹`. -/
theorem exists_polygonal_approximation [FiniteDimensional ℝ E] {γ : ℝ → E}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a < b) :
    ∃ γn : ℕ → ℝ → E,
      (∀ n, TauCeti.IsPolygonalOnInterval (γn n) a b ∧ γn n a = γ a ∧ γn n b = γ b) ∧
      TendstoUniformlyOn γn γ atTop (Icc a b) ∧
      Tendsto (fun n ↦ ∫ t in a..b, ‖deriv (γn n) t - deriv γ t‖) atTop (𝓝 0) := by
  have hex (n : ℕ) := exists_polygonal_error_le hγ hab
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose p hp ha hb hu hd using hex
  have hlim : Tendsto (fun n : ℕ ↦ 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  refine ⟨p, fun n ↦ ⟨hp n, ha n, hb n⟩, ?_, ?_⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
    intro t ht
    simpa only [dist_eq_norm, norm_sub_rev] using (hu n t ht).trans_lt hn
  · exact squeeze_zero (fun n ↦ intervalIntegral.integral_nonneg hab.le
      (fun _ _ ↦ norm_nonneg _)) hd hlim

end AbsolutelyContinuousOnInterval
