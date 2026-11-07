/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
public import Mathlib.Analysis.Convex.Segment
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Log
import TauCeti.Analysis.Complex.SlitPlane
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Basic.Complex.BigOperators
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp

/-!
# Proximity and straight-line homotopy invariance for absolutely continuous curves

Two absolutely continuous curves with equal endpoint ratios have equal winding numbers when their
pointwise separation is smaller than the first curve's distance to that point. Their comparison
quotient lies in the right half-plane, where the principal logarithm is smooth. The fundamental
theorem for its absolutely continuous logarithm evaluates the difference of their index integrals.

Chaining finitely many proximity steps along the straight-line homotopy `(1 - s) • γ₀ + s • γ₁`
deduces invariance from the geometric condition `z ∉ segment ℝ (γ₀ t) (γ₁ t)` for all `t`.
-/

public section

open Complex MeasureTheory Set Filter Metric
open scoped Topology

namespace TauCeti.Contour

/-- A pointwise leash preserves the winding number when the comparison quotient has equal
endpoint values. The curves themselves need not be closed. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_of_dist_lt_dist_of_eq_endpoint_ratios
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (h₀ : AbsolutelyContinuousOnInterval γ₀ a b)
    (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (hends : (γ₁ a - z) / (γ₀ a - z) = (γ₁ b - z) / (γ₀ b - z))
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) z) :
    windingNumber γ₁ a b z = windingNumber γ₀ a b z := by
  -- The leash excludes the pole from both traces.
  have h₀ne : ∀ t ∈ uIcc a b, γ₀ t - z ≠ 0 := by
    intro t ht
    exact sub_ne_zero.mpr
      (dist_pos.mp (lt_of_le_of_lt dist_nonneg (hlt t ht)))
  have h₁ne : ∀ t ∈ uIcc a b, γ₁ t - z ≠ 0 := by
    intro t ht
    apply sub_ne_zero.mpr
    intro heq
    have h := hlt t ht
    rw [heq, dist_comm] at h
    exact lt_irrefl _ h
  have h₀off : z ∉ γ₀ '' uIcc a b := by
    rintro ⟨t, ht, heq⟩
    exact h₀ne t ht (sub_eq_zero.mpr heq)
  have h₁off : z ∉ γ₁ '' uIcc a b := by
    rintro ⟨t, ht, heq⟩
    exact h₁ne t ht (sub_eq_zero.mpr heq)
  -- The comparison quotient and its principal logarithm are absolutely continuous.
  have hσslit : ∀ t ∈ uIcc a b, (γ₁ t - z) / (γ₀ t - z) ∈ slitPlane := fun t ht ↦
    TauCeti.div_sub_mem_slitPlane_of_dist_lt_dist (hlt t ht)
  have hlog := h₀.log_div_sub h₁ hσslit
  have hlogderiv := h₀.ae_hasDerivAt_log_div_sub h₁ hσslit
  -- FTC evaluates the logarithmic derivative at the equal endpoint ratios.
  have hint := hlog.integral_eq_sub_of_ae_hasDerivAt hlogderiv
  simp only [Function.comp_apply, hends, sub_self] at hint
  have hint₀ := h₀.intervalIntegrable_inv_sub_mul_deriv h₀off
  have hint₁ := h₁.intervalIntegrable_inv_sub_mul_deriv h₁off
  rw [intervalIntegral.integral_sub hint₁ hint₀] at hint
  rw [h₁.windingNumber_eq_integral h₁off,
    h₀.windingNumber_eq_integral h₀off]
  exact congrArg ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ·) (sub_eq_zero.mp hint)

/-- A pointwise leash preserves winding numbers of closed absolutely continuous curves. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_of_dist_lt_dist
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (h₀ : AbsolutelyContinuousOnInterval γ₀ a b) (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) z) :
    windingNumber γ₁ a b z = windingNumber γ₀ a b z :=
  h₀.windingNumber_eq_of_dist_lt_dist_of_eq_endpoint_ratios h₁
    (by rw [h₀closed, h₁closed]) hlt

/-- A pointwise leash preserves winding numbers of AC paths with common endpoints. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_of_dist_lt_dist_of_eq_endpoints
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (h₀ : AbsolutelyContinuousOnInterval γ₀ a b) (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (ha : γ₀ a = γ₁ a) (hb : γ₀ b = γ₁ b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) z) :
    windingNumber γ₁ a b z = windingNumber γ₀ a b z := by
  have hne (t : ℝ) (ht : t ∈ uIcc a b) : γ₀ t - z ≠ 0 :=
    sub_ne_zero.mpr (dist_pos.mp (lt_of_le_of_lt dist_nonneg (hlt t ht)))
  exact h₀.windingNumber_eq_of_dist_lt_dist_of_eq_endpoint_ratios h₁
    (by rw [← ha, ← hb, div_self (hne a left_mem_uIcc), div_self (hne b right_mem_uIcc)]) hlt

/-- Uniform approximation of closed AC curves preserves the trace domain and every index outside
that domain once the approximation is sufficiently close. -/
theorem _root_.AbsolutelyContinuousOnInterval.eventually_windingNumber_eq_on_compl
    {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ} {γn : ℕ → ℝ → ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγn : ∀ n, AbsolutelyContinuousOnInterval (γn n) a b)
    (hclosed : γ a = γ b) (hclosedn : ∀ n, γn n a = γn n b)
    (hconv : TendstoUniformlyOn γn γ atTop (uIcc a b))
    (hU : IsOpen U) (htrace : γ '' uIcc a b ⊆ U) :
    ∀ᶠ n in atTop, γn n '' uIcc a b ⊆ U ∧
      ∀ z ∉ U, windingNumber (γn n) a b z = windingNumber γ a b z := by
  obtain ⟨ε, hε, hεU⟩ :=
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).exists_thickening_subset_open hU htrace
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv ε hε] with n hn
  have hnear (t) (ht : t ∈ uIcc a b) : dist (γn n t) (γ t) < ε := by
    simpa only [dist_comm] using hn t ht
  constructor
  · rintro z ⟨t, ht, rfl⟩
    exact hεU (mem_thickening_iff.mpr ⟨γ t, ⟨t, ht, rfl⟩, hnear t ht⟩)
  · intro z hz
    apply AbsolutelyContinuousOnInterval.windingNumber_eq_of_dist_lt_dist
      hγ (hγn n) hclosed (hclosedn n)
    intro t ht
    have hdist : ε ≤ dist (γ t) z := by
      by_contra h
      exact hz (hεU (mem_thickening_iff.mpr ⟨γ t, ⟨t, ht, rfl⟩,
        by simpa only [dist_comm] using lt_of_not_ge h⟩))
    exact (hnear t ht).trans_le hdist

variable {ι : Type*} {s : Finset ι} {γ : ι → ℝ → ℂ} {γn : ℕ → ι → ℝ → ℂ}
  {a b : ι → ℝ} {w : ι → ℤ} {U : Set ℂ}

/-- Joint uniform approximation preserves every off-domain index eventually, so it preserves
the total integer-weighted index without any individual index-vanishing assumption. -/
theorem eventually_sum_windingNumber_eq_on_compl_of_tendstoUniformlyOn
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hγn : ∀ n, ∀ i ∈ s, AbsolutelyContinuousOnInterval (γn n i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i))
    (hclosedn : ∀ n, ∀ i ∈ s, γn n i (a i) = γn n i (b i))
    (hconv : ∀ i ∈ s, TendstoUniformlyOn (fun n ↦ γn n i) (γ i) atTop (uIcc (a i) (b i)))
    (hU : IsOpen U) (htrace : ∀ i ∈ s, γ i '' uIcc (a i) (b i) ⊆ U) :
    ∀ᶠ n in atTop, (∀ i ∈ s, γn n i '' uIcc (a i) (b i) ⊆ U) ∧
      ∀ z ∉ U, (∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γn n i) (a i) (b i) z) =
        ∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γ i) (a i) (b i) z := by
  have he := (Filter.eventually_all_finset s).mpr fun i hi ↦
    AbsolutelyContinuousOnInterval.eventually_windingNumber_eq_on_compl (hγ i hi)
      (fun n ↦ hγn n i hi) (hclosed i hi) (fun n ↦ hclosedn n i hi)
      (hconv i hi) hU (htrace i hi)
  filter_upwards [he] with n hn
  refine ⟨fun i hi ↦ (hn i hi).1, fun z hz ↦ ?_⟩
  exact Finset.sum_congr rfl fun i hi ↦ congrArg ((w i : ℂ) * ·) ((hn i hi).2 z hz)

/-- The stage at time `s` of the straight-line homotopy `(1 - s) • γ₀ + s • γ₁`. -/
private noncomputable def lineHomotopy (γ₀ γ₁ : ℝ → ℂ) (s : ℝ) : ℝ → ℂ :=
  fun t ↦ (1 - s) • γ₀ t + s • γ₁ t

private theorem lineHomotopy_apply (γ₀ γ₁ : ℝ → ℂ) (s t : ℝ) :
    lineHomotopy γ₀ γ₁ s t = (1 - s) • γ₀ t + s • γ₁ t := (rfl)

private theorem lineHomotopy_sub (γ₀ γ₁ : ℝ → ℂ) (s s' t : ℝ) :
    lineHomotopy γ₀ γ₁ s' t - lineHomotopy γ₀ γ₁ s t = (s' - s) • (γ₁ t - γ₀ t) := by
  simp only [lineHomotopy_apply]
  module

private theorem lineHomotopy_sub_const (γ₀ γ₁ : ℝ → ℂ) (z : ℂ) (s t : ℝ) :
    lineHomotopy γ₀ γ₁ s t - z = (1 - (s : ℂ)) * (γ₀ t - z) + (s : ℂ) * (γ₁ t - z) := by
  simp only [lineHomotopy_apply, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

private theorem lineHomotopy_endpoint_ratio_eq {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hends : (γ₁ a - z) / (γ₀ a - z) = (γ₁ b - z) / (γ₀ b - z))
    (h₀a : γ₀ a - z ≠ 0) (h₀b : γ₀ b - z ≠ 0) {s s' : ℝ}
    (hsa : lineHomotopy γ₀ γ₁ s a - z ≠ 0) (hsb : lineHomotopy γ₀ γ₁ s b - z ≠ 0) :
    (lineHomotopy γ₀ γ₁ s' a - z) / (lineHomotopy γ₀ γ₁ s a - z) =
      (lineHomotopy γ₀ γ₁ s' b - z) / (lineHomotopy γ₀ γ₁ s b - z) := by
  have hmul : (γ₁ a - z) * (γ₀ b - z) = (γ₁ b - z) * (γ₀ a - z) :=
    (div_eq_div_iff h₀a h₀b).mp hends
  rw [div_eq_div_iff hsa hsb]
  simp only [lineHomotopy_sub_const]
  linear_combination ((s' : ℂ) - s) * hmul

private theorem windingNumber_lineHomotopy_div_eq_of_norm_div_lt
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (h₀ : AbsolutelyContinuousOnInterval γ₀ a b)
    (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (hends : (γ₁ a - z) / (γ₀ a - z) = (γ₁ b - z) / (γ₀ b - z))
    {m : ℝ} {N : ℕ} (hNpos : (0 : ℝ) < N) (hm : 0 < m)
    (hlt : ∀ t ∈ uIcc a b, ‖γ₁ t - γ₀ t‖ / N < m)
    (hmle : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ uIcc a b, m ≤ ‖lineHomotopy γ₀ γ₁ s t - z‖) :
    ∀ k : ℕ, k ≤ N → windingNumber (lineHomotopy γ₀ γ₁ (k / N)) a b z =
      windingNumber (lineHomotopy γ₀ γ₁ 0) a b z := by
  have hHac : ∀ s : ℝ, AbsolutelyContinuousOnInterval (lineHomotopy γ₀ γ₁ s) a b := fun s ↦
    ((lipschitzWith_smul (1 - s)).comp_absolutelyContinuousOnInterval h₀).fun_add
      ((lipschitzWith_smul s).comp_absolutelyContinuousOnInterval h₁)
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ uIcc a b, lineHomotopy γ₀ γ₁ s t - z ≠ 0 :=
    fun s hs t ht ↦ norm_pos_iff.mp (hm.trans_le (hmle s hs t ht))
  have h₀a : γ₀ a - z ≠ 0 := by
    simpa only [lineHomotopy_apply, sub_zero, one_smul, zero_smul, add_zero] using
      hne 0 ⟨le_rfl, zero_le_one⟩ a left_mem_uIcc
  have h₀b : γ₀ b - z ≠ 0 := by
    simpa only [lineHomotopy_apply, sub_zero, one_smul, zero_smul, add_zero] using
      hne 0 ⟨le_rfl, zero_le_one⟩ b right_mem_uIcc
  intro k
  induction k with
  | zero => intro _; norm_num
  | succ k ih =>
    intro hk
    have hkN : k ≤ N := Nat.le_of_succ_le hk
    have hmem : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hNpos).mpr (by exact_mod_cast hkN)⟩
    rw [← ih hkN]
    refine (hHac _).windingNumber_eq_of_dist_lt_dist_of_eq_endpoint_ratios (hHac _)
      (lineHomotopy_endpoint_ratio_eq hends h₀a h₀b (hne _ hmem a left_mem_uIcc)
        (hne _ hmem b right_mem_uIcc)) fun t ht ↦ ?_
    have hgap : ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N = 1 / N := by push_cast; ring
    have hdisp : ‖lineHomotopy γ₀ γ₁ ((k + 1 : ℕ) / N) t
        - lineHomotopy γ₀ γ₁ ((k : ℝ) / N) t‖ = ‖γ₁ t - γ₀ t‖ / N := by
      rw [lineHomotopy_sub, norm_smul, Real.norm_eq_abs, hgap, abs_of_pos (by positivity)]
      ring
    rw [dist_eq_norm, dist_eq_norm, hdisp]
    exact lt_of_lt_of_le (hlt t ht) (hmle _ hmem t ht)

/-- **Invariance of the winding number along a straight-line homotopy** with equal endpoint
ratios. If for every parameter `t ∈ uIcc a b` the segment `[γ₀ t, γ₁ t]` misses `z`, then the two
absolutely continuous curves have the same winding number about `z`. -/
theorem
    _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_of_notMem_segment_of_eq_endpoint_ratios
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (h₀ : AbsolutelyContinuousOnInterval γ₀ a b)
    (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (hends : (γ₁ a - z) / (γ₀ a - z) = (γ₁ b - z) / (γ₀ b - z))
    (hseg : ∀ t ∈ uIcc a b, z ∉ segment ℝ (γ₀ t) (γ₁ t)) :
    windingNumber γ₁ a b z = windingNumber γ₀ a b z := by
  have hHne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ uIcc a b, lineHomotopy γ₀ γ₁ s t - z ≠ 0 := by
    intro s hs t ht
    refine sub_ne_zero.mpr fun heq ↦ hseg t ht ?_
    exact heq ▸ ⟨1 - s, s, by linarith [hs.2], hs.1, by ring, rfl⟩
  have hKcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ uIcc a b) := isCompact_Icc.prod isCompact_uIcc
  have hKne : (Icc (0 : ℝ) 1 ×ˢ uIcc a b).Nonempty := ⟨(0, a), ⟨by norm_num, left_mem_uIcc⟩⟩
  have hcont₀ : ContinuousOn (fun p : ℝ × ℝ ↦ γ₀ p.2) (Icc (0 : ℝ) 1 ×ˢ uIcc a b) :=
    h₀.continuousOn.comp continuousOn_snd fun p hp ↦ hp.2
  have hcont₁ : ContinuousOn (fun p : ℝ × ℝ ↦ γ₁ p.2) (Icc (0 : ℝ) 1 ×ˢ uIcc a b) :=
    h₁.continuousOn.comp continuousOn_snd fun p hp ↦ hp.2
  have hcontF : ContinuousOn (fun p : ℝ × ℝ ↦ ‖lineHomotopy γ₀ γ₁ p.1 p.2 - z‖)
      (Icc (0 : ℝ) 1 ×ˢ uIcc a b) := by
    simp only [lineHomotopy_apply]
    exact ((((continuousOn_const.sub continuousOn_fst).smul hcont₀).add
      (continuousOn_fst.smul hcont₁)).sub continuousOn_const).norm
  obtain ⟨q, hqK, hqmin⟩ := hKcompact.exists_isMinOn hKne hcontF
  have hm : 0 < ‖lineHomotopy γ₀ γ₁ q.1 q.2 - z‖ :=
    norm_pos_iff.mpr (hHne q.1 hqK.1 q.2 hqK.2)
  have hmle : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ uIcc a b,
      ‖lineHomotopy γ₀ γ₁ q.1 q.2 - z‖ ≤ ‖lineHomotopy γ₀ γ₁ s t - z‖ :=
    fun s hs t ht ↦ isMinOn_iff.mp hqmin (s, t) ⟨hs, ht⟩
  obtain ⟨M, hM⟩ :=
    isCompact_uIcc.exists_bound_of_continuousOn (h₁.continuousOn.sub h₀.continuousOn)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a left_mem_uIcc)
  obtain ⟨N, hN⟩ := exists_nat_gt (M / ‖lineHomotopy γ₀ γ₁ q.1 q.2 - z‖)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hstep : M / N < ‖lineHomotopy γ₀ γ₁ q.1 q.2 - z‖ := by
    rw [div_lt_iff₀ hNpos, mul_comm]
    exact (div_lt_iff₀ hm).mp hN
  have hfinal := windingNumber_lineHomotopy_div_eq_of_norm_div_lt h₀ h₁ hends hNpos hm
    (fun t ht ↦ lt_of_le_of_lt (by gcongr; exact hM t ht) hstep) hmle N le_rfl
  rw [div_self (ne_of_gt hNpos)] at hfinal
  have hH0 : lineHomotopy γ₀ γ₁ 0 = γ₀ := by
    funext t; rw [lineHomotopy_apply]; simp
  have hH1 : lineHomotopy γ₀ γ₁ 1 = γ₁ := by
    funext t; rw [lineHomotopy_apply]; simp
  rwa [hH0, hH1] at hfinal

/-- **Invariance of the winding number along a straight-line homotopy** of closed absolutely
continuous curves. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_of_notMem_segment
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (h₀ : AbsolutelyContinuousOnInterval γ₀ a b) (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    (hseg : ∀ t ∈ uIcc a b, z ∉ segment ℝ (γ₀ t) (γ₁ t)) :
    windingNumber γ₁ a b z = windingNumber γ₀ a b z :=
  h₀.windingNumber_eq_of_notMem_segment_of_eq_endpoint_ratios h₁
    (by rw [h₀closed, h₁closed]) hseg

/-- **Invariance of the winding number along a straight-line homotopy** of absolutely continuous
paths with common endpoints. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_of_notMem_segment_of_eq_endpoints
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (h₀ : AbsolutelyContinuousOnInterval γ₀ a b) (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (ha : γ₀ a = γ₁ a) (hb : γ₀ b = γ₁ b)
    (hseg : ∀ t ∈ uIcc a b, z ∉ segment ℝ (γ₀ t) (γ₁ t)) :
    windingNumber γ₁ a b z = windingNumber γ₀ a b z := by
  have hne (t : ℝ) (ht : t ∈ uIcc a b) : γ₀ t - z ≠ 0 :=
    sub_ne_zero.mpr fun heq ↦ hseg t ht (heq ▸ left_mem_segment ℝ _ _)
  exact h₀.windingNumber_eq_of_notMem_segment_of_eq_endpoint_ratios h₁
    (by rw [← ha, ← hb, div_self (hne a left_mem_uIcc), div_self (hne b right_mem_uIcc)]) hseg

end TauCeti.Contour
