/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Real Laplace integrals: moments, parametric differentiation, and Abelian limits

This file establishes basic analytic properties of one-sided real Laplace integrals
`p ↦ ∫ t in Ioi 0, exp (-(p * t)) • f t ∂μ` and their polynomial moments
`p ↦ ∫ t in Ioi 0, (exp (-(p * t)) * t ^ j) • f t ∂μ` for functions `f : ℝ → E` into a real normed
space `E`.

## Main results

* `TauCeti.locallyIntegrableOn_of_integrableOn_exp_neg_mul_smul`: integrability of
  `t ↦ exp (-(p * t)) • f t` on `(a, ∞)` implies `LocallyIntegrableOn f (Ici a)`.
* `TauCeti.integrableOn_exp_neg_mul_mul_pow_smul_of_lt`: integrability of
  `t ↦ exp (-(q * t)) • f t` on `(0, ∞)` implies integrability of all polynomial moments
  `t ↦ (exp (-(p * t)) * t ^ j) • f t` for every `p > q`.
* `TauCeti.hasDerivAt_integral_exp_neg_mul_mul_pow_smul` and
  `TauCeti.iteratedDeriv_integral_exp_neg_mul_smul`: differentiation under the Laplace integral on
  `{p | q < p}`.
* `TauCeti.tendsto_pow_succ_smul_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero`: if `h` is locally
  integrable on `[0, ∞)` and `h t → L` as `t → ∞`, then
  `p ^ (j + 1) • ∫ t in Ioi 0, (exp (-(p * t)) * t ^ j) • h t → j ! • L` as `p → 0⁺`.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `t ↦ exp (-(p * t)) • f t` is integrable on `(a, ∞)`, then `f` is locally integrable on
`[a, ∞)`. -/
theorem locallyIntegrableOn_of_integrableOn_exp_neg_mul_smul {μ : Measure ℝ}
    [NullSingletonClass μ] {f : ℝ → E} {a p : ℝ}
    (hf : IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) • f t) (Ioi a) μ) :
    LocallyIntegrableOn f (Ici a) μ :=
  (((integrableOn_Ici_iff_integrableOn_Ioi eNorm_ne_top).mpr hf).locallyIntegrableOn
      |>.continuousOn_smul isClosed_Ici.isLocallyClosed
      (by fun_prop : ContinuousOn (fun t : ℝ ↦ Real.exp (p * t)) (Ici a))).congr
    (ae_of_all _ fun t ↦ by simp [smul_smul, ← Real.exp_add])

/-- If `t ↦ exp (-(q * t)) • f t` is Bochner integrable on `(0, ∞)` and `q < p`, then every
polynomial moment `t ↦ (exp (-(p * t)) * t ^ j) • f t` is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_mul_mul_pow_smul_of_lt {μ : Measure ℝ} {f : ℝ → E} {q p : ℝ}
    (hqp : q < p) (hf : IntegrableOn (fun t : ℝ ↦ Real.exp (-(q * t)) • f t) (Ioi 0) μ) (j : ℕ) :
    IntegrableOn (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ j) • f t) (Ioi 0) μ := by
  obtain ⟨M, _, hM⟩ := exists_rpow_mul_exp_neg_mul_le (Nat.cast_nonneg j) (sub_pos.mpr hqp)
  refine (hf.bdd_smul M
    (by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-((p - q) * t)) * t ^ j).aestronglyMeasurable
    ?_).congr (ae_of_all _ fun t ↦ ?_)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t (ht : 0 < t)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le _)), mul_comm,
      ← Real.rpow_natCast]
    exact hM t ht.le
  · have hexp : -((p - q) * t) + -(q * t) = -(p * t) := by ring
    rw [Pi.smul_apply', smul_smul, mul_right_comm, ← Real.exp_add, hexp]

/-- Differentiation under the integral sign for the Laplace moments
`r ↦ ∫ t in Ioi 0, (exp (-(r * t)) * t ^ j) • f t ∂μ` on `{r | q < r}`. -/
theorem hasDerivAt_integral_exp_neg_mul_mul_pow_smul {μ : Measure ℝ} {f : ℝ → E} {q p : ℝ}
    (hqp : q < p) (hf : IntegrableOn (fun t : ℝ ↦ Real.exp (-(q * t)) • f t) (Ioi 0) μ) (j : ℕ) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in Ioi 0, (Real.exp (-(r * t)) * t ^ j) • f t ∂μ)
      (-(∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ (j + 1)) • f t ∂μ)) p := by
  let m := (q + p) / 2
  have hqm : q < m := by dsimp [m]; linarith
  have hmp : m < p := by dsimp [m]; linarith
  have hdom := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioi m)
    (F := fun r t ↦ (Real.exp (-(r * t)) * t ^ j) • f t)
    (F' := fun r t ↦ -((Real.exp (-(r * t)) * t ^ (j + 1)) • f t))
    (bound := fun t ↦ ‖(Real.exp (-(m * t)) * t ^ (j + 1)) • f t‖) (Ioi_mem_nhds hmp)
    (by filter_upwards [Ioi_mem_nhds hqp] with r (hr : q < r) using
      (integrableOn_exp_neg_mul_mul_pow_smul_of_lt hr hf j).aestronglyMeasurable)
    (integrableOn_exp_neg_mul_mul_pow_smul_of_lt hqp hf j)
    (integrableOn_exp_neg_mul_mul_pow_smul_of_lt hqp hf (j + 1)).neg.aestronglyMeasurable ?_
    (integrableOn_exp_neg_mul_mul_pow_smul_of_lt hqm hf (j + 1)).norm ?_
  · simpa [integral_neg] using hdom.2
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t (ht : 0 < t) r (hr : m < r)
    simp only [norm_neg, norm_smul,
      Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le _))]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith)) (pow_nonneg ht.le _)) (norm_nonneg _)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _ r _
    exact (((((hasDerivAt_id r).mul_const t).neg.exp).mul_const (t ^ j)).congr_deriv
      (by simp [pow_succ]; ring)).smul_const (f t) |>.congr_deriv (neg_smul _ _)

/-- Formula for the `n`-th derivative of the Laplace integral
`r ↦ ∫ t in Ioi 0, exp (-(r * t)) • f t ∂μ` at any `p > q` where `t ↦ exp (-(q * t)) • f t` is
integrable on `(0, ∞)`. -/
theorem iteratedDeriv_integral_exp_neg_mul_smul {μ : Measure ℝ} {f : ℝ → E} {q p : ℝ} (hqp : q < p)
    (hf : IntegrableOn (fun t : ℝ ↦ Real.exp (-(q * t)) • f t) (Ioi 0) μ) (n : ℕ) :
    iteratedDeriv n (fun r : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(r * t)) • f t ∂μ) p =
      (-1 : ℝ) ^ n • ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ n) • f t ∂μ := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : (iteratedDeriv n fun r : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(r * t)) • f t ∂μ) =ᶠ[𝓝 p]
        ((-1 : ℝ) ^ n • fun r : ℝ ↦ ∫ t in Ioi 0, (Real.exp (-(r * t)) * t ^ n) • f t ∂μ) := by
      filter_upwards [Ioi_mem_nhds hqp] with r hr using ih hr
    rw [heq.deriv_eq,
      ((hasDerivAt_integral_exp_neg_mul_mul_pow_smul hqp hf n).const_smul ((-1 : ℝ) ^ n)).deriv]
    simp [pow_succ, mul_smul]

/-- Helper for `tendsto_pow_succ_smul_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero`: if `h` is
locally integrable on `[0, ∞)` and bounded by `c` on `(T, ∞)` (`0 ≤ T`), then
`t ↦ (exp (-(p * t)) * t ^ j) • h t` is integrable on `(0, ∞)` with norm integral at most
`T ^ j * ∫ t in Ioc 0 T, ‖h t‖ + c * (j ! / p ^ (j + 1))`. -/
private theorem integrableOn_and_norm_integral_exp_neg_mul_mul_pow_smul_le {h : ℝ → E}
    {p T c : ℝ} (hp : 0 < p) (hT : 0 ≤ T) (hc : 0 ≤ c) (j : ℕ)
    (hh : LocallyIntegrableOn h (Ici 0)) (hbound : ∀ t ∈ Ioi T, ‖h t‖ ≤ c) :
    IntegrableOn (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ j) • h t) (Ioi 0) ∧
      ‖∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ j) • h t‖ ≤
        T ^ j * (∫ t in Ioc 0 T, ‖h t‖) + c * (j.factorial / p ^ (j + 1)) := by
  have hh_Ioc : IntegrableOn h (Ioc 0 T) :=
    (hh.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc).mono_set Ioc_subset_Icc_self
  have h1_w : ∀ t ∈ Ioc 0 T, ‖Real.exp (-(p * t)) * t ^ j‖ ≤ T ^ j := fun t ht ↦ by
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.1.le _))]
    exact (mul_le_of_le_one_left (pow_nonneg ht.1.le _)
      (Real.exp_le_one_iff.mpr (by nlinarith [ht.1]))).trans (pow_le_pow_left₀ ht.1.le ht.2 j)
  have h1_int : IntegrableOn (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ j) • h t) (Ioc 0 T) :=
    hh_Ioc.bdd_smul (T ^ j)
      (by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-(p * t)) * t ^ j).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc h1_w)
  have hdom_T : IntegrableOn (fun t : ℝ ↦ c * (t ^ j * Real.exp (-(p * t)))) (Ioi T) :=
    ((integrableOn_pow_mul_exp_neg_mul_Ioi j hp).mono_set (Ioi_subset_Ioi hT)).const_mul c
  have h2_ae : ∀ᵐ t ∂volume.restrict (Ioi T),
      ‖(Real.exp (-(p * t)) * t ^ j) • h t‖ ≤ c * (t ^ j * Real.exp (-(p * t))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := hT.trans (mem_Ioi.mp ht).le
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht0 _)),
      mul_comm (Real.exp _), mul_comm c]
    exact mul_le_mul_of_nonneg_left (hbound t ht)
      (mul_nonneg (pow_nonneg ht0 _) (Real.exp_pos _).le)
  have h2_int : IntegrableOn (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ j) • h t) (Ioi T) :=
    hdom_T.mono' ((by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-(p * t)) * t ^ j
      ).aestronglyMeasurable.smul (hh.aestronglyMeasurable.mono_set (Ioi_subset_Ici hT))) h2_ae
  refine ⟨Ioc_union_Ioi_eq_Ioi hT ▸ h1_int.union h2_int, ?_⟩
  rw [← Ioc_union_Ioi_eq_Ioi hT, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    h1_int h2_int]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_integral_le_of_norm_le (hh_Ioc.norm.const_mul (T ^ j))
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right (h1_w t ht) (norm_nonneg _))).trans_eq
      (integral_const_mul _ _)
  · refine (norm_integral_le_of_norm_le hdom_T h2_ae).trans ?_
    rw [← integral_pow_mul_exp_neg_mul_Ioi j hp, ← integral_const_mul]
    exact setIntegral_mono_set ((integrableOn_pow_mul_exp_neg_mul_Ioi j hp).const_mul c)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦
        mul_nonneg hc (mul_nonneg (pow_nonneg (mem_Ioi.mp ht).le _) (Real.exp_pos _).le))
      (Eventually.of_forall (Ioi_subset_Ioi hT))

/-- **Abelian limit for rescaled Laplace moments.** If `h` is locally integrable on `[0, ∞)` and
`h t → L` as `t → ∞`, then
`p ^ (j + 1) • ∫ t in Ioi 0, (exp (-(p * t)) * t ^ j) • h t → j ! • L` as `p → 0⁺`. -/
theorem tendsto_pow_succ_smul_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero [CompleteSpace E]
    {h : ℝ → E} {L : E} (hh : LocallyIntegrableOn h (Ici 0)) (hh_top : Tendsto h atTop (𝓝 L))
    (j : ℕ) :
    Tendsto (fun p : ℝ ↦ p ^ (j + 1) • ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ j) • h t)
      (𝓝[>] 0) (𝓝 ((j.factorial : ℝ) • L)) := by
  have hj_pos : (0 : ℝ) < j.factorial := Nat.cast_pos.mpr j.factorial_pos
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set c := δ / (2 * j.factorial)
  have hc : 0 < c := by positivity
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hh_top.eventually (Metric.closedBall_mem_nhds L hc))
  set T := max T₀ 0
  set K := T ^ j * ∫ t in Ioc 0 T, ‖h t - L‖
  have hsmall : ∀ᶠ p : ℝ in 𝓝[>] 0, p ^ (j + 1) * K < δ / 2 :=
    (((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).pow (j + 1)).mul_const K).eventually_lt_const
      (by simpa using half_pos hδ)
  filter_upwards [hsmall, self_mem_nhdsWithin] with p hpK (hp : 0 < p)
  obtain ⟨hint_sub, hnorm⟩ := integrableOn_and_norm_integral_exp_neg_mul_mul_pow_smul_le
    (h := fun t ↦ h t - L) hp (le_max_right T₀ 0) hc.le j (hh.sub (locallyIntegrableOn_const L))
    fun t ht ↦ by simpa [dist_eq_norm] using hT₀ t ((le_max_left T₀ 0).trans (mem_Ioi.mp ht).le)
  have hw : IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) * t ^ j) (Ioi 0) := by
    simpa only [mul_comm] using integrableOn_pow_mul_exp_neg_mul_Ioi j hp
  have hw_int : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * t ^ j = j.factorial / p ^ (j + 1) := by
    simpa only [mul_comm] using integral_pow_mul_exp_neg_mul_Ioi j hp
  have hw_eq : p ^ (j + 1) * ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * t ^ j = j.factorial := by
    rw [hw_int, mul_div_cancel₀ _ (pow_pos hp _).ne']
  have hfun : (fun t : ℝ ↦ (Real.exp (-(p * t)) * t ^ j) • h t) = fun t ↦
      (Real.exp (-(p * t)) * t ^ j) • (h t - L) + (Real.exp (-(p * t)) * t ^ j) • L := by
    ext t; rw [← smul_add, sub_add_cancel]
  have hsplit : p ^ (j + 1) • ∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ j) • h t =
      p ^ (j + 1) • (∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ j) • (h t - L)) +
        (j.factorial : ℝ) • L := by
    rw [hfun, integral_add hint_sub (hw.smul_const L), integral_smul_const, smul_add, smul_smul,
      hw_eq]
  rw [dist_eq_norm, hsplit, add_sub_cancel_right, norm_smul,
    Real.norm_of_nonneg (pow_nonneg hp.le _)]
  calc p ^ (j + 1) * ‖∫ t in Ioi 0, (Real.exp (-(p * t)) * t ^ j) • (h t - L)‖
      ≤ p ^ (j + 1) * (K + c * (j.factorial / p ^ (j + 1))) := by gcongr
    _ = p ^ (j + 1) * K + δ / 2 := by
        rw [mul_add]; congr 1; simp only [c]; field_simp [hp.ne', hj_pos.ne']
    _ < δ := by linarith

end TauCeti
