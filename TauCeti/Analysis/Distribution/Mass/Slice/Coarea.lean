/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Slice.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The coarea pairing identity for slices by smooth functions

For a locally normal `(k + 1)`-current `T` on an open set `Ω ⊆ E`, smooth `u : E → ℝ` and
`g : ℝ → ℝ`, and a test `k`-form `φ`, integrating `g(t) ⟨T, u, t⟩(φ)` recovers
`T((g ∘ u) • (du ∧ φ))` (and `g = 1` gives `∫ t, slice T u t φ = T (du ∧ φ)`).

The proof applies the 1D fundamental theorem of calculus to the `L¹(‖S‖)` curve
`s ↦ (∫_{a}^{s} g(t) ψ((m + 1)(t - u(·))) dt) • η`, passes to `m → ∞` against
`H(s) = ∫_{s}^{M} g(t) dt`, and concludes via the Leibniz rule.

## Main declarations

* `Distribution.integral_mul_slice_apply`: `∫ g(t) ⟨T, u, t⟩(φ) dt = T((g ∘ u) • (du ∧ φ))`.
* `Distribution.integral_slice_apply`: `∫ ⟨T, u, t⟩(φ) dt = T(du ∧ φ)`.

## References

* H. Federer, *Geometric Measure Theory*, §4.3.2.
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §5.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter TestFunction ContinuousLinearMap
open scoped ENNReal NNReal Distributions Topology ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E} {k : ℕ} {u : E → ℝ}

private theorem memLp_intervalIntegral_mul_smoothTransition_smul {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ]
    (hu : ContDiff ℝ ∞ u) {g : ℝ → ℝ} (hg : Continuous g) (η : 𝓓(Ω, G)) (a b : ℝ) (m : ℕ) :
    MemLp (fun x : Ω =>
      (∫ t in a..b, g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x))) • η x) 1 μ := by
  have hJcont : Continuous fun x : E =>
      ∫ t in a..b, g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x t => g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))
      ((hg.comp continuous_snd).mul <| Real.smoothTransition.continuous.comp <|
        continuous_const.mul (continuous_snd.sub (hu.continuous.comp continuous_fst))) a b
  refine ((hJcont.comp continuous_subtypeVal).smul
    (η.continuous.comp continuous_subtypeVal)).memLp_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (TestFunction.isCompact_preimage_tsupport η)
      fun x hx => ?_)
  by_contra h
  exact hx (by simp [image_eq_zero_of_notMem_tsupport h])

private theorem abs_apply_smulLeftCLM_smoothTransition_le {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {S : 𝓓(Ω, G) →L[ℝ] ℝ} (hS : HasLocallyFiniteMass S) (hu : ContDiff ℝ ∞ u)
    (η : 𝓓(Ω, G)) (m : ℕ) (t : ℝ) :
    |S (smulLeftCLM (hu.smoothTransition_mul_sub ((m : ℝ) + 1) t) η)| ≤
      ‖TestFunction.toLp 1 (massMeasure S) η‖ := by
  rw [← extendL1_toLp hS, ← Real.norm_eq_abs]
  refine (norm_extendL1_apply_le _).trans ?_
  rw [TestFunction.toLp_apply, TestFunction.toLp_apply, Lp.norm_toLp, Lp.norm_toLp]
  refine ENNReal.toReal_mono (TestFunction.memLp_subtype (p := 1) η).eLpNorm_lt_top.ne
    (eLpNorm_mono (TestFunction.memLp_subtype (p := 1)
      (smulLeftCLM (hu.smoothTransition_mul_sub ((m : ℝ) + 1) t) η)).aestronglyMeasurable
      fun x => ?_)
  rw [smulLeftCLM_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg (η x)) (Real.smoothTransition.abs_le_one _)

private theorem intervalIntegral_mul_apply_smulLeftCLM_smoothTransition {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {S : 𝓓(Ω, G) →L[ℝ] ℝ} (hS : HasLocallyFiniteMass S) (hu : ContDiff ℝ ∞ u)
    {g : ℝ → ℝ} (hg : Continuous g) (η : 𝓓(Ω, G)) (a b : ℝ) (m : ℕ) :
    ∫ t in a..b, g t * S (smulLeftCLM (hu.smoothTransition_mul_sub ((m : ℝ) + 1) t) η) =
      extendL1 S ((memLp_intervalIntegral_mul_smoothTransition_smul
        (massMeasure S) hu hg η a b m).toLp _) := by
  -- Differentiate the `L¹(‖S‖)` curve `q s = (∫_{a}^{s} g(t) ψ((m + 1)(t - u ·)) dt) • η`
  -- by dominated convergence on its difference quotients, then apply the FTC to `extendL1 S ∘ q`.
  let J (s : ℝ) (x : E) : ℝ :=
    ∫ t in a..s, g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x))
  have hcont_t (x : E) : Continuous fun t =>
      g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
    hg.mul (Real.smoothTransition.continuous.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))
  let hmem (s : ℝ) :=
    memLp_intervalIntegral_mul_smoothTransition_smul (massMeasure S) hu hg η a s m
  let q (s : ℝ) : Lp G 1 (massMeasure S) := (hmem s).toLp _
  have hderiv_q (s : ℝ) :
      HasDerivAt q
        (g s • TestFunction.toLp 1 (massMeasure S)
          (smulLeftCLM (hu.smoothTransition_mul_sub ((m : ℝ) + 1) s) η)) s := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hmem_sl (h : ℝ) : MemLp (fun x : Ω => (h⁻¹ * (J (s + h) x - J s x)) • η x) 1
        (massMeasure S) :=
      (((hmem (s + h)).sub (hmem s)).const_smul h⁻¹).ae_eq
        (ae_of_all _ fun x => by simp [J, sub_smul, mul_smul])
    have hmem₀ : MemLp (fun x : Ω =>
        (g s * Real.smoothTransition (((m : ℝ) + 1) * (s - u x))) • η x) 1 (massMeasure S) :=
      ((TestFunction.memLp_subtype (p := 1)
          (smulLeftCLM (hu.smoothTransition_mul_sub ((m : ℝ) + 1) s) η)).const_smul (g s)).ae_eq
        (ae_of_all _ fun x => by simp [smulLeftCLM_apply, mul_smul])
    have hq_sl (h : ℝ) : h⁻¹ • (q (s + h) - q s) = (hmem_sl h).toLp _ := by
      rw [← MemLp.toLp_sub, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
      exact ae_of_all _ fun x => by simp [J, sub_smul, mul_smul]
    have hq₀ : g s • TestFunction.toLp 1 (massMeasure S)
        (smulLeftCLM (hu.smoothTransition_mul_sub ((m : ℝ) + 1) s) η) = hmem₀.toLp _ := by
      rw [TestFunction.toLp_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
      exact ae_of_all _ fun x => by simp [smulLeftCLM_apply, mul_smul]
    simp_rw [hq_sl, hq₀]
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc (s - 1) (s + 1)) hg.continuousOn
    refine TestFunction.tendsto_toLp_smul_of_dominated ENNReal.one_ne_top hmem_sl hmem₀
      (M + |g s|) ?_ fun x _ => ?_
    · filter_upwards [mem_nhdsWithin_of_mem_nhds
          (Ioo_mem_nhds (a := (-1 : ℝ)) (b := 1) (by norm_num) (by norm_num)),
        self_mem_nhdsWithin] with h hh hh0 x _
      have hsub_J : J (s + h) x - J s x =
          ∫ t in s..(s + h), g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
        sub_eq_of_eq_add' (intervalIntegral.integral_add_adjacent_intervals
          ((hcont_t x).intervalIntegrable a s) ((hcont_t x).intervalIntegrable s (s + h))).symm
      have hint : |J (s + h) x - J s x| ≤ M * |h| := by
        rw [hsub_J, ← Real.norm_eq_abs]
        simpa only [add_sub_cancel_left] using
          intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := s + h) (C := M)
            fun t ht => by
              have htIcc : t ∈ Icc (s - 1) (s + 1) := by
                rw [Set.mem_uIoc] at ht
                rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [hh.1, hh.2]
              rw [Real.norm_eq_abs, abs_mul]
              exact (mul_le_of_le_one_right (abs_nonneg _)
                (Real.smoothTransition.abs_le_one _)).trans (by simpa using hM t htIcc)
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_inv]
        calc |h|⁻¹ * |J (s + h) x - J s x| ≤ |h|⁻¹ * (M * |h|) := by gcongr
          _ = M := by field_simp [abs_ne_zero.2 (mem_compl_singleton_iff.1 hh0)]
      · rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.abs_le_one _)
    · simpa only [smul_eq_mul] using hasDerivAt_iff_tendsto_slope_zero.1 <|
        intervalIntegral.integral_hasDerivAt_right ((hcont_t x).intervalIntegrable a s)
          ((hcont_t x).stronglyMeasurableAtFilter volume (𝓝 s)) (hcont_t x).continuousAt
  have hcont_prod : Continuous fun t : ℝ =>
      g t * S (smulLeftCLM (hu.smoothTransition_mul_sub ((m : ℝ) + 1) t) η) :=
    hg.mul (continuous_apply_smulLeftCLM_smoothTransition hS hu η ((m : ℝ) + 1))
  have hqa : q a = 0 := by rw [← norm_eq_zero, Lp.norm_toLp]; simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => extendL1 S (q s))
    (fun s _ => ((extendL1 S).hasFDerivAt.comp_hasDerivAt s (hderiv_q s)).congr_deriv
      (by simp [map_smul, smul_eq_mul, extendL1_toLp hS]))
    (hcont_prod.intervalIntegrable a b), hqa, map_zero, sub_zero]

private theorem tendsto_intervalIntegral_mul_apply_smulLeftCLM_smoothTransition {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {S : 𝓓(Ω, G) →L[ℝ] ℝ} (hS : HasLocallyFiniteMass S) (hu : ContDiff ℝ ∞ u)
    {g H : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {M : ℝ} (hM : 0 < M)
    (hH : ContDiff ℝ ∞ H) (hH_eq : ∀ s, H s = ∫ t in s..M, g t) (η : 𝓓(Ω, G))
    (hη : ∀ x : Ω, (x : E) ∈ tsupport η → |u x| < M) :
    Tendsto (fun m : ℕ =>
        ∫ t in (-M)..M,
          g t * S (smulLeftCLM (hu.smoothTransition_mul_sub ((m : ℝ) + 1) t) η))
      atTop (𝓝 (S (smulLeftCLM (hH.comp hu) η))) := by
  -- Pass `m → ∞` inside `extendL1 S`: for each `x ∈ tsupport η`, the scalar integral over `[-M, M]`
  -- is dominated by `∫ |g|` and converges to `∫_{u x}^{M} g(t) dt = H (u x)`.
  simp_rw [intervalIntegral_mul_apply_smulLeftCLM_smoothTransition hS hu hg.continuous η (-M) M,
    ← extendL1_toLp hS (smulLeftCLM (hH.comp hu) η)]
  refine ((extendL1 S).continuous.tendsto _).comp ?_
  have hle_M : -M ≤ M := by linarith
  let I : ℝ := ∫ t in uIoc (-M) M, |g t|
  have hmemH : MemLp (fun x : Ω => H (u x) • η x) 1 (massMeasure S) := by
    simpa [smulLeftCLM_apply] using
      TestFunction.memLp_subtype (p := 1) (μ := massMeasure S) (smulLeftCLM (hH.comp hu) η)
  have htoLpH : TestFunction.toLp 1 (massMeasure S) (smulLeftCLM (hH.comp hu) η) =
      hmemH.toLp _ := by
    rw [TestFunction.toLp_apply, MemLp.toLp_eq_toLp_iff]
    exact ae_of_all _ fun x => by simp [smulLeftCLM_apply]
  rw [htoLpH]
  refine TestFunction.tendsto_toLp_smul_of_dominated ENNReal.one_ne_top
    (fun m => memLp_intervalIntegral_mul_smoothTransition_smul (massMeasure S) hu hg.continuous
      η (-M) M m)
    hmemH (I + I) (.of_forall fun m x hx => ?_) fun x hx => ?_
  · have hux := abs_lt.1 (hη x hx)
    refine (abs_sub _ _).trans <| add_le_add
      (Real.smoothTransition.abs_intervalIntegral_mul_le (hg.continuous.intervalIntegrable (-M) M))
      ?_
    rw [hH_eq (u x), ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := g)).trans ?_
    simpa only [Real.norm_eq_abs] using setIntegral_mono_set
      (intervalIntegrable_iff.1 (hg.continuous.abs.intervalIntegrable (-M) M))
      (ae_of_all _ fun _ => abs_nonneg _)
      (by rw [uIoc_of_le hux.2.le, uIoc_of_le hle_M]
          exact .of_forall (Ioc_subset_Ioc_left hux.1.le))
  · have hux := abs_lt.1 (hη x hx)
    have hind_eq : ∫ t in (-M)..M, (Ioi (u x)).indicator g t = H (u x) := by
      have hint_ind : IntervalIntegrable ((Ioi (u x)).indicator g) volume (-M) M :=
        intervalIntegrable_iff.2 <| (hg.continuous.integrableOn_Icc.mono_set
          Ioc_subset_Icc_self).indicator measurableSet_Ioi
      rw [← intervalIntegral.integral_add_adjacent_intervals
          (hint_ind.mono_set (by rw [uIcc_of_le hux.1.le, uIcc_of_le hle_M]
                                 exact Icc_subset_Icc_right hux.2.le))
          (hint_ind.mono_set (by rw [uIcc_of_le hux.2.le, uIcc_of_le hle_M]
                                 exact Icc_subset_Icc_left hux.1.le)),
        hH_eq (u x), intervalIntegral.integral_of_le hux.1.le,
        intervalIntegral.integral_of_le hux.2.le, intervalIntegral.integral_of_le hux.2.le,
        setIntegral_eq_zero_of_forall_eq_zero
          fun t (ht : t ∈ Ioc (-M) (u x)) => indicator_of_notMem (not_lt.2 ht.2) _,
        zero_add]
      exact setIntegral_congr_fun measurableSet_Ioc fun t ht => indicator_of_mem ht.1 g
    rw [← hind_eq]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => |g t|)
      (.of_forall fun m => (hg.continuous.mul (Real.smoothTransition.continuous.comp
        (continuous_const.mul (continuous_id.sub continuous_const)))).aestronglyMeasurable)
      (.of_forall fun m => ae_of_all _ fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.abs_le_one _))
      (hg.continuous.abs.intervalIntegrable (-M) M) ?_
    filter_upwards [compl_mem_ae_iff.2 (by simp : volume ({u x} : Set ℝ) = 0)] with t ht _
    rcases lt_trichotomy (u x) t with hlt | heq | hgt
    · rw [indicator_of_mem hlt]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const
        (sub_pos.2 hlt)).eventually_ge_atTop 1] with m hm
      rw [Real.smoothTransition.one_of_one_le hm, mul_one]
    · exact (ht heq.symm).elim
    · rw [indicator_of_notMem (not_lt.2 hgt.le)]
      refine tendsto_const_nhds.congr' (.of_forall fun m => ?_)
      dsimp only
      rw [Real.smoothTransition.zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 hgt.le)), mul_zero]

/-- **The coarea pairing identity for smooth functions.** For a locally normal `(k + 1)`-current
`T`, smooth `u : E → ℝ`, smooth `g : ℝ → ℝ`, and test `k`-form `φ`,
`∫ g(t) ⟨T, u, t⟩(φ) dt = T((g ∘ u) • (du ∧ φ))`. -/
theorem integral_mul_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    ∫ t, g t * slice T u t φ =
      T (smulLeftCLM (hg.comp hu) (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ)) := by
  -- Cut off to `(-M, M]` covering `u '' tsupport φ`, take the antiderivative `H s = ∫_s^M g`,
  -- and compare the `m → ∞` limits of the smooth-transition integrals on both sides.
  obtain ⟨hT₁, hT₂⟩ := isLocallyNormal_succ_iff.1 hT
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (c := (0 : ℝ)).1
    (φ.hasCompactSupport.image_of_continuousOn
      (hu.continuous.continuousOn.mono φ.tsupport_subset)).isBounded
  let M : ℝ := max R 0 + 1
  have hM : 0 < M := by positivity
  have hφ_lt : ∀ x : Ω, (x : E) ∈ tsupport φ → |u x| < M := fun x hx => by
    have huxR : |u x| ≤ R := by simpa [Metric.mem_closedBall, Real.dist_eq] using hR ⟨x, hx, rfl⟩
    exact (huxR.trans (le_max_left _ _)).trans_lt (lt_add_one _)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (-M) M) fun t ht => by
      rw [slice_apply_eq_zero_of_notMem_Ioc hT hφ_lt ht, mul_zero],
    ← intervalIntegral.integral_of_le (by linarith : -M ≤ M)]
  let H : ℝ → ℝ := fun s => ∫ t in s..M, g t
  have hdH (s : ℝ) : HasDerivAt H (-g s) s := by
    have hH_neg : H = fun s => -(∫ t in M..s, g t) :=
      funext fun s => by rw [intervalIntegral.integral_symm, neg_neg]
    rw [hH_neg]
    exact (intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable M s)
      (hg.continuous.stronglyMeasurableAtFilter volume (𝓝 s)) hg.continuous.continuousAt).neg
  have hH : ContDiff ℝ ∞ H := contDiff_infty_iff_deriv.2
    ⟨fun s => (hdH s).differentiableAt, by rw [funext fun s => (hdH s).deriv]; exact hg.neg⟩
  let hf (m : ℕ) := hu.smoothTransition_mul_sub ((m : ℝ) + 1)
  have hlim_R :=
    (tendsto_intervalIntegral_mul_apply_smulLeftCLM_smoothTransition hT₁ hu hg hM hH
      (fun _ => rfl) (extDerivCLM φ) fun x hx => hφ_lt x (tsupport_extDerivCLM_subset φ hx)).sub
    (tendsto_intervalIntegral_mul_apply_smulLeftCLM_smoothTransition hT₂ hu hg hM hH
      (fun _ => rfl) φ hφ_lt)
  let C : ℝ := ‖TestFunction.toLp 1 (massMeasure T) (extDerivCLM φ)‖ +
    ‖TestFunction.toLp 1 (massMeasure (T ∘L extDerivCLM)) φ‖
  have hlim_L : Tendsto (fun m : ℕ =>
      (∫ t in (-M)..M, g t * T (smulLeftCLM (hf m t) (extDerivCLM φ))) -
        ∫ t in (-M)..M, g t * (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ))
      atTop (𝓝 (∫ t in (-M)..M, g t * slice T u t φ)) := by
    have hsub_eq (m : ℕ) :
        (∫ t in (-M)..M, g t * T (smulLeftCLM (hf m t) (extDerivCLM φ))) -
          (∫ t in (-M)..M, g t * (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ)) =
        ∫ t in (-M)..M, g t * (T (smulLeftCLM (hf m t) (extDerivCLM φ)) -
          (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ)) := by
      have hi1 : IntervalIntegrable
          (fun t => g t * T (smulLeftCLM (hf m t) (extDerivCLM φ))) volume (-M) M :=
        (hg.continuous.mul (continuous_apply_smulLeftCLM_smoothTransition hT₁ hu (extDerivCLM φ)
          ((m : ℝ) + 1))).intervalIntegrable (-M) M
      have hi2 : IntervalIntegrable
          (fun t => g t * (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ)) volume (-M) M :=
        (hg.continuous.mul (continuous_apply_smulLeftCLM_smoothTransition hT₂ hu φ
          ((m : ℝ) + 1))).intervalIntegrable (-M) M
      rw [← intervalIntegral.integral_sub hi1 hi2]
      simp_rw [mul_sub]
    simp_rw [hsub_eq]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => |g t| * C)
      (.of_forall fun m => (hg.continuous.mul
        ((continuous_apply_smulLeftCLM_smoothTransition hT₁ hu (extDerivCLM φ) ((m : ℝ) + 1)).sub
          (continuous_apply_smulLeftCLM_smoothTransition hT₂ hu φ
            ((m : ℝ) + 1)))).aestronglyMeasurable)
      (.of_forall fun m => ae_of_all _ fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add
          (abs_apply_smulLeftCLM_smoothTransition_le hT₁ hu (extDerivCLM φ) m t)
          (abs_apply_smulLeftCLM_smoothTransition_le hT₂ hu φ m t))) (abs_nonneg _))
      ((hg.continuous.abs.intervalIntegrable (-M) M).mul_const C)
      (ae_of_all _ fun t _ => tendsto_const_nhds.mul <|
        (tendsto_neg_oneFormWedgeCLM_slice_apply hT hu t φ).congr fun m => by
          have hL := DFunLike.congr_fun (comp_smulLeftCLM_comp_extDerivCLM T (hf m t)) φ
          simp only [comp_apply, sub_apply] at hL; rw [comp_apply]; linarith)
  -- Apply the Leibniz rule to rewrite the limit in terms of `d(H ∘ u) = -(g ∘ u) du`.
  have hleib : T (smulLeftCLM (hH.comp hu) (extDerivCLM φ)) -
      (T ∘L extDerivCLM) (smulLeftCLM (hH.comp hu) φ) =
      -T (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 (hH.comp hu)).2 φ) := by
    have hL := DFunLike.congr_fun (comp_smulLeftCLM_comp_extDerivCLM T (hH.comp hu)) φ
    simp only [comp_apply, sub_apply] at hL; rw [comp_apply]; linarith
  have hwedge : oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 (hH.comp hu)).2 φ =
      -smulLeftCLM (hg.comp hu) (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ) := by
    ext x
    have hfd : fderiv ℝ (H ∘ u) x = (-g (u x)) • fderiv ℝ u x :=
      ((hdH (u x)).comp_hasFDerivAt x ((hu.differentiable (by simp)) x).hasFDerivAt).fderiv
    have hsmul : ((-g (u x)) • fderiv ℝ u x).smulRight (φ x) =
        (-g (u x)) • (fderiv ℝ u x).smulRight (φ x) := by ext y; simp [smul_smul]
    rw [oneFormWedgeCLM_apply, hfd, hsmul, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
    simp [neg_smul]
  rw [tendsto_nhds_unique hlim_L hlim_R, hleib, hwedge, map_neg, neg_neg]

/-- **Integrating all slices recovers contraction with `du`.** For a locally normal
`(k + 1)`-current `T` and smooth `u : E → ℝ`, `∫ ⟨T, u, t⟩(φ) dt = T(du ∧ φ)`. -/
theorem integral_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    ∫ t, slice T u t φ = T (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ) := by
  have h := integral_mul_slice_apply hT hu (contDiff_const (c := (1 : ℝ))) φ
  have hone : smulLeftCLM ((contDiff_const (c := (1 : ℝ))).comp hu)
      (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ) =
      oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ := by ext x; simp
  simpa [hone] using h

end Distribution
