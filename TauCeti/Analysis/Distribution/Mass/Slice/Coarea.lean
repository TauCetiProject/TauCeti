/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Slice.Basic

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

private theorem extendL1_toLp_smul {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {S : 𝓓(Ω, G) →L[ℝ] ℝ} (hS : HasLocallyFiniteMass S)
    {c : E → ℝ} (hc : ContDiff ℝ ∞ c) (hc' : Continuous fun x : Ω => c x) (η : 𝓓(Ω, G)) :
    extendL1 S ((TestFunction.memLp_smul_of_continuous hc' η).toLp (fun x : Ω => c x • η x)) =
      S (smulLeftCLM hc η) := by
  rw [← extendL1_toLp hS]
  refine congrArg (extendL1 S) ?_
  rw [TestFunction.toLp_apply, MemLp.toLp_eq_toLp_iff]
  exact ae_of_all _ fun x => by simp [smulLeftCLM_apply]

private theorem continuous_apply_smulLeftCLM_smoothTransition {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {S : 𝓓(Ω, G) →L[ℝ] ℝ} (hS : HasLocallyFiniteMass S) (hu : ContDiff ℝ ∞ u)
    (η : 𝓓(Ω, G)) (c : ℝ) :
    Continuous fun s : ℝ => S (smulLeftCLM (hu.smoothTransition_mul_sub c s) η) := by
  let K (x : E) (s : ℝ) : ℝ := Real.smoothTransition (c * (s - u x))
  have hK : Continuous fun q : Ω × ℝ => K q.1 q.2 := Real.smoothTransition.continuous.comp <|
    continuous_const.mul (continuous_snd.sub (hu.continuous.comp
      (continuous_subtypeVal.comp continuous_fst)))
  let hc (s : ℝ) : Continuous fun x : Ω => K x s :=
    hK.comp (continuous_id.prodMk continuous_const)
  have heq (s : ℝ) : S (smulLeftCLM (hu.smoothTransition_mul_sub c s) η) =
      extendL1 S ((TestFunction.memLp_smul_of_continuous (p := 1) (μ := massMeasure S)
        (hc s) η).toLp _) :=
    (extendL1_toLp_smul hS (hu.smoothTransition_mul_sub c s) (hc s) η).symm
  simp_rw [heq]
  exact (extendL1 S).continuous.comp (TestFunction.continuous_toLp_smul ENNReal.one_ne_top hK η)

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
    (eLpNorm_mono (TestFunction.memLp_subtype (p := 1) _).aestronglyMeasurable fun x => ?_)
  rw [smulLeftCLM_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg (η x)) (Real.smoothTransition.abs_le_one _)

private theorem intervalIntegral_mul_apply_smulLeftCLM_smoothTransition {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {S : 𝓓(Ω, G) →L[ℝ] ℝ} (hS : HasLocallyFiniteMass S) (hu : ContDiff ℝ ∞ u)
    {g : ℝ → ℝ} (hg : Continuous g) (η : 𝓓(Ω, G)) (a b : ℝ) (m : ℕ) :
    ∫ t in a..b, g t * S (smulLeftCLM (hu.smoothTransition_mul_sub ((m : ℝ) + 1) t) η) =
      extendL1 S ((TestFunction.memLp_intervalIntegral_smul
        (K := fun x t => g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))
        ((hg.comp continuous_snd).mul <| Real.smoothTransition.continuous.comp <|
          continuous_const.mul (continuous_snd.sub
            (hu.continuous.comp (continuous_subtypeVal.comp continuous_fst))))
        a b η).toLp _) := by
  let K (x : E) (t : ℝ) : ℝ := g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x))
  have hK : Continuous fun p : Ω × ℝ => K p.1 p.2 := (hg.comp continuous_snd).mul <|
    Real.smoothTransition.continuous.comp <| continuous_const.mul
      (continuous_snd.sub (hu.continuous.comp (continuous_subtypeVal.comp continuous_fst)))
  let hc (t : ℝ) : Continuous fun x : Ω => K x t :=
    hK.comp (continuous_id.prodMk continuous_const)
  have hpt (t : ℝ) : g t * S (smulLeftCLM (hu.smoothTransition_mul_sub ((m : ℝ) + 1) t) η) =
      extendL1 S ((TestFunction.memLp_smul_of_continuous (p := 1) (μ := massMeasure S)
        (hc t) η).toLp _) := by
    have hct : Continuous fun x : Ω => Real.smoothTransition (((m : ℝ) + 1) * (t - u x)) :=
      Real.smoothTransition.continuous.comp
        (continuous_const.mul (continuous_const.sub (hu.continuous.comp continuous_subtypeVal)))
    rw [← extendL1_toLp_smul hS (hu.smoothTransition_mul_sub ((m : ℝ) + 1) t) hct η,
      ← smul_eq_mul, ← map_smul]
    refine congrArg (extendL1 S) ?_
    rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    exact ae_of_all _ fun x => by simp [K, mul_smul]
  simp_rw [hpt]
  rw [(extendL1 S).intervalIntegral_comp_comm
      ((TestFunction.continuous_toLp_smul ENNReal.one_ne_top hK η).intervalIntegrable a b),
    TestFunction.intervalIntegral_toLp_smul ENNReal.one_ne_top hK a b η]

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
  have hHc : Continuous fun x : Ω => (H ∘ u) x :=
    (hH.continuous.comp hu.continuous).comp continuous_subtypeVal
  simp_rw [intervalIntegral_mul_apply_smulLeftCLM_smoothTransition hS hu hg.continuous η (-M) M,
    ← extendL1_toLp_smul hS (hH.comp hu) hHc η]
  refine ((extendL1 S).continuous.tendsto _).comp ?_
  have hle_M : -M ≤ M := by linarith
  let I : ℝ := ∫ t in uIoc (-M) M, |g t|
  refine TestFunction.tendsto_toLp_smul_of_dominated (l := atTop) ENNReal.one_ne_top
    (fun m : ℕ => TestFunction.memLp_intervalIntegral_smul
      (K := fun x t => g t * Real.smoothTransition (((m : ℝ) + 1) * (t - u x)))
      ((hg.continuous.comp continuous_snd).mul <| Real.smoothTransition.continuous.comp <|
        continuous_const.mul (continuous_snd.sub
          (hu.continuous.comp (continuous_subtypeVal.comp continuous_fst)))) (-M) M η)
    (TestFunction.memLp_smul_of_continuous hHc η) (I + I) (.of_forall fun m x hx => ?_)
    fun x hx => ?_
  · have hux := abs_lt.1 (hη x hx)
    refine (abs_sub _ _).trans <| add_le_add
      (Real.smoothTransition.abs_intervalIntegral_mul_le (hg.continuous.intervalIntegrable (-M) M))
      ?_
    rw [Function.comp_apply, hH_eq (u x), ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := g)).trans <| by
      simpa only [Real.norm_eq_abs] using setIntegral_mono_set
        (intervalIntegrable_iff.1 (hg.continuous.abs.intervalIntegrable (-M) M))
        (ae_of_all _ fun _ => abs_nonneg _)
        (by rw [uIoc_of_le hux.2.le, uIoc_of_le hle_M]
            exact .of_forall (Ioc_subset_Ioc_left hux.1.le))
  · have hux := abs_lt.1 (hη x hx)
    have hind_eq : ∫ t in (-M)..M, (Ioi (u x)).indicator g t = H (u x) := by
      rw [intervalIntegral.integral_of_le hle_M, setIntegral_indicator measurableSet_Ioi,
        Set.Ioc_inter_Ioi, sup_eq_right.2 hux.1.le, ← intervalIntegral.integral_of_le hux.2.le,
        hH_eq (u x)]
    rw [Function.comp_apply, ← hind_eq]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => |g t|)
      (.of_forall fun m => (hg.continuous.mul (Real.smoothTransition.continuous.comp
        (continuous_const.mul (continuous_id.sub continuous_const)))).aestronglyMeasurable)
      (.of_forall fun m => ae_of_all _ fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.abs_le_one _))
      (hg.continuous.abs.intervalIntegrable (-M) M) (ae_of_all _ fun t _ => by
        simpa [indicator_apply, mul_ite] using
          (Real.smoothTransition.tendsto_indicator id (u x) t).const_mul (g t))

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
  obtain ⟨M, hM, hφ_lt'⟩ := φ.exists_pos_norm_lt_of_continuousOn hu.continuous.continuousOn
  have hφ_lt : ∀ x : Ω, (x : E) ∈ tsupport φ → |u x| < M := fun x hx => by
    simpa [Real.norm_eq_abs] using hφ_lt' x hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (-M) M) fun t ht => by
      rw [slice_apply_eq_zero_of_notMem_Ioc hT hφ_lt ht, mul_zero],
    ← intervalIntegral.integral_of_le (by linarith : -M ≤ M)]
  let H : ℝ → ℝ := fun s => ∫ t in s..M, g t
  have hdH (s : ℝ) : HasDerivAt H (-g s) s :=
    intervalIntegral.integral_hasDerivAt_left (hg.continuous.intervalIntegrable s M)
      (hg.continuous.stronglyMeasurableAtFilter volume (𝓝 s)) hg.continuous.continuousAt
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
  have hc₁ (m : ℕ) : Continuous fun t => T (smulLeftCLM (hf m t) (extDerivCLM φ)) :=
    continuous_apply_smulLeftCLM_smoothTransition hT₁ hu (extDerivCLM φ) ((m : ℝ) + 1)
  have hc₂ (m : ℕ) : Continuous fun t => (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ) :=
    continuous_apply_smulLeftCLM_smoothTransition hT₂ hu φ ((m : ℝ) + 1)
  have hsub_eq (m : ℕ) :
      (∫ t in (-M)..M, g t * T (smulLeftCLM (hf m t) (extDerivCLM φ))) -
        (∫ t in (-M)..M, g t * (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ)) =
      ∫ t in (-M)..M, g t * (T (smulLeftCLM (hf m t) (extDerivCLM φ)) -
        (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ)) := by
    have hi₁ : IntervalIntegrable (fun t => g t * T (smulLeftCLM (hf m t) (extDerivCLM φ)))
        volume (-M) M := (hg.continuous.mul (hc₁ m)).intervalIntegrable (-M) M
    have hi₂ : IntervalIntegrable (fun t => g t * (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ))
        volume (-M) M := (hg.continuous.mul (hc₂ m)).intervalIntegrable (-M) M
    rw [← intervalIntegral.integral_sub hi₁ hi₂]
    simp_rw [mul_sub]
  have hlim_L : Tendsto (fun m : ℕ =>
      (∫ t in (-M)..M, g t * T (smulLeftCLM (hf m t) (extDerivCLM φ))) -
        ∫ t in (-M)..M, g t * (T ∘L extDerivCLM) (smulLeftCLM (hf m t) φ))
      atTop (𝓝 (∫ t in (-M)..M, g t * slice T u t φ)) := by
    simp_rw [hsub_eq]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => |g t| * C)
      (.of_forall fun m => (hg.continuous.mul ((hc₁ m).sub (hc₂ m))).aestronglyMeasurable)
      (.of_forall fun m => ae_of_all _ fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add
          (abs_apply_smulLeftCLM_smoothTransition_le hT₁ hu (extDerivCLM φ) m t)
          (abs_apply_smulLeftCLM_smoothTransition_le hT₂ hu φ m t))) (abs_nonneg _))
      ((hg.continuous.abs.intervalIntegrable (-M) M).mul_const C)
      (ae_of_all _ fun t _ => tendsto_const_nhds.mul <|
        (tendsto_neg_oneFormWedgeCLM_slice_apply hT hu t φ).congr fun m =>
          (apply_smulLeftCLM_extDerivCLM_sub T (hf m t) φ).symm)
  -- Apply the Leibniz rule to rewrite the limit in terms of `d(H ∘ u) = -(g ∘ u) du`.
  have hwedge : oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 (hH.comp hu)).2 φ =
      -smulLeftCLM (hg.comp hu) (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ) := by
    ext x
    have hfd : fderiv ℝ (H ∘ u) x = (-g (u x)) • fderiv ℝ u x :=
      ((hdH (u x)).comp_hasFDerivAt x ((hu.differentiable (by simp)) x).hasFDerivAt).fderiv
    have hsmul : ((-g (u x)) • fderiv ℝ u x).smulRight (φ x) =
        (-g (u x)) • (fderiv ℝ u x).smulRight (φ x) := by ext y; simp [smul_smul]
    rw [oneFormWedgeCLM_apply, hfd, hsmul, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
    simp [neg_smul]
  rw [tendsto_nhds_unique hlim_L hlim_R, apply_smulLeftCLM_extDerivCLM_sub T (hH.comp hu) φ,
    hwedge, map_neg, neg_neg]

/-- **Integrating all slices recovers contraction with `du`.** For a locally normal
`(k + 1)`-current `T` and smooth `u : E → ℝ`, `∫ ⟨T, u, t⟩(φ) dt = T(du ∧ φ)`. -/
theorem integral_slice_apply {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsLocallyNormal T) (hu : ContDiff ℝ ∞ u) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    ∫ t, slice T u t φ = T (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ) := by
  have hone : smulLeftCLM ((contDiff_const (c := (1 : ℝ))).comp hu)
      (oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ) =
      oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hu).2 φ := by ext x; simp
  simpa [hone] using integral_mul_slice_apply hT hu (contDiff_const (c := (1 : ℝ))) φ

end Distribution
