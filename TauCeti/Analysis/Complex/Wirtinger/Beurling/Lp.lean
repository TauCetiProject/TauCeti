/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Lp
public import TauCeti.Analysis.Complex.Pompeiu.Weak
public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Normed.Lp.SmoothApprox
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# The Cauchy transform of `Lᵖ` data is weakly differentiable

For `1 < p < ∞` and `f ∈ Lᵖ(ℂ)` supported in the closed disc of radius `r` about `c`, the Cauchy
transform `T f w = π⁻¹ ∫ (w - z)⁻¹ • f z` has a weak real derivative on the whole plane whose
Wirtinger parts are `∂ (T f) = B f` and `bar∂ (T f) = f`, where `B` is the Beurling operator
`TauCeti.beurlingLp` on `Lᵖ(ℂ)` (`TauCeti.hasWeakFDerivOn_cauchyTransform_of_memLp`). A real-linear
map `ℂ → F` with Wirtinger parts `a` and `b` is `v ↦ v • a + conj v • b`
(`TauCeti.wirtingerPartsCLM`), so the weak derivative is `w ↦ wirtingerPartsCLM (B f w) (f w)`.

The proof is by density. Smooth functions `g` supported in the disc of radius `r + 1` approximate
`f` in `Lᵖ`. For them the classical derivative of `T g` has Wirtinger parts `B g` (almost
everywhere, `HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp`) and `g`. On a
bounded disc `D_R`, `T g → T f` in `Lᵖ(D_R)` by the fixed-disc bound
`TauCeti.eLpNorm_cauchyTransform_le` with constant `2 (r + 1 + R)`, and `B g → B f` in `Lᵖ(ℂ)`
by continuity of `B`. Both convergences pass to `L¹(D_R)`, and weak derivatives survive `L¹`
limits (`TauCeti.hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub`). The discs exhaust the plane.

Consequences:

* `∂ (T f) = B f` almost everywhere for compactly supported `C¹` data
  (`HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp_of_contDiff_one`),
  extending the smooth case of `TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy`;
* the global derivative bound `‖D (T f)‖_{Lᵖ(ℂ)} ≤ (‖B‖ + 1) ‖f‖_{Lᵖ}` for all such `Lᵖ` data
  (`TauCeti.eLpNorm_weakFDeriv_cauchyTransform_le`); for `1 < p ≤ 2` and data with nonzero
  integral `T f` itself is not in `Lᵖ(ℂ)`, so only the derivative is bounded globally;
* the bound `T : Lᵖ(D_r) → W^{1,p}(D_R)` with explicit constant `2 (r + R) + ‖B‖ + 1`
  (`TauCeti.eLpNorm_cauchyTransform_add_eLpNorm_weakFDeriv_le`), and membership of `T f` in the
  local Sobolev class `W^{1,p}_loc` on every subset of the plane
  (`TauCeti.memWkpLoc_one_cauchyTransform_of_memLp`);
* continuity in parameters: for a family of data with common support depending continuously on a
  parameter in `Lᵖ`, the transforms depend continuously on it in `Lᵖ(D_R)` and their derivatives in
  `Lᵖ(ℂ)` (`TauCeti.continuous_toLp_cauchyTransform`,
  `TauCeti.continuous_toLp_weakFDeriv_cauchyTransform`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.2 (the Cauchy and Beurling operators on `Lᵖ`).
* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, second edition, Chapter V, §A
  (`∂ (P f) = T f` and `bar∂ (P f) = f` for `f ∈ Lᵖ`, `p > 2`, in the notation there).
-/

public noncomputable section

open MeasureTheory Complex ComplexConjugate Metric Filter Topology Function Set TopologicalSpace
open scoped ENNReal NNReal ContDiff

namespace TauCeti

/-! ### Real-linear maps through their Wirtinger parts -/

section Parts

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `a ↦ (v ↦ v • a)`, the complex-linear part. -/
private def holPartL : F →L[ℝ] ℂ →L[ℝ] F := (ContinuousLinearMap.lsmul ℝ ℂ).flip

/-- `b ↦ (v ↦ conj v • b)`, the complex-antilinear part. -/
private def antiPartL : F →L[ℝ] ℂ →L[ℝ] F :=
  ((ContinuousLinearMap.compL ℝ ℂ ℂ F).flip conjCLE.toContinuousLinearMap).comp holPartL

/-- The real-linear map `v ↦ v • a + conj v • b` of the plane into `F`. Its Wirtinger parts are
`a` and `b` (`TauCeti.fderiv_eq_wirtingerPartsCLM`), and it determines them
(`TauCeti.wirtingerPartsCLM_inj`). -/
@[expose] def wirtingerPartsCLM (a b : F) : ℂ →L[ℝ] F :=
  (ContinuousLinearMap.lsmul ℝ ℂ).flip a +
    ((ContinuousLinearMap.lsmul ℝ ℂ).flip b).comp conjCLE.toContinuousLinearMap

private theorem wirtingerPartsCLM_eq (a b : F) :
    wirtingerPartsCLM a b = holPartL a + antiPartL b := rfl

@[simp]
theorem wirtingerPartsCLM_apply (a b : F) (v : ℂ) :
    wirtingerPartsCLM a b v = v • a + conj v • b := rfl

theorem wirtingerPartsCLM_sub (a b a' b' : F) :
    wirtingerPartsCLM (a - a') (b - b') = wirtingerPartsCLM a b - wirtingerPartsCLM a' b' := by
  ext v
  simp only [wirtingerPartsCLM_apply, sub_apply, smul_sub]
  abel

/-- The operator norm of `v ↦ v • a + conj v • b` is at most `‖a‖ + ‖b‖`. -/
theorem norm_wirtingerPartsCLM_le (a b : F) : ‖wirtingerPartsCLM a b‖ ≤ ‖a‖ + ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [wirtingerPartsCLM_apply]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_smul, norm_smul, Complex.norm_conj]
  ring

/-- The two Wirtinger parts are determined by the real-linear map. -/
theorem wirtingerPartsCLM_inj {a b a' b' : F} :
    wirtingerPartsCLM a b = wirtingerPartsCLM a' b' ↔ a = a' ∧ b = b' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.1 ▸ h.2 ▸ rfl⟩
  have h1 := congrArg (· 1) h
  have hI := congrArg (· I) h
  simp only [wirtingerPartsCLM_apply, map_one, one_smul, conj_I, neg_smul] at h1 hI
  have hI' : a - b = a' - b' := by
    have := congrArg ((-I) • ·) hI
    simp only [smul_add, smul_neg, smul_smul, neg_mul, I_mul_I, neg_neg, one_smul] at this
    simpa only [sub_eq_add_neg] using this
  constructor
  · have h2 : (2 : ℂ) • a = (2 : ℂ) • a' := by
      rw [two_smul, two_smul]
      linear_combination (norm := module) h1 + hI'
    exact smul_right_injective F two_ne_zero h2
  · have h2 : (2 : ℂ) • b = (2 : ℂ) • b' := by
      rw [two_smul, two_smul]
      linear_combination (norm := module) h1 - hI'
    exact smul_right_injective F two_ne_zero h2

/-- In one variable the real derivative is the real-linear map with its two Wirtinger parts. -/
theorem fderiv_eq_wirtingerPartsCLM (f : ℂ → F) (x : ℂ) :
    fderiv ℝ f x = wirtingerPartsCLM (wirtingerDeriv f x 1) (conjWirtingerDeriv f x 1) := by
  ext v
  rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv, wirtingerPartsCLM_apply]

/-- Pointwise combination of two `Lᵖ` maps through `wirtingerPartsCLM` stays in `Lᵖ`. -/
theorem _root_.MeasureTheory.MemLp.wirtingerPartsCLM {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} {a b : α → F} (ha : MemLp a p μ) (hb : MemLp b p μ) :
    MemLp (fun x ↦ TauCeti.wirtingerPartsCLM (a x) (b x)) p μ := by
  refine ((holPartL.comp_memLp' ha).add (antiPartL.comp_memLp' hb)).ae_eq
    (.of_forall fun x ↦ ?_)
  simp only [Pi.add_apply, comp_apply, wirtingerPartsCLM_eq]

/-- The `Lᵖ` distance of two maps built by `wirtingerPartsCLM` is at most the sum of the `Lᵖ`
distances of their parts. -/
private theorem eLpNorm_wirtingerPartsCLM_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ≥0∞} (hq : 1 ≤ q) {a a' b b' : α → F} (ha : AEStronglyMeasurable (a - a') μ)
    (hb : AEStronglyMeasurable (b - b') μ) :
    eLpNorm (fun x ↦ wirtingerPartsCLM (a x) (b x) - wirtingerPartsCLM (a' x) (b' x)) q μ ≤
      eLpNorm (a - a') q μ + eLpNorm (b - b') q μ := by
  have hm : AEStronglyMeasurable
      (fun x ↦ wirtingerPartsCLM (a x) (b x) - wirtingerPartsCLM (a' x) (b' x)) μ := by
    refine ((holPartL.continuous.comp_aestronglyMeasurable ha).add
      (antiPartL.continuous.comp_aestronglyMeasurable hb)).congr (.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply, ← wirtingerPartsCLM_eq, wirtingerPartsCLM_sub]
  calc _ ≤ eLpNorm (fun x ↦ ‖(a - a') x‖ + ‖(b - b') x‖) q μ :=
        eLpNorm_mono_real hm fun x ↦ by
          rw [← wirtingerPartsCLM_sub]
          exact norm_wirtingerPartsCLM_le _ _
    _ ≤ eLpNorm (a - a') q μ + eLpNorm (b - b') q μ := by
        refine (eLpNorm_add_le (f := fun x ↦ ‖(a - a') x‖) (g := fun x ↦ ‖(b - b') x‖)
          hq).trans_eq ?_
        rw [eLpNorm_norm _ ha, eLpNorm_norm _ hb]

end Parts

/-! ### The weak derivative of the Cauchy transform of `Lᵖ` data -/

section Weak

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [InnerProductSpace ℂ F] [CompleteSpace F] [Fact (1 ≤ p)] in
/-- Compactly supported `Lᵖ` data, `1 ≤ p`, is integrable. -/
private theorem integrable_of_memLp_of_support_subset {f : ℂ → F} (hp : 1 ≤ p)
    (hf : MemLp f p volume) {c : ℂ} {r : ℝ} (hs : support f ⊆ closedBall c r) : Integrable f := by
  have : IsFiniteMeasure (volume.restrict (closedBall c r)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have h : Integrable ((closedBall c r).indicator f) :=
    (integrable_indicator_iff measurableSet_closedBall).2 (hf.restrict _ |>.integrable hp)
  rwa [indicator_eq_self.2 hs] at h

omit [Fact (1 ≤ p)] in
/-- On a finite measure, `Lᵖ` convergence to zero, `1 ≤ p`, implies `L¹` convergence to zero. -/
private theorem tendsto_lintegral_enorm_of_tendsto_eLpNorm {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ] (hp : 1 ≤ p) {u : ℕ → α → E}
    (hu : ∀ n, AEStronglyMeasurable (u n) μ)
    (h : Tendsto (fun n ↦ eLpNorm (u n) p μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫⁻ x, ‖u n x‖ₑ ∂μ) atTop (𝓝 0) := by
  have hq : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
    rcases eq_or_ne p (∞ : ℝ≥0∞) with rfl | hp_top
    · simp
    · have : 1 ≤ p.toReal := by
        simpa using ENNReal.toReal_mono hp_top hp
      simp only [ENNReal.toReal_one, div_one, sub_nonneg]
      exact div_le_one_of_le₀ this (by positivity)
  set C := μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal)
  have hC : C ≠ (∞ : ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg hq (measure_ne_top μ univ)
  have hup : Tendsto (fun n ↦ eLpNorm (u n) p μ * C) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const h (.inr hC)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ ↦ zero_le)
    fun n ↦ ?_
  rw [← eLpNorm_one_eq_lintegral_enorm (hu n)]
  exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hu n)

omit [CompleteSpace F] in
/-- For compactly supported `Lᵖ` data the Cauchy transform is additive almost everywhere on each
output disc. -/
private theorem cauchyTransform_sub_ae_eq {f g : ℂ → F} {c : ℂ} {r R : ℝ≥0}
    (hf : MemLp f p volume) (hg : MemLp g p volume) (hfs : support f ⊆ closedBall c (r : ℝ))
    (hgs : support g ⊆ closedBall c (r : ℝ)) :
    cauchyTransform (g - f) =ᵐ[volume.restrict (closedBall c (R : ℝ))]
      cauchyTransform g - cauchyTransform f := by
  have hp : 1 ≤ p := Fact.out
  filter_upwards [ae_integrable_cauchyTransform (R := R) hp (hf.restrict _) hfs,
    ae_integrable_cauchyTransform (R := R) hp (hg.restrict _) hgs] with w hwf hwg
  simp only [Pi.sub_apply, cauchyTransform_apply, ← smul_sub,
    ← integral_sub hwg hwf]

/-- On a disc, the weak derivative of the Cauchy transform of `Lᵖ` data supported in a disc. -/
private theorem hasWeakFDerivOn_cauchyTransform_ball (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {f : ℂ → F} (hf : MemLp f p volume)
    {c : ℂ} {r : ℝ≥0} (hs : support f ⊆ closedBall c (r : ℝ)) (R : ℝ≥0) :
    HasWeakFDerivOn volume ⟨ball c R, isOpen_ball⟩ (cauchyTransform f)
      fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top (hf.toLp f) w) (f w) := by
  set B := beurlingLp (F := F) p hp hp_top
  set Ω : Opens ℂ := ⟨ball c R, isOpen_ball⟩
  set t := closedBall c ((r + 1 : ℝ≥0) : ℝ)
  have hst : closedBall c (r : ℝ) ⊆ t := closedBall_subset_closedBall (by simp)
  have hfs : support f ⊆ t := hs.trans hst
  have hfint : Integrable f := integrable_of_memLp_of_support_subset hp.le hf hs
  have : IsFiniteMeasure (volume.restrict (ball c (R : ℝ))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- Smooth approximants supported in `t`.
  have ht : t ∈ 𝓝ˢ (closedBall c (r : ℝ)) :=
    mem_of_superset (isOpen_ball.mem_nhdsSet.2 (closedBall_subset_ball (by simp)))
      ball_subset_closedBall
  have happrox (n : ℕ) := hf.exist_contDiff_tsupport_subset_eLpNorm_sub_le hp_top hp.le
    isClosed_closedBall ht (.of_forall fun y hy ↦ notMem_support.1 fun h ↦ hy (hs h))
    (Nat.one_div_pos_of_nat (n := n))
  choose g hgc hg hgt hgf using happrox
  have hgm (n : ℕ) : MemLp (g n) p volume :=
    (hg n).continuous.memLp_of_hasCompactSupport (hgc n)
  have hgs (n : ℕ) : support (g n) ⊆ t := (subset_tsupport _).trans (hgt n)
  have hlim : Tendsto (fun n ↦ eLpNorm (g n - f) p volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ ↦ zero_le) fun n ↦ (eLpNorm_sub_comm _ _ _ _).trans_le (hgf n)
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  -- `B g → B f` in `Lᵖ(ℂ)`.
  have hBlim : Tendsto (fun n ↦ eLpNorm (⇑(B ((hgm n).toLp (g n))) - ⇑(B (hf.toLp f))) p volume)
      atTop (𝓝 0) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 ((B.continuous.tendsto _).comp ?_)
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hgm f hf).2 hlim
  -- The weak derivative of each smooth approximant.
  have hweak (n : ℕ) : HasWeakFDerivOn volume Ω (cauchyTransform (g n))
      fun w ↦ wirtingerPartsCLM (B ((hgm n).toLp (g n)) w) (g n w) := by
    have hT := (hgc n).contDiff_cauchyTransform (hg n)
    have hcl := hasWeakFDerivOn_of_differentiableOn (μ := volume) (Ω := Ω)
      ((hT.continuous_fderiv (by simp)).locallyIntegrable.locallyIntegrableOn _)
      fun x _ ↦ hT.differentiable (by simp) x
    refine hcl.congr_ae_deriv (ae_restrict_of_ae ?_)
    filter_upwards [(hgc n).wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp (hg n) hp hp_top]
      with w hw
    rw [fderiv_eq_wirtingerPartsCLM, hw,
      (hgc n).conjWirtingerDeriv_cauchyTransform ((hg n).of_le (by simp))]
  -- The limit derivative field is in `Lᵖ(ℂ)`.
  have hD : MemLp (fun w ↦ wirtingerPartsCLM (B (hf.toLp f) w) (f w)) p volume :=
    MemLp.wirtingerPartsCLM (Lp.memLp _) hf
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    ((locallyIntegrable_cauchyTransform hfint).locallyIntegrableOn _)
    (fun v ↦ (((ContinuousLinearMap.apply ℝ F v).comp_memLp' hD).locallyIntegrable
      hp.le).locallyIntegrableOn _) hweak ?_ ?_
  · -- `T g → T f` in `L¹` on the disc.
    refine tendsto_lintegral_enorm_of_tendsto_eLpNorm (μ := volume.restrict (ball c (R : ℝ)))
      hp.le (fun n ↦ ?_) ?_
    · exact ((locallyIntegrable_cauchyTransform ((hg n).continuous.integrable_of_hasCompactSupport
        (hgc n))).aestronglyMeasurable.sub
          (locallyIntegrable_cauchyTransform hfint).aestronglyMeasurable).restrict
    have hup : Tendsto (fun n ↦ ((2 * (r + 1 + R) : ℝ≥0) : ℝ≥0∞) * eLpNorm (g n - f) p volume)
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul hlim
        (.inr (ENNReal.coe_ne_top : ((2 * (r + 1 + R) : ℝ≥0) : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)))
      rwa [mul_zero] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ ↦ zero_le)
      fun n ↦ ?_
    calc eLpNorm (cauchyTransform (g n) - cauchyTransform f) p (volume.restrict (ball c R))
        ≤ eLpNorm (cauchyTransform (g n) - cauchyTransform f) p
            (volume.restrict (closedBall c R)) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono_set _ ball_subset_closedBall)
      _ = eLpNorm (cauchyTransform (g n - f)) p (volume.restrict (closedBall c R)) :=
          eLpNorm_congr_ae (cauchyTransform_sub_ae_eq hf (hgm n) hfs (hgs n)).symm
      _ ≤ (2 * (r + 1 + R) : ℝ≥0) * eLpNorm (g n - f) p (volume.restrict t) :=
          eLpNorm_cauchyTransform_le Fact.out
            ((hgm n).sub hf).aestronglyMeasurable.restrict
            ((support_sub _ _).trans (union_subset (hgs n) hfs))
      _ ≤ (2 * (r + 1 + R) : ℝ≥0) * eLpNorm (g n - f) p volume := by
          gcongr
          exact Measure.restrict_le_self
  · -- `D (T g) → D (T f)` in `L¹` on the disc.
    refine tendsto_lintegral_enorm_of_tendsto_eLpNorm (μ := volume.restrict (ball c (R : ℝ)))
      hp.le (fun n ↦ ((MemLp.wirtingerPartsCLM (Lp.memLp _) (hgm n)).aestronglyMeasurable.sub
        hD.aestronglyMeasurable).restrict) ?_
    have hup := hBlim.add hlim
    rw [add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ ↦ zero_le)
      fun n ↦ ?_
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (eLpNorm_wirtingerPartsCLM_sub_le hp.le
        ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
        ((hgm n).sub hf).aestronglyMeasurable)

/-- **The weak derivative of the Cauchy transform of `Lᵖ` data.** For `1 < p < ∞` and `f ∈ Lᵖ(ℂ)`
supported in a closed disc, the Cauchy transform `T f` is weakly differentiable on every open
subset of the plane, and its weak derivative has Wirtinger parts `∂ (T f) = B f`, the Beurling
operator applied to `f`, and `bar∂ (T f) = f`. -/
theorem hasWeakFDerivOn_cauchyTransform_of_memLp (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {f : ℂ → F} (hf : MemLp f p volume) {c : ℂ} {r : ℝ} (hs : support f ⊆ closedBall c r)
    (Ω : Opens ℂ) :
    HasWeakFDerivOn volume Ω (cauchyTransform f)
      fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top (hf.toLp f) w) (f w) := by
  have hs' : support f ⊆ closedBall c (r.toNNReal : ℝ) :=
    hs.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal r))
  refine hasWeakFDerivOn_iff_locally.2 fun x _ ↦
    ⟨⟨ball c ((‖x - c‖₊ + 1 : ℝ≥0) : ℝ), isOpen_ball⟩, ?_,
      hasWeakFDerivOn_cauchyTransform_ball hp hp_top hf hs' _⟩
  change x ∈ ball c _
  rw [mem_ball, dist_eq_norm]
  push_cast
  linarith

/-- **`∂ T = B` on compactly supported `C¹` data.** For `1 < p < ∞` and compactly supported `C¹`
data `f`, the Wirtinger derivative `∂ (T f)` agrees almost everywhere with the Beurling operator
on `Lᵖ(ℂ)` applied to `f`. -/
theorem _root_.HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp_of_contDiff_one
    {f : ℂ → F} (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) =ᵐ[volume]
      beurlingLp p hp hp_top ((hf.continuous.memLp_of_hasCompactSupport hc).toLp f) := by
  have hfm : MemLp f p volume := hf.continuous.memLp_of_hasCompactSupport hc
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hT := hc.contDiff_cauchyTransform hf
  have hcl := (hasWeakFDerivOn_cauchyTransform_of_memLp hp hp_top hfm
    ((subset_tsupport f).trans hr) ⊤).ae_eq_fderiv
      ((hT.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      fun x _ ↦ hT.differentiable one_ne_zero x
  rw [Opens.coe_top, Measure.restrict_univ] at hcl
  filter_upwards [hcl] with w hw
  rw [fderiv_eq_wirtingerPartsCLM, hc.conjWirtingerDeriv_cauchyTransform hf] at hw
  exact (wirtingerPartsCLM_inj.1 hw).1.symm

/-- **The global derivative bound for the Cauchy transform of `Lᵖ` data.** The weak derivative
`v ↦ v • B f + conj v • f` of `T f` has `Lᵖ(ℂ)` norm at most `(‖B‖ + 1) ‖f‖_{Lᵖ}`, where `‖B‖` is
the operator norm of the Beurling operator on `Lᵖ(ℂ)`. For `1 < p ≤ 2` and data with nonzero
integral `T f` itself is not in `Lᵖ(ℂ)`, so only the derivative is bounded globally. -/
theorem eLpNorm_weakFDeriv_cauchyTransform_le (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {f : ℂ → F} (hf : MemLp f p volume) :
    eLpNorm (fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top (hf.toLp f) w) (f w)) p volume ≤
      ((‖beurlingLp (F := F) p hp hp_top‖₊ : ℝ≥0∞) + 1) * eLpNorm f p volume := by
  set B := beurlingLp (F := F) p hp hp_top
  set a := ⇑(B (hf.toLp f))
  have ha : AEStronglyMeasurable a volume := Lp.aestronglyMeasurable _
  have hB : eLpNorm a p volume ≤ ‖B‖₊ * eLpNorm f p volume :=
    calc eLpNorm a p volume = ‖B (hf.toLp f)‖ₑ := (Lp.enorm_def _).symm
      _ ≤ ‖B‖₊ * ‖hf.toLp f‖ₑ := by
          simp only [enorm_eq_nnnorm]
          exact_mod_cast B.le_opNNNorm _
      _ = ‖B‖₊ * eLpNorm f p volume := by
          rw [Lp.enorm_def, eLpNorm_congr_ae hf.coeFn_toLp]
  calc eLpNorm (fun w ↦ wirtingerPartsCLM (a w) (f w)) p volume
      ≤ eLpNorm (fun w ↦ ‖a w‖ + ‖f w‖) p volume :=
        eLpNorm_mono_real (MemLp.wirtingerPartsCLM (Lp.memLp _) hf).aestronglyMeasurable
          fun w ↦ norm_wirtingerPartsCLM_le _ _
    _ ≤ eLpNorm a p volume + eLpNorm f p volume := by
        refine (eLpNorm_add_le (f := fun w ↦ ‖a w‖) (g := fun w ↦ ‖f w‖) hp.le).trans_eq ?_
        rw [eLpNorm_norm _ ha, eLpNorm_norm _ hf.aestronglyMeasurable]
    _ ≤ ‖B‖₊ * eLpNorm f p volume + eLpNorm f p volume := by gcongr
    _ = ((‖B‖₊ : ℝ≥0∞) + 1) * eLpNorm f p volume := by ring

/-- **`T : Lᵖ(D_r) → W^{1,p}(D_R)` is bounded.** For `1 < p < ∞`, data `f ∈ Lᵖ` supported in the
closed disc of radius `r` about `c`, and every output radius `R`, the `Lᵖ` norms on the closed disc
of radius `R` of `T f` and of its weak derivative sum to at most `2 (r + R) + ‖B‖ + 1` times
`‖f‖_{Lᵖ}`, where `‖B‖` is the operator norm of the Beurling operator on `Lᵖ(ℂ)`. -/
theorem eLpNorm_cauchyTransform_add_eLpNorm_weakFDeriv_le (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {f : ℂ → F} (hf : MemLp f p volume) {c : ℂ} {r : ℝ≥0} (hs : support f ⊆ closedBall c r)
    (R : ℝ≥0) :
    eLpNorm (cauchyTransform f) p (volume.restrict (closedBall c R)) +
        eLpNorm (fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top (hf.toLp f) w) (f w)) p
          (volume.restrict (closedBall c R)) ≤
      ((2 * (r + R) + ‖beurlingLp (F := F) p hp hp_top‖₊ + 1 : ℝ≥0) : ℝ≥0∞) *
        eLpNorm f p volume := by
  have h₁ : eLpNorm (cauchyTransform f) p (volume.restrict (closedBall c R)) ≤
      (2 * (r + R) : ℝ≥0) * eLpNorm f p volume :=
    (eLpNorm_cauchyTransform_le hp.le hf.aestronglyMeasurable.restrict hs).trans
      (by gcongr; exact Measure.restrict_le_self)
  have h₂ := (eLpNorm_mono_measure
    (fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top (hf.toLp f) w) (f w))
    (Measure.restrict_le_self (s := closedBall c (R : ℝ)))).trans
      (eLpNorm_weakFDeriv_cauchyTransform_le hp hp_top hf)
  calc _ ≤ (2 * (r + R) : ℝ≥0) * eLpNorm f p volume +
        ((‖beurlingLp (F := F) p hp hp_top‖₊ : ℝ≥0∞) + 1) * eLpNorm f p volume :=
        add_le_add h₁ h₂
    _ = _ := by
        push_cast
        ring

/-- **The Cauchy transform of `Lᵖ` data is locally `W^{1,p}`.** For `1 < p < ∞` and `f ∈ Lᵖ(ℂ)`
supported in a closed disc, `T f` belongs to the local Sobolev class `W^{1,p}_loc` on every subset
of the plane. -/
theorem memWkpLoc_one_cauchyTransform_of_memLp (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {f : ℂ → F} (hf : MemLp f p volume) {c : ℂ} {r : ℝ} (hs : support f ⊆ closedBall c r)
    (U : Set ℂ) : MemWkpLoc p U 1 (cauchyTransform f) := by
  have hs' : support f ⊆ closedBall c (r.toNNReal : ℝ) :=
    hs.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal r))
  refine memWkpLoc_succ_iff.2 ⟨memLpLoc_iff.2 fun K _ hK ↦ ?_, _,
    hasWeakFDerivOn_cauchyTransform_of_memLp hp hp_top hf hs _,
    memWkpLoc_zero_iff.2 <| memLpLoc_iff.2 fun K _ _ ↦
      (MemLp.wirtingerPartsCLM (Lp.memLp _) hf).restrict K⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall c
  exact (memLp_cauchyTransform (R := R.toNNReal) hp.le (hf.restrict _) hs').mono_measure
    (Measure.restrict_mono_set _
      (hR.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal R))))

omit [CompleteSpace F] in
/-- **Continuity in parameters of the function term.** For a family `f x` of `Lᵖ` data with a
common support disc of radius `r` about `c`, depending continuously on `x` in `Lᵖ(ℂ)`, the Cauchy
transforms `T (f x)` depend continuously on `x` in `Lᵖ` of the closed disc of radius `R`. -/
theorem continuous_toLp_cauchyTransform {X : Type*} [TopologicalSpace X] {f : X → ℂ → F}
    (hf : ∀ x, MemLp (f x) p volume) {c : ℂ} {r : ℝ≥0}
    (hs : ∀ x, support (f x) ⊆ closedBall c r) (hcont : Continuous fun x ↦ (hf x).toLp (f x))
    (R : ℝ≥0) :
    Continuous fun x ↦ (memLp_cauchyTransform (R := R) (Fact.out : 1 ≤ p) ((hf x).restrict _)
      (hs x)).toLp (cauchyTransform (f x)) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hf _ (hf x)).1 (hcont.tendsto x)
  refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 ?_
  have hup := ENNReal.Tendsto.const_mul h
    (.inr (ENNReal.coe_ne_top : ((2 * (r + R) : ℝ≥0) : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)))
  rw [mul_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ ↦ zero_le)
    fun y ↦ ?_
  calc eLpNorm (cauchyTransform (f y) - cauchyTransform (f x)) p
        (volume.restrict (closedBall c R))
      = eLpNorm (cauchyTransform (f y - f x)) p (volume.restrict (closedBall c R)) :=
        eLpNorm_congr_ae (cauchyTransform_sub_ae_eq (hf x) (hf y) (hs x) (hs y)).symm
    _ ≤ (2 * (r + R) : ℝ≥0) * eLpNorm (f y - f x) p (volume.restrict (closedBall c r)) :=
        eLpNorm_cauchyTransform_le Fact.out ((hf y).sub (hf x)).aestronglyMeasurable.restrict
          ((support_sub _ _).trans (union_subset (hs y) (hs x)))
    _ ≤ (2 * (r + R) : ℝ≥0) * eLpNorm (f y - f x) p volume := by
        gcongr
        exact Measure.restrict_le_self

/-- **Continuity in parameters of the derivative term.** For a family `f x` of `Lᵖ` data depending
continuously on `x` in `Lᵖ(ℂ)`, `1 < p < ∞`, the weak derivatives `v ↦ v • B (f x) + conj v • f x`
of the Cauchy transforms depend continuously on `x` in `Lᵖ(ℂ)`. -/
theorem continuous_toLp_weakFDeriv_cauchyTransform (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {X : Type*} [TopologicalSpace X] {f : X → ℂ → F} (hf : ∀ x, MemLp (f x) p volume)
    (hcont : Continuous fun x ↦ (hf x).toLp (f x)) :
    Continuous fun x ↦ (MemLp.wirtingerPartsCLM
      (Lp.memLp (beurlingLp p hp hp_top ((hf x).toLp (f x)))) (hf x)).toLp
        fun w ↦ wirtingerPartsCLM (beurlingLp p hp hp_top ((hf x).toLp (f x)) w) (f x w) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hf _ (hf x)).1 (hcont.tendsto x)
  have hB := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
    (((beurlingLp p hp hp_top).continuous.comp hcont).tendsto x)
  refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 ?_
  have hup := hB.add h
  rw [add_zero] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ ↦ zero_le)
    fun y ↦ eLpNorm_wirtingerPartsCLM_sub_le hp.le
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
      ((hf y).sub (hf x)).aestronglyMeasurable

end Weak

end TauCeti
