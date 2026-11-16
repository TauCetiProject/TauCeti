/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# The L² Brownian Itô integral process

For a Brownian-integrable predictable integrand `H` (`TauCeti.BrownianIntegrable`) and a filtered
pre-Brownian motion `W`, any process satisfying `TauCeti.IsItoIntegral ℱ P W H I` agrees almost
surely at every time `t` with the finite-horizon predictable L² Brownian integral
`hW.l2Integral t` (`ae_eq_l2Integral_of_isItoIntegral`). This yields square integrability, mean
zero, the bilinear cross-isometry (`integral_mul_of_isItoIntegral`), the Itô isometry and the
martingale property (`itoIntegral_isometry`) without requiring Brownian path continuity or usual
filtration conditions.

When `W` has almost surely continuous paths, every `BrownianIntegrable` integrand admits a
strongly predictable, almost surely continuous square-integrable martingale Itô integral
(`exists_isItoIntegral_of_brownianIntegrable`), constructed via continuous L²-martingale
completion of elementary integrals, together with an elementary approximating sequence whose
integrals converge almost surely uniformly on every finite horizon
(`exists_seq_elementaryIntegrand_tendstoUniformlyOn`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}

/-- A Brownian-integrable process belongs to `L²` of the finite-horizon predictable measure. -/
theorem BrownianIntegrable.memLp_predictableMeasure
    (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 (ℱ.predictableMeasure P T) :=
  (ℱ.memLp_predictableMeasure_iff P hH.isStronglyPredictable T 2).mpr (by
    simpa only [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def] using hH.memLp T)

end TauCeti

namespace MeasureTheory.Filtration

open TauCeti TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A left-open interval indicator weighted by an `ℱ s`-measurable height is predictable. -/
private theorem stronglyMeasurable_predictable_indicator_Ioc_mul (ℱ : Filtration ℝ≥0 mΩ)
    (s t : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ p.2) p.1) := by
  have hp : StronglyMeasurable[ℱ.predictable]
      (Function.uncurry
        (Finance.simpleHolding (fun k ↦ if k = 0 then s else t) 1 (fun _ ↦ ξ))) :=
    Finance.isStronglyPredictable_simpleHolding (ℱ := ℱ)
      (fun j hj ↦ by rcases Nat.lt_one_iff.mp hj with rfl; exact hξ)
  convert hp using 1
  ext ⟨u, ω⟩
  simp [Finance.simpleHolding_def]

/-- A left-open interval indicator weighted by a square-integrable `ℱ s`-measurable height belongs
to `L²` of the finite-horizon predictable measure. -/
theorem memLp_predictableMeasure_indicator_Ioc_mul (ℱ : Filtration ℝ≥0 mΩ)
    {P : Measure Ω} [IsFiniteMeasure P] (T s t : ℝ≥0)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ p.2) p.1) 2
      (ℱ.predictableMeasure P T) := by
  rw [ℱ.memLp_predictableMeasure_iff P
    (ℱ.stronglyMeasurable_predictable_indicator_Ioc_mul s t hξ) T 2]
  convert (hξ₂.comp_snd (timeMeasure T)).indicator
    ((measurableSet_Ioc (a := s) (b := t)).prod MeasurableSet.univ).nullMeasurableSet using 1
  ext ⟨u, ω⟩
  by_cases hu : u ∈ Ioc s t <;> simp [hu]

end MeasureTheory.Filtration

namespace TauCeti.Probability

/-- Convergence to zero in `L²((timeMeasure t).prod P)` implies convergence to zero in probability
of the pathwise square energies on `(0, t]`. -/
theorem tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [SFinite P]
    {F : ℕ → ℝ≥0 → Ω → ℝ} (hF : ∀ n, Measurable (Function.uncurry (F n))) {t : ℝ≥0}
    (hlim : Tendsto (fun n ↦ eLpNorm (Function.uncurry (F n)) 2 ((timeMeasure t).prod P))
      atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ε ≤ ∫⁻ s, ‖F n s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) := by
  let δ : ℝ≥0∞ := min ε 1
  have hδpos : 0 < δ := lt_min hε zero_lt_one
  have hδtop : δ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right ε 1)
  have hsq : Tendsto (fun n ↦ δ⁻¹ *
      eLpNorm (Function.uncurry (F n)) 2 ((timeMeasure t).prod P) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      ENNReal.Tendsto.const_mul (ENNReal.Tendsto.pow (n := 2) hlim)
        (Or.inr (ENNReal.inv_ne_top.mpr hδpos.ne'))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq
    (fun _ ↦ zero_le) fun n ↦ ?_
  have hmeas : Measurable (fun p : ℝ≥0 × Ω ↦ ‖Function.uncurry (F n) p‖ₑ ^ 2) :=
    (hF n).eNorm.pow_const 2
  have hmarkov : P {ω | δ ≤ ∫⁻ s, ‖F n s ω‖ₑ ^ 2 ∂timeMeasure t} * δ ≤
      eLpNorm (Function.uncurry (F n)) 2 ((timeMeasure t).prod P) ^ 2 := by
    have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      (hF n).aestronglyMeasurable (μ := (timeMeasure t).prod P)
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at hpow
    rw [mul_comm, hpow, lintegral_prod _ hmeas.aemeasurable,
      lintegral_lintegral_swap hmeas.aemeasurable]
    exact mul_meas_ge_le_lintegral₀ hmeas.lintegral_prod_left'.aemeasurable δ
  rw [← ENNReal.div_eq_inv_mul]
  exact (measure_mono fun _ hω ↦ (min_le_left ε 1).trans hω).trans
    ((ENNReal.le_div_iff_mul_le (.inl hδpos.ne') (.inl hδtop)).2 hmarkov)

end TauCeti.Probability

namespace TauCeti.Probability.IsFilteredPreBrownianReal

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- For `s ≤ t`, the clipped increment `W (max s (min t T)) - W s` equals
`W (min t T) - W (min s T)`. -/
private theorem sub_max_min_eq_sub_min {s t : ℝ≥0} (hst : s ≤ t) (T : ℝ≥0) (ω : Ω) :
    W (max s (min t T)) ω - W s ω = W (min t T) ω - W (min s T) ω := by
  by_cases hsT : s ≤ T
  · rw [min_eq_left hsT, max_eq_right (le_min hst hsT)]
  · have hTs : T ≤ s := le_of_not_ge hsT
    rw [min_eq_right hTs, min_eq_right (hTs.trans hst), max_eq_left hTs, sub_self, sub_self]

/-- The predictable L² Brownian integral of a single left-open interval weighted by an arbitrary
square-integrable `ℱ s`-measurable height equals the height times the clipped Brownian increment. -/
theorem coeFn_l2Integral_indicator_Ioc_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P)
    (hmem : MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ p.2) p.1) 2
      (ℱ.predictableMeasure P T)) :
    hW.l2Integral T (hmem.toLp _) =ᵐ[P]
      fun ω ↦ ξ ω * (W (min t T) ω - W (min s T) ω) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let t' : ℝ≥0 := max s (min t T)
  have hst' : s ≤ t' := le_max_left _ _
  have hae_pred {u v : Ω → ℝ} (hu : StronglyMeasurable[ℱ s] u) (hv : StronglyMeasurable[ℱ s] v)
      (h : u =ᵐ[P] v) :
      (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ u p.2) p.1) =ᵐ[ℱ.predictableMeasure P T]
        (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ v p.2) p.1) := by
    have hset : MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω |
        (Ioc s t).indicator (fun _ ↦ u p.2) p.1 ≠ (Ioc s t).indicator (fun _ ↦ v p.2) p.1} :=
      (measurableSet_eq_fun (ℱ.stronglyMeasurable_predictable_indicator_Ioc_mul s t hu).measurable
        (ℱ.stronglyMeasurable_predictable_indicator_Ioc_mul s t hv).measurable).compl
    rw [EventuallyEq, ae_iff, ℱ.predictableMeasure_def,
      trim_measurableSet_eq ℱ.predictable_le_prod hset, ← ae_iff]
    exact (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P) |>.ae h).mono
      fun p hp ↦ by simp [hp]
  let mk (f : lpMeas ℝ ℝ (ℱ s) 2 P) : Ω → ℝ := (mem_lpMeas_iff_aestronglyMeasurable.mp f.2).mk f
  have hmk_meas (f) : StronglyMeasurable[ℱ s] (mk f) :=
    (mem_lpMeas_iff_aestronglyMeasurable.mp f.2).stronglyMeasurable_mk
  have hmk_ae (f : lpMeas ℝ ℝ (ℱ s) 2 P) : ((f : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] mk f :=
    (mem_lpMeas_iff_aestronglyMeasurable.mp f.2).ae_eq_mk
  have hmk_memLp (f : lpMeas ℝ ℝ (ℱ s) 2 P) : MemLp (mk f) 2 P :=
    (Lp.memLp (f : Lp ℝ 2 P)).ae_eq (hmk_ae f)
  have hmk_add (f g) : mk (f + g) =ᵐ[P] fun ω ↦ mk f ω + mk g ω :=
    (hmk_ae (f + g)).symm.trans ((Lp.coeFn_add (f : Lp ℝ 2 P) g).trans ((hmk_ae f).add (hmk_ae g)))
  have htoP (f : lpMeas ℝ ℝ (ℱ s) 2 P) :=
    ℱ.memLp_predictableMeasure_indicator_Ioc_mul T s t (hmk_meas f) (hmk_memLp f)
  have hΨm (f : lpMeas ℝ ℝ (ℱ s) 2 P) := hW.memLp_mul_sub hst' (hmk_meas f) (hmk_memLp f)
  let Φ (f : lpMeas ℝ ℝ (ℱ s) 2 P) : Lp ℝ 2 P := hW.l2Integral T ((htoP f).toLp _)
  let Ψ (f : lpMeas ℝ ℝ (ℱ s) 2 P) : Lp ℝ 2 P := (hΨm f).toLp _
  have hΦ_add (f g) : Φ (f + g) = Φ f + Φ g := by
    dsimp only [Φ]; rw [← map_add]; congr 1; apply Lp.ext
    filter_upwards [(htoP (f + g)).coeFn_toLp, Lp.coeFn_add ((htoP f).toLp _) ((htoP g).toLp _),
      (htoP f).coeFn_toLp, (htoP g).coeFn_toLp,
      hae_pred (hmk_meas (f + g)) ((hmk_meas f).add (hmk_meas g)) (hmk_add f g)]
      with p h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5]
    by_cases hp : p.1 ∈ Ioc s t <;> simp [hp]
  have hΨ_add (f g) : Ψ (f + g) = Ψ f + Ψ g := by
    dsimp only [Ψ]; apply Lp.ext
    filter_upwards [(hΨm (f + g)).coeFn_toLp, Lp.coeFn_add ((hΨm f).toLp _) ((hΨm g).toLp _),
      (hΨm f).coeFn_toLp, (hΨm g).coeFn_toLp, hmk_add f g] with ω h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, add_mul]
  have hΦ_bound (f) : ‖Φ f‖ ≤ ((timeMeasure T Set.univ) ^ (2 : ℝ)⁻¹).toReal * ‖f‖ := by
    have hfn : ‖f‖ = (eLpNorm (mk f) 2 P).toReal := by
      change ‖(f : Lp ℝ 2 P)‖ = _
      rw [Lp.norm_def, eLpNorm_congr_ae (hmk_ae f)]
    rw [LinearIsometry.norm_map, Lp.norm_toLp, ℱ.predictableMeasure_def,
      eLpNorm_trim ℱ.predictable_le_prod
        (ℱ.stronglyMeasurable_predictable_indicator_Ioc_mul s t (hmk_meas f)),
      hfn, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top (by finiteness) (hmk_memLp f).eLpNorm_ne_top) ?_
    calc eLpNorm (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ mk f p.2) p.1) 2
          ((timeMeasure T).prod P)
        ≤ eLpNorm (mk f ∘ Prod.snd) 2 ((timeMeasure T).prod P) :=
          eLpNorm_mono ((ℱ.stronglyMeasurable_predictable_indicator_Ioc_mul s t (hmk_meas f)).mono
            ℱ.predictable_le_prod).aestronglyMeasurable
            fun p ↦ by by_cases h : p.1 ∈ Ioc s t <;> simp [h]
      _ = eLpNorm (mk f) 2 ((timeMeasure T Set.univ) • P) := by
          rw [← Measure.map_snd_prod,
            eLpNorm_map_measure ((hmk_meas f).mono (ℱ.le s)).aestronglyMeasurable
              measurable_snd.aemeasurable]
      _ ≤ (timeMeasure T Set.univ) ^ (2 : ℝ)⁻¹ * eLpNorm (mk f) 2 P := by
          simpa only [smul_eq_mul, one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using
            eLpNorm_smul_measure_le (timeMeasure T Set.univ) (mk f) 2 P
  have hΨ_bound (f) : ‖Ψ f‖ ≤ √((t' : ℝ) - s) * ‖f‖ := by
    have hsq {g : Ω → ℝ} (hg : MemLp g 2 P) : ‖hg.toLp g‖ ^ 2 = ∫ ω, g ω ^ 2 ∂P := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      exact integral_congr_ae (hg.coeFn_toLp.mono fun ω hω ↦ by simp [hω, sq])
    have hfnorm : ‖(hmk_memLp f).toLp _‖ = ‖f‖ :=
      congrArg norm (Lp.ext ((hmk_memLp f).coeFn_toLp.trans (hmk_ae f).symm))
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg f),
      ← Real.sqrt_mul (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst'))]
    refine Real.sqrt_le_sqrt (le_of_eq ?_)
    rw [hsq, hW.integral_sq_mul_sub hst' (hmk_meas f), ← hsq (hmk_memLp f), hfnorm, mul_comm]
  have hΦΨ : ∀ g : Lp ℝ 2 P, AEStronglyMeasurable[ℱ s] g P →
      ∀ hg : g ∈ lpMeas ℝ ℝ (ℱ s) 2 P, Φ ⟨g, hg⟩ = Ψ ⟨g, hg⟩ :=
    Lp.induction_stronglyMeasurable (ℱ.le s) (by norm_num)
      (fun g ↦ ∀ hg : g ∈ lpMeas ℝ ℝ (ℱ s) 2 P, Φ ⟨g, hg⟩ = Ψ ⟨g, hg⟩)
      (fun c A hA hμA hg ↦ by
        let fc : lpMeas ℝ ℝ (ℱ s) 2 P := ⟨_, hg⟩
        have hfc_ae : mk fc =ᵐ[P] A.indicator (fun _ ↦ c) :=
          (hmk_ae fc).symm.trans (by
            rw [show (fc : Lp ℝ 2 P) = indicatorConstLp 2 (ℱ.le s A hA) hμA.ne c from
              Lp.simpleFunc.coe_indicatorConst _ _ _]
            exact indicatorConstLp_coeFn)
        have hEq : (htoP fc).toLp _ =
            indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
              (measure_ne_top _ _) c := by
          apply Lp.ext
          filter_upwards [(htoP fc).coeFn_toLp,
            indicatorConstLp_coeFn (p := 2) (c := c)
              (hs := measurableSet_predictable_Ioc_prod s t hA) (hμs := measure_ne_top _ _),
            hae_pred (hmk_meas fc) (stronglyMeasurable_const.indicator hA) hfc_ae] with p h1 h2 h3
          rw [h1, h2, h3]
          by_cases h1' : p.1 ∈ Ioc s t <;> by_cases h2' : p.2 ∈ A <;> simp [h1', h2']
        apply Lp.ext
        filter_upwards [Lp.ext_iff.mp (congrArg (hW.l2Integral T) hEq),
          hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T s t hA c, (hΨm fc).coeFn_toLp, hfc_ae]
          with ω h1 h2 h3 h4
        dsimp only [Φ, Ψ]
        rw [h1, h2, h3, h4])
      (fun f g hf hg hfm hgm _ h1 h2 hfg ↦ by
        have hf' : hf.toLp f ∈ lpMeas ℝ ℝ (ℱ s) 2 P := mem_lpMeas_iff_aestronglyMeasurable.mpr
          (hfm.aestronglyMeasurable.congr hf.coeFn_toLp.symm)
        have hg' : hg.toLp g ∈ lpMeas ℝ ℝ (ℱ s) 2 P := mem_lpMeas_iff_aestronglyMeasurable.mpr
          (hgm.aestronglyMeasurable.congr hg.coeFn_toLp.symm)
        have : (⟨hf.toLp f + hg.toLp g, hfg⟩ : lpMeas ℝ ℝ (ℱ s) 2 P) = ⟨_, hf'⟩ + ⟨_, hg'⟩ := rfl
        rw [this, hΦ_add, hΨ_add, h1 hf', h2 hg'])
      (by
        convert isClosed_eq
          (AddMonoidHomClass.continuous_of_bound (AddMonoidHom.mk' Φ hΦ_add) _ hΦ_bound)
          (AddMonoidHomClass.continuous_of_bound (AddMonoidHom.mk' Ψ hΨ_add) _ hΨ_bound) using 1
        ext f; exact ⟨fun h ↦ h f.2, fun h _ ↦ h⟩)
  have hfξ_mem : hξ₂.toLp ξ ∈ lpMeas ℝ ℝ (ℱ s) 2 P :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr (hξ.aestronglyMeasurable.congr hξ₂.coeFn_toLp.symm)
  let fξ : lpMeas ℝ ℝ (ℱ s) 2 P := ⟨hξ₂.toLp ξ, hfξ_mem⟩
  have hfξ_ae : mk fξ =ᵐ[P] ξ := (hmk_ae fξ).symm.trans hξ₂.coeFn_toLp
  have hL : hmem.toLp _ = (htoP fξ).toLp _ :=
    Lp.ext (hmem.coeFn_toLp.trans ((hae_pred (hmk_meas fξ) hξ hfξ_ae).symm.trans
      (htoP fξ).coeFn_toLp.symm))
  filter_upwards [Lp.ext_iff.mp ((congrArg (hW.l2Integral T) hL).trans
      (hΦΨ _ (mem_lpMeas_iff_aestronglyMeasurable.mp hfξ_mem) hfξ_mem)),
    (hΨm fξ).coeFn_toLp, hfξ_ae] with ω h1 h2 h3
  dsimp only [Ψ] at h1
  rw [h1, h2, h3, sub_max_min_eq_sub_min hst T ω]

/-- On any elementary integrand `K`, the finite-horizon predictable L² Brownian integral agrees
almost surely with the elementary integral `K.integral W T`. -/
theorem coeFn_l2Integral_elementaryIntegrand (hW : IsFilteredPreBrownianReal ℱ W P)
    (K : ElementaryIntegrand ℱ) (T : ℝ≥0)
    (hmem : MemLp (Function.uncurry K.toProcess) 2 (ℱ.predictableMeasure P T)) :
    hW.l2Integral T (hmem.toLp (Function.uncurry K.toProcess)) =ᵐ[P] K.integral W T := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hξ₂ (i : Fin K.n) : MemLp (K.ξ i) 2 P :=
    let ⟨C, hC⟩ := K.bounded i
    MemLp.of_bound ((K.stronglyMeasurable i).mono (ℱ.le _)).aestronglyMeasurable
      C (.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hC ω)
  have hterm (i : Fin K.n) := ℱ.memLp_predictableMeasure_indicator_Ioc_mul (P := P) T
    (K.s i.castSucc) (K.s i.succ) (K.stronglyMeasurable i) (hξ₂ i)
  have hsum : hmem.toLp (Function.uncurry K.toProcess) = ∑ i : Fin K.n, (hterm i).toLp _ := by
    apply Lp.ext
    filter_upwards [hmem.coeFn_toLp, Lp.coeFn_finsetSum Finset.univ (fun i ↦ (hterm i).toLp _),
      ae_all_iff.mpr fun i ↦ (hterm i).coeFn_toLp] with p h1 h2 h3
    rw [h1, h2, Finset.sum_apply, Function.uncurry_apply_pair, K.toProcess_def]
    exact Finset.sum_congr rfl fun i _ ↦ (h3 i).symm
  have hmap := (congrArg (hW.l2Integral T) hsum).trans (map_sum _ _ _)
  filter_upwards [Lp.ext_iff.mp hmap,
    Lp.coeFn_finsetSum Finset.univ (fun i ↦ hW.l2Integral T ((hterm i).toLp _)),
    ae_all_iff.mpr fun i ↦ hW.coeFn_l2Integral_indicator_Ioc_mul T (K.mono i.castSucc_le_succ)
      (K.stronglyMeasurable i) (hξ₂ i) (hterm i)] with ω h1 h2 h3
  rw [h1, h2, Finset.sum_apply, K.integral_def]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h3 i, min_comm T, min_comm T]

/-- Helper: extract a single sequence of `ElementaryIntegrand`s approximating a `BrownianIntegrable`
integrand in `L²((timeMeasure T).prod P)` on every finite horizon `T`. -/
private theorem exists_seq_elementaryIntegrand_tendsto_eLpNorm [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    ∃ K : ℕ → ElementaryIntegrand ℱ, ∀ T : ℝ≥0,
      Tendsto (fun m ↦ eLpNorm (fun p : ℝ≥0 × Ω ↦ (K m).toProcess p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P)) atTop (𝓝 0) := by
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  refine ⟨fun m ↦ ElementaryIntegrand.ofSimple (n m) (τ m) (a m) (hτ m).monotoneOn (ha m)
    (fun j hj ↦ ⟨C m, fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩),
    fun T ↦ by simpa only [ElementaryIntegrand.toProcess_ofSimple] using hlim T⟩

/-- The `L²(P)` distance between two finite-horizon predictable L² Brownian integrals equals the
time-product `L²` distance between their integrands on `(0, t]`. -/
theorem eLpNorm_l2Integral_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : BrownianIntegrable ℱ P H₁) (hH₂ : BrownianIntegrable ℱ P H₂)
    (t : ℝ≥0) :
    eLpNorm ((hW.l2Integral t ((hH₁.memLp_predictableMeasure t).toLp (Function.uncurry H₁)) :
        Ω → ℝ) -
      (hW.l2Integral t ((hH₂.memLp_predictableMeasure t).toLp (Function.uncurry H₂)) : Ω → ℝ))
      2 P = eLpNorm (Function.uncurry H₁ - Function.uncurry H₂) 2 ((timeMeasure t).prod P) := by
  rw [← Lp.edist_def, eDist_eq_eNorm_sub, ← map_sub, LinearIsometry.eNorm_map,
    ← eDist_eq_eNorm_sub, Lp.edist_def,
    eLpNorm_congr_ae ((hH₁.memLp_predictableMeasure t).coeFn_toLp.sub
      (hH₂.memLp_predictableMeasure t).coeFn_toLp),
    ℱ.predictableMeasure_def,
    eLpNorm_trim ℱ.predictable_le_prod (hH₁.isStronglyPredictable.sub hH₂.isStronglyPredictable)]

/-- The `L²(P)` distance between an elementary integral and `hW.l2Integral t` of a
`BrownianIntegrable` integrand equals the time-product `L²` distance between their integrands. -/
theorem eLpNorm_elementaryIntegrand_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (K : ElementaryIntegrand ℱ) {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    eLpNorm (fun ω ↦ K.integral W t ω -
        hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) ω) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ K.toProcess p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure t).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hK := K.brownianIntegrable_toProcess (P := P)
  refine (eLpNorm_congr_ae ((hW.coeFn_l2Integral_elementaryIntegrand K t
    (hK.memLp_predictableMeasure t)).symm.mono fun ω hω ↦ ?_)).trans
    (hW.eLpNorm_l2Integral_sub hK hH t)
  simp only [Pi.sub_apply, hω]

/-- For a `BrownianIntegrable` integrand, every Itô integral agrees almost surely at every time `t`
with the finite-horizon predictable L² Brownian integral `hW.l2Integral t`. Neither Brownian path
continuity nor progressive measurability of `I` is required. -/
theorem ae_eq_l2Integral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hKlim⟩ := exists_seq_elementaryIntegrand_tendsto_eLpNorm (P := P) hH
  obtain ⟨L, hLE, hLI⟩ := hI.exists_approx t
  exact hW.ae_eq_of_tendsto_lintegral_enorm_sq hH.isStronglyPredictable hLE
    (fun _ hε ↦ tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
      (F := fun m s ω ↦ (K m).toProcess s ω - H s ω)
      (fun m ↦ (((K m).isStronglyPredictable_toProcess.sub hH.isStronglyPredictable).mono
        ℱ.predictable_le_prod).measurable) (hKlim t) hε)
    hLI (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      ((hKlim t).congr fun m ↦ (hW.eLpNorm_elementaryIntegrand_sub_l2Integral (K m) hH t).symm))

/-- Any Itô integral of a `BrownianIntegrable` integrand is square integrable at every time. -/
theorem memLp_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) : MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm

/-- Any Itô integral of a `BrownianIntegrable` integrand has expectation zero at every time. -/
theorem integral_eq_zero_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) : ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t)).trans
    (hW.integral_l2Integral t _)

/-- **Bilinear Itô cross-isometry (covariance).** For two `BrownianIntegrable` integrands and
their Itô integrals, the expected product at time `t` equals the time-product integral of the
product of the integrands on `(0, t]`. -/
theorem integral_mul_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H₁ H₂ I₁ I₂ : ℝ≥0 → Ω → ℝ}
    (hH₁ : BrownianIntegrable ℱ P H₁) (hH₂ : BrownianIntegrable ℱ P H₂)
    (hI₁ : IsItoIntegral ℱ P W H₁ I₁) (hI₂ : IsItoIntegral ℱ P W H₂ I₂) (t : ℝ≥0) :
    ∫ ω, I₁ t ω * I₂ t ω ∂P = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂(timeMeasure t).prod P := by
  let f₁ := (hH₁.memLp_predictableMeasure t).toLp (Function.uncurry H₁)
  let f₂ := (hH₂.memLp_predictableMeasure t).toLp (Function.uncurry H₂)
  calc
    ∫ ω, I₁ t ω * I₂ t ω ∂P = ⟪hW.l2Integral t f₁, hW.l2Integral t f₂⟫_ℝ := by
      rw [L2.inner_def]
      refine integral_congr_ae ((hW.ae_eq_l2Integral_of_isItoIntegral hH₁ hI₁ t).mp
        ((hW.ae_eq_l2Integral_of_isItoIntegral hH₂ hI₂ t).mono fun _ h2 h1 ↦ ?_))
      simp only [f₁, f₂, RCLike.inner_apply, conj_trivial, h1, h2, mul_comm]
    _ = ⟪f₁, f₂⟫_ℝ := (hW.l2Integral t).inner_map_map f₁ f₂
    _ = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂ℱ.predictableMeasure P t := by
      rw [L2.inner_def]
      refine integral_congr_ae ((hH₁.memLp_predictableMeasure t).coeFn_toLp.mp
        ((hH₂.memLp_predictableMeasure t).coeFn_toLp.mono fun ⟨_, _⟩ h2 h1 ↦ ?_))
      simp only [f₁, f₂, RCLike.inner_apply, conj_trivial, h1, h2, Function.uncurry_apply_pair,
        mul_comm]
    _ = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂(timeMeasure t).prod P :=
      ℱ.integral_predictableMeasure P (hH₁.isStronglyPredictable.mul hH₂.isStronglyPredictable) t

/-- **Itô isometry** for the second moment of an Itô integral of a `BrownianIntegrable`
integrand. -/
theorem integral_sq_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  simpa only [sq] using hW.integral_mul_of_isItoIntegral hH hH hI hI t

/-- **L²-seminorm Itô isometry.** The `eLpNorm` of an Itô integral at time `t` equals the
time-product `eLpNorm` of its integrand on `(0, t]`. -/
theorem eLpNorm_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    eLpNorm (I t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) := by
  have h := hW.eLpNorm_elementaryIntegrand_sub_l2Integral (ElementaryIntegrand.zero ℱ) hH t
  simp only [ElementaryIntegrand.integral_zero, ElementaryIntegrand.toProcess_zero, zero_sub] at h
  rw [← eLpNorm_neg (I t)]
  exact (eLpNorm_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).neg).trans
    (h.trans (eLpNorm_neg (Function.uncurry H) 2 ((timeMeasure t).prod P)))

/-- **L²-seminorm Itô isometry for differences.** The `L²(P)` distance between two Itô integrals
at time `t` equals the time-product `L²` distance between their integrands on `(0, t]`. -/
theorem eLpNorm_sub_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H₁ H₂ I₁ I₂ : ℝ≥0 → Ω → ℝ}
    (hH₁ : BrownianIntegrable ℱ P H₁) (hH₂ : BrownianIntegrable ℱ P H₂)
    (hI₁ : IsItoIntegral ℱ P W H₁ I₁) (hI₂ : IsItoIntegral ℱ P W H₂ I₂) (t : ℝ≥0) :
    eLpNorm (I₁ t - I₂ t) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ H₁ p.1 p.2 - H₂ p.1 p.2) 2 ((timeMeasure t).prod P) :=
  hW.eLpNorm_of_isItoIntegral (H := fun s ω ↦ H₁ s ω - H₂ s ω)
    ⟨hH₁.isStronglyPredictable.sub hH₂.isStronglyPredictable,
      fun T ↦ (hH₁.memLp T).sub (hH₂.memLp T)⟩ (hI₁.sub hI₂) t

/-- Any strongly adapted Itô integral of a `BrownianIntegrable` integrand is a martingale. -/
theorem martingale_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (hAdap : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hKlim⟩ := exists_seq_elementaryIntegrand_tendsto_eLpNorm (P := P) hH
  refine martingale_of_tendsto_eLpNorm_one (fun m ↦ (K m).martingale_integral hW.martingale)
    hAdap fun t ↦
      TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
  refine (hKlim t).congr fun m ↦ ?_
  rw [← hW.eLpNorm_elementaryIntegrand_sub_l2Integral (K m) hH t]
  exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm)

/-- **Itô isometry and martingale theorem.** Any strongly adapted Itô integral of a
`BrownianIntegrable` integrand is a square-integrable martingale whose second moment at every
time `t` equals the expected square energy of `H` on `(0, t]`. Neither Brownian path continuity
nor usual filtration conditions are required. -/
theorem itoIntegral_isometry (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (hAdap : StronglyAdapted ℱ I) :
    Martingale I ℱ P ∧
      ∀ t : ℝ≥0, ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P :=
  ⟨hW.martingale_of_isItoIntegral hH hI hAdap, hW.integral_sq_of_isItoIntegral hH hI⟩

/-- Internal existence builder exposing an approximating sequence of elementary integrands whose
integrals converge almost surely uniformly on every finite horizon to the constructed continuous
martingale Itô integral. -/
private theorem exists_approx_continuous_martingale_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    ∃ (I : ℝ≥0 → Ω → ℝ) (K : ℕ → ElementaryIntegrand ℱ),
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P ∧
      (∀ t : ℝ≥0, MemLp (I t) 2 P) ∧
      (∀ T : ℝ≥0, Tendsto (fun n ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ (K n).toProcess p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂P, Continuous (I · ω) ∧ ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun n t ↦ (K n).integral W t ω) (I · ω) atTop (Set.Iic T) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨L, hLlim⟩ := exists_seq_elementaryIntegrand_tendsto_eLpNorm (P := P) hH
  have hmem : ∀ m t, MemLp ((L m).integral W t) 2 P := fun m t ↦ (L m).memLp_integral hW t
  have hcau (t : ℝ≥0) : CauchySeq (fun m ↦ (hmem m t).toLp ((L m).integral W t)) := by
    let Z := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))
    refine Tendsto.cauchySeq (x := Z) ?_
    rw [← Lp.toLp_coeFn Z (Lp.memLp Z),
      Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (hmem · t) _ (Lp.memLp Z)]
    exact (hLlim t).congr fun m ↦ (hW.eLpNorm_elementaryIntegrand_sub_l2Integral (L m) hH t).symm
  obtain ⟨I, hImart, hIpred, hIlim, -, φ, hφ, hpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2)
      (fun m ↦ (L m).martingale_integral hW.martingale)
      (fun m ↦ (L m).ae_continuous_integral hcont) hmem hcau
  exact ⟨I, fun n ↦ L (φ n),
    ⟨hH.isStronglyPredictable, hpath.mono fun _ h ↦ h.1, fun t ↦
      ⟨L, fun _ hε ↦ tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
          (F := fun m s ω ↦ (L m).toProcess s ω - H s ω)
          (fun m ↦ (((L m).isStronglyPredictable_toProcess.sub hH.isStronglyPredictable).mono
            ℱ.predictable_le_prod).measurable) (hLlim t) hε,
        tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hIlim t).2⟩⟩,
    hIpred, hImart, fun t ↦ (hIlim t).1, fun T ↦ (hLlim T).comp hφ.tendsto_atTop, hpath⟩

/-- **Existence of the L² Brownian Itô integral process.** For a filtered pre-Brownian motion `W`
with almost surely continuous paths, every `BrownianIntegrable` integrand admits a strongly
predictable, almost surely continuous square-integrable martingale Itô integral. No usual
filtration conditions are required. -/
theorem exists_isItoIntegral_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ,
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Martingale I ℱ P ∧ ∀ t : ℝ≥0, MemLp (I t) 2 P :=
  let ⟨I, _, hIito, hIpred, hImart, hImem, _, _⟩ :=
    hW.exists_approx_continuous_martingale_of_brownianIntegrable hcont hH
  ⟨I, hIito, hIpred, hImart, hImem⟩

/-- Every Itô integral of a `BrownianIntegrable` integrand against an almost surely continuous
filtered pre-Brownian motion is approximated almost surely uniformly on every finite horizon by a
single sequence of elementary integrals whose integrands converge in `L²` on every horizon. -/
theorem exists_seq_elementaryIntegrand_tendstoUniformlyOn
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) :
    ∃ K : ℕ → ElementaryIntegrand ℱ,
      (∀ T : ℝ≥0, Tendsto (fun n ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ (K n).toProcess p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun n t ↦ (K n).integral W t ω) (I · ω) atTop (Set.Iic T) := by
  obtain ⟨I₀, K, hI₀ito, -, -, -, hKlim, hpath⟩ :=
    hW.exists_approx_continuous_martingale_of_brownianIntegrable hcont hH
  refine ⟨K, hKlim, ?_⟩
  filter_upwards [hpath, hW.isItoIntegral_unique hI hI₀ito] with ω hω heq T
  simpa only [show (fun t ↦ I t ω) = fun t ↦ I₀ t ω from funext heq] using hω.2 T

end TauCeti.Probability.IsFilteredPreBrownianReal
