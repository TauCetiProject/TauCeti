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
  have hpred := ℱ.stronglyMeasurable_predictable_indicator_Ioc_mul s t hξ
  rw [ℱ.memLp_predictableMeasure_iff P hpred T 2, MemLp]
  have hm : Measurable (fun p : ℝ≥0 × Ω ↦ ‖(Ioc s t).indicator (fun _ ↦ ξ p.2) p.1‖ₑ ^ 2) :=
    (hpred.mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
  have hsq : eLpNorm (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ p.2) p.1) 2
      ((timeMeasure T).prod P) ^ 2 < ∞ := by
    have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      (hpred.mono ℱ.predictable_le_prod).aestronglyMeasurable (μ := (timeMeasure T).prod P)
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at hpow
    rw [hpow, lintegral_prod _ hm.aemeasurable]
    have hinner (u : ℝ≥0) :
        (∫⁻ ω, ‖(Ioc s t).indicator (fun _ ↦ ξ ω) u‖ₑ ^ 2 ∂P) =
          (Ioc s t).indicator (fun _ ↦ ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P) u := by
      by_cases hu : u ∈ Ioc s t <;> simp [hu]
    simp_rw [hinner, lintegral_indicator measurableSet_Ioc, lintegral_const,
      Measure.restrict_apply_univ]
    have hξfin : ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P < ∞ := by
      have hp := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
        hξ₂.aestronglyMeasurable
      simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at hp
      rw [← hp]
      exact ENNReal.pow_lt_top hξ₂.eLpNorm_lt_top
    exact ENNReal.mul_lt_top hξfin (measure_lt_top _ _)
  exact lt_of_not_ge fun htop ↦ by simp [top_le_iff.mp htop] at hsq

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
  have hmeas : Measurable (fun p : ℝ≥0 × Ω ↦ ‖F n p.1 p.2‖ₑ ^ 2) :=
    (hF n).eNorm.pow_const 2
  have hEmeas : Measurable (fun ω ↦ ∫⁻ s, ‖F n s ω‖ₑ ^ 2 ∂timeMeasure t) :=
    hmeas.lintegral_prod_left'
  have hmarkov : P {ω | δ ≤ ∫⁻ s, ‖F n s ω‖ₑ ^ 2 ∂timeMeasure t} * δ ≤
      ∫⁻ ω, ∫⁻ s, ‖F n s ω‖ₑ ^ 2 ∂timeMeasure t ∂P := by
    rw [mul_comm]
    exact mul_meas_ge_le_lintegral₀ hEmeas.aemeasurable δ
  have htonelli : (∫⁻ ω, ∫⁻ s, ‖F n s ω‖ₑ ^ 2 ∂timeMeasure t ∂P) =
      eLpNorm (Function.uncurry (F n)) 2 ((timeMeasure t).prod P) ^ 2 := by
    rw [← lintegral_lintegral_swap hmeas.aemeasurable, ← lintegral_prod _ hmeas.aemeasurable]
    have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      (hF n).aestronglyMeasurable (μ := (timeMeasure t).prod P)
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at hpow
    exact (lintegral_congr fun ⟨_, _⟩ ↦ rfl).trans hpow.symm
  rw [htonelli] at hmarkov
  have hle := (ENNReal.le_div_iff_mul_le (Or.inl hδpos.ne') (Or.inl hδtop)).2 hmarkov
  rw [ENNReal.div_eq_inv_mul] at hle
  exact (measure_mono fun ω hω ↦ (min_le_left ε 1).trans hω).trans hle

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
    have hTt : T ≤ t := hTs.trans hst
    rw [min_eq_right hTs, min_eq_right hTt, max_eq_left hTs, sub_self, sub_self]

/-- A simple function measurable with respect to `ℱ s` is bounded and hence in `L²(P)`. -/
private theorem memLp_simpleFunc [IsFiniteMeasure P] {s : ℝ≥0}
    (g : @SimpleFunc Ω (ℱ s) ℝ) : MemLp (g : Ω → ℝ) 2 P := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ ω, ‖g ω‖ ≤ C :=
    ⟨(insert (0 : ℝ) ((@SimpleFunc.range Ω ℝ (ℱ s) g).image (fun x ↦ ‖x‖))).sup'
        (Finset.insert_nonempty _ _) id, fun ω ↦
      Finset.le_sup' (f := id)
        (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (@SimpleFunc.mem_range_self Ω ℝ (ℱ s) g ω)))⟩
  have hmeas : StronglyMeasurable[ℱ s] (g : Ω → ℝ) := @SimpleFunc.stronglyMeasurable Ω ℝ (ℱ s) _ g
  exact MemLp.of_bound (hmeas.mono (ℱ.le s)).aestronglyMeasurable C (.of_forall hC)

/-- On an `ℱ s`-measurable simple function height, `l2Integral T` equals the height times the
clipped Brownian increment. -/
private theorem coeFn_l2Integral_indicator_Ioc_simpleFunc
    (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t)
    (g : @SimpleFunc Ω (ℱ s) ℝ) :
    have := (hW.hasLaw_eval 0).isProbabilityMeasure
    let hmem := ℱ.memLp_predictableMeasure_indicator_Ioc_mul (P := P) T s t
      (@SimpleFunc.stronglyMeasurable Ω ℝ (ℱ s) _ g) (memLp_simpleFunc g)
    hW.l2Integral T (hmem.toLp _) =ᵐ[P]
      fun ω ↦ g ω * (W (min t T) ω - W (min s T) ω) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  induction g using @SimpleFunc.induction Ω ℝ (ℱ s) _ with
  | @const c A hA =>
    let gc : @SimpleFunc Ω (ℱ s) ℝ :=
      @SimpleFunc.piecewise Ω ℝ (ℱ s) A hA (@SimpleFunc.const Ω ℝ (ℱ s) c)
        (@SimpleFunc.const Ω ℝ (ℱ s) 0)
    have hmem := ℱ.memLp_predictableMeasure_indicator_Ioc_mul (P := P) T s t
      (@SimpleFunc.stronglyMeasurable Ω ℝ (ℱ s) _ gc) (memLp_simpleFunc gc)
    have heq : hmem.toLp _ =
        indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) c := by
      apply Lp.ext
      filter_upwards [hmem.coeFn_toLp,
        indicatorConstLp_coeFn (p := 2) (c := c)
          (hs := measurableSet_predictable_Ioc_prod s t hA)
          (hμs := measure_ne_top (ℱ.predictableMeasure P T) _)] with p hp₁ hp₂
      rw [hp₁, hp₂]
      by_cases h1 : p.1 ∈ Ioc s t <;> by_cases h2 : p.2 ∈ A <;> simp [gc, h1, h2]
    refine (Lp.ext_iff.mp (congrArg (hW.l2Integral T) heq)).trans ?_
    filter_upwards [hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T s t hA c] with ω hω
    by_cases h2 : ω ∈ A <;> simp [hω, sub_max_min_eq_sub_min hst T ω, h2]
  | @add f₁ f₂ _ hf₁ hf₂ =>
    have hmem₁ := ℱ.memLp_predictableMeasure_indicator_Ioc_mul (P := P) T s t
      (@SimpleFunc.stronglyMeasurable Ω ℝ (ℱ s) _ f₁) (memLp_simpleFunc f₁)
    have hmem₂ := ℱ.memLp_predictableMeasure_indicator_Ioc_mul (P := P) T s t
      (@SimpleFunc.stronglyMeasurable Ω ℝ (ℱ s) _ f₂) (memLp_simpleFunc f₂)
    have hmem₁₂ := ℱ.memLp_predictableMeasure_indicator_Ioc_mul (P := P) T s t
      (@SimpleFunc.stronglyMeasurable Ω ℝ (ℱ s) _ (f₁ + f₂)) (memLp_simpleFunc (f₁ + f₂))
    have hsum : hmem₁₂.toLp _ = hmem₁.toLp _ + hmem₂.toLp _ := by
      apply Lp.ext
      filter_upwards [hmem₁₂.coeFn_toLp, Lp.coeFn_add (hmem₁.toLp _) (hmem₂.toLp _),
        hmem₁.coeFn_toLp, hmem₂.coeFn_toLp] with p hp₁₂ hadd hp₁ hp₂
      rw [hp₁₂, hadd, Pi.add_apply, hp₁, hp₂, FunLike.coe_add, Pi.add_apply]
      by_cases hp : p.1 ∈ Ioc s t <;> simp [hp]
    have hmap := congrArg (hW.l2Integral T) hsum
    rw [map_add] at hmap
    filter_upwards [Lp.ext_iff.mp hmap,
      Lp.coeFn_add (hW.l2Integral T (hmem₁.toLp _)) (hW.l2Integral T (hmem₂.toLp _)),
      hf₁, hf₂] with ω hω hadd h₁ h₂
    rw [hω, hadd, Pi.add_apply, h₁, h₂, FunLike.coe_add, Pi.add_apply, add_mul]

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
  let X : Lp ℝ 2 P := hW.l2Integral T (hmem.toLp _)
  have hYmem : MemLp (fun ω ↦ ξ ω * (W (max s (min t T)) ω - W s ω)) 2 P :=
    hW.memLp_mul_sub (le_max_left s (min t T)) hξ hξ₂
  let Y : Lp ℝ 2 P := hYmem.toLp _
  suffices hXY : X = Y by
    filter_upwards [Lp.ext_iff.mp hXY, hYmem.coeFn_toLp] with ω h1 h2
    rw [h1, h2, sub_max_min_eq_sub_min hst T ω]
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  have hξ_trim_lt : eLpNorm ξ 2 (P.trim (ℱ.le s)) < ∞ := by
    rw [eLpNorm_trim (ℱ.le s) hξ]
    exact hξ₂.eLpNorm_lt_top
  let M : ℝ := √((T : ℝ) + 1) + √((max s (min t T) - s : ℝ≥0) : ℝ) + 1
  have hMpos : 0 < M := by positivity
  have hδpos : 0 < ε / M := div_pos hε hMpos
  have happrox : ∃ g : @SimpleFunc Ω (ℱ s) ℝ,
      eLpNorm (ξ - ⇑g) 2 (P.trim (ℱ.le s)) < ENNReal.ofReal (ε / M) := by
    let μs : @Measure Ω (ℱ s) := P.trim (ℱ.le s)
    let : MeasurableSpace Ω := ℱ s
    obtain ⟨g, hg_lt, -⟩ :=
      MemLp.exists_simpleFunc_eLpNorm_sub_lt (μ := μs) hξ_trim_lt (by norm_num)
        (ENNReal.ofReal_pos.mpr hδpos).ne'
    exact ⟨g, hg_lt⟩
  obtain ⟨g, hg_lt⟩ := happrox
  have hg_meas : StronglyMeasurable[ℱ s] (g : Ω → ℝ) :=
    @SimpleFunc.stronglyMeasurable Ω ℝ (ℱ s) _ g
  have hg_mem : MemLp (g : Ω → ℝ) 2 P := memLp_simpleFunc g
  have hdiff_meas : StronglyMeasurable[ℱ s] (ξ - (g : Ω → ℝ)) := hξ.sub hg_meas
  have hdiff_mem : MemLp (ξ - (g : Ω → ℝ)) 2 P := hξ₂.sub hg_mem
  have hdiff_norm : ‖hdiff_mem.toLp _‖ ≤ ε / M := by
    rw [Lp.norm_toLp, ← eLpNorm_trim (ℱ.le s) hdiff_meas]
    exact ENNReal.toReal_le_of_le_ofReal hδpos.le hg_lt.le
  have hg_prod : MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ g p.2) p.1) 2
      (ℱ.predictableMeasure P T) :=
    ℱ.memLp_predictableMeasure_indicator_Ioc_mul T s t hg_meas hg_mem
  have hXg_eq : hW.l2Integral T (hg_prod.toLp _) =
      (hW.memLp_mul_sub (le_max_left s (min t T)) hg_meas hg_mem).toLp _ := by
    apply Lp.ext
    filter_upwards [hW.coeFn_l2Integral_indicator_Ioc_simpleFunc T hst g,
      (hW.memLp_mul_sub (le_max_left s (min t T)) hg_meas hg_mem).coeFn_toLp] with ω h1 h2
    rw [h1, h2, sub_max_min_eq_sub_min hst T ω]
  have hdistX : dist X (hW.l2Integral T (hg_prod.toLp _)) ≤
      √((T : ℝ) + 1) * ‖hdiff_mem.toLp _‖ := by
    rw [dist_eq_norm, ← map_sub, LinearIsometry.norm_map]
    have hsub_eq : hmem.toLp _ - hg_prod.toLp _ =
        (ℱ.memLp_predictableMeasure_indicator_Ioc_mul T s t hdiff_meas hdiff_mem).toLp _ := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (hmem.toLp _) (hg_prod.toLp _), hmem.coeFn_toLp,
        hg_prod.coeFn_toLp,
        (ℱ.memLp_predictableMeasure_indicator_Ioc_mul T s t hdiff_meas hdiff_mem).coeFn_toLp]
        with p hsub h1 h2 h3
      rw [hsub, Pi.sub_apply, h1, h2, h3, Pi.sub_apply]
      by_cases hp : p.1 ∈ Ioc s t <;> simp [hp]
    rw [hsub_eq, ← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg (hdiff_mem.toLp _)),
      ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have hpred := ℱ.stronglyMeasurable_predictable_indicator_Ioc_mul s t hdiff_meas
    have hnormsq : ‖(ℱ.memLp_predictableMeasure_indicator_Ioc_mul T s t
        hdiff_meas hdiff_mem).toLp _‖ ^ 2 =
        ∫ p, ((Ioc s t).indicator (fun _ ↦ (ξ - g) p.2) p.1) ^ 2 ∂(timeMeasure T).prod P := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      have hae :=
        (ℱ.memLp_predictableMeasure_indicator_Ioc_mul T s t hdiff_meas hdiff_mem).coeFn_toLp
      refine (integral_congr_ae (hae.mono fun p hp ↦ ?_)).trans
        (ℱ.integral_predictableMeasure P (hpred.pow 2) T)
      simp only [RCLike.inner_apply, conj_trivial, hp, ← sq, Pi.pow_apply]
    have hξnormsq : ‖hdiff_mem.toLp _‖ ^ 2 = ∫ ω, (ξ ω - g ω) ^ 2 ∂P := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      exact integral_congr_ae (hdiff_mem.coeFn_toLp.mono fun ω hω ↦ by
        simp only [RCLike.inner_apply, conj_trivial, hω, Pi.sub_apply, ← sq])
    rw [hnormsq, hξnormsq]
    have hint_prod : Integrable
        (fun p : ℝ≥0 × Ω ↦ ((Ioc s t).indicator (fun _ ↦ (ξ - g) p.2) p.1) ^ 2)
        ((timeMeasure T).prod P) := by
      have hm2 := (ℱ.memLp_predictableMeasure_iff P hpred T 2).mp
        (ℱ.memLp_predictableMeasure_indicator_Ioc_mul T s t hdiff_meas hdiff_mem)
      convert hm2.integrable_mul hm2 using 1
      ext p
      exact sq _
    rw [integral_prod _ hint_prod]
    have hinner (u : ℝ≥0) :
        (∫ ω, ((Ioc s t).indicator (fun _ ↦ (ξ - g) ω) u) ^ 2 ∂P) =
          (Ioc s t).indicator (fun _ ↦ ∫ ω, (ξ ω - g ω) ^ 2 ∂P) u := by
      by_cases hu : u ∈ Ioc s t <;> simp [hu]
    simp_rw [hinner, integral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ ↦ sq_nonneg _)
    have hle : (timeMeasure T).real (Ioc s t) ≤ (T : ℝ) := by
      rw [measureReal_def, timeMeasure_Ioc, ENNReal.toReal_ofReal']
      have hmt : ((min t T : ℝ≥0) : ℝ) ≤ T := NNReal.coe_le_coe.mpr (min_le_right t T)
      have hs0 : (0 : ℝ) ≤ s := NNReal.coe_nonneg s
      exact max_le (by linarith) (NNReal.coe_nonneg T)
    linarith
  have hdistY : dist (hW.l2Integral T (hg_prod.toLp _)) Y ≤
      √((max s (min t T) - s : ℝ≥0) : ℝ) * ‖hdiff_mem.toLp _‖ := by
    rw [hXg_eq, dist_comm, dist_eq_norm]
    have hsub_eq : Y - (hW.memLp_mul_sub (le_max_left s (min t T)) hg_meas hg_mem).toLp _ =
        (hW.memLp_mul_sub (le_max_left s (min t T)) hdiff_meas hdiff_mem).toLp _ := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub Y _, hYmem.coeFn_toLp,
        (hW.memLp_mul_sub (le_max_left s (min t T)) hg_meas hg_mem).coeFn_toLp,
        (hW.memLp_mul_sub (le_max_left s (min t T)) hdiff_meas hdiff_mem).coeFn_toLp]
        with ω hsub h1 h2 h3
      rw [hsub, Pi.sub_apply, h1, h2, h3, Pi.sub_apply, sub_mul]
    rw [hsub_eq, ← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg (hdiff_mem.toLp _)),
      ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    have hinner_eq :
        ∫ ω, ⟪(hW.memLp_mul_sub (le_max_left s (min t T)) hdiff_meas hdiff_mem).toLp _ ω,
          (hW.memLp_mul_sub (le_max_left s (min t T)) hdiff_meas hdiff_mem).toLp _ ω⟫_ℝ ∂P =
          ∫ ω, ((ξ - g) ω * (W (max s (min t T)) ω - W s ω)) *
            ((ξ - g) ω * (W (max s (min t T)) ω - W s ω)) ∂P :=
      integral_congr_ae
        ((hW.memLp_mul_sub (le_max_left s (min t T)) hdiff_meas hdiff_mem).coeFn_toLp.mono
          fun ω hω ↦ by simp only [RCLike.inner_apply, conj_trivial, hω])
    rw [hinner_eq,
      hW.integral_mul_sub_mul_mul_sub (le_max_left s (min t T)) (le_max_left s (min t T))
        hdiff_meas hdiff_meas hdiff_mem hdiff_mem, min_self, max_self, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact le_of_eq (integral_congr_ae (hdiff_mem.coeFn_toLp.mono fun ω hω ↦ by
      simp only [RCLike.inner_apply, conj_trivial, hω]))
  calc
    dist X Y ≤ dist X (hW.l2Integral T (hg_prod.toLp _)) +
        dist (hW.l2Integral T (hg_prod.toLp _)) Y := dist_triangle _ _ _
    _ ≤ √((T : ℝ) + 1) * ‖hdiff_mem.toLp _‖ +
        √((max s (min t T) - s : ℝ≥0) : ℝ) * ‖hdiff_mem.toLp _‖ := add_le_add hdistX hdistY
    _ ≤ M * ‖hdiff_mem.toLp _‖ := by
      have hle : √((T : ℝ) + 1) + √((max s (min t T) - s : ℝ≥0) : ℝ) ≤ M := by
        simp only [M]; linarith
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ ≤ M * (ε / M) := mul_le_mul_of_nonneg_left hdiff_norm hMpos.le
    _ = ε := mul_div_cancel₀ ε hMpos.ne'

/-- On any elementary integrand `K`, the finite-horizon predictable L² Brownian integral agrees
almost surely with the elementary integral `K.integral W T`. -/
theorem coeFn_l2Integral_elementaryIntegrand (hW : IsFilteredPreBrownianReal ℱ W P)
    (K : ElementaryIntegrand ℱ) (T : ℝ≥0)
    (hmem : MemLp (Function.uncurry K.toProcess) 2 (ℱ.predictableMeasure P T)) :
    hW.l2Integral T (hmem.toLp (Function.uncurry K.toProcess)) =ᵐ[P] K.integral W T := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hξ₂ (i : Fin K.n) : MemLp (K.ξ i) 2 P := by
    obtain ⟨C, hC⟩ := K.bounded i
    exact MemLp.of_bound ((K.stronglyMeasurable i).mono (ℱ.le _)).aestronglyMeasurable
      C (.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hC ω)
  have hterm (i : Fin K.n) := ℱ.memLp_predictableMeasure_indicator_Ioc_mul (P := P) T
    (K.s i.castSucc) (K.s i.succ) (K.stronglyMeasurable i) (hξ₂ i)
  have hsum : hmem.toLp (Function.uncurry K.toProcess) =
      ∑ i : Fin K.n, (hterm i).toLp _ := by
    apply Lp.ext
    have hcoe : (∑ i : Fin K.n, (hterm i).toLp _) =ᵐ[ℱ.predictableMeasure P T]
        fun p ↦ ∑ i : Fin K.n,
          (Ioc (K.s i.castSucc) (K.s i.succ)).indicator (fun _ ↦ K.ξ i p.2) p.1 := by
      have hall : ∀ᵐ p ∂ℱ.predictableMeasure P T, ∀ i : Fin K.n,
          ((hterm i).toLp _) p =
            (Ioc (K.s i.castSucc) (K.s i.succ)).indicator (fun _ ↦ K.ξ i p.2) p.1 :=
        ae_all_iff.mpr fun i ↦ (hterm i).coeFn_toLp
      filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin K.n ↦ (hterm i).toLp _),
        hall] with p h1 h2
      rw [h1, Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ ↦ h2 i
    filter_upwards [hmem.coeFn_toLp, hcoe] with p h1 h2
    rw [h1, h2]
    exact K.toProcess_def p.1 p.2
  have hmap := congrArg (hW.l2Integral T) hsum
  rw [map_sum] at hmap
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin K.n,
      (hW.l2Integral T ((hterm i).toLp _)) ω =
        K.ξ i ω * (W (min (K.s i.succ) T) ω - W (min (K.s i.castSucc) T) ω) :=
    ae_all_iff.mpr fun i ↦
      hW.coeFn_l2Integral_indicator_Ioc_mul T (K.mono i.castSucc_le_succ)
        (K.stronglyMeasurable i) (hξ₂ i) (hterm i)
  filter_upwards [Lp.ext_iff.mp hmap,
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin K.n ↦ hW.l2Integral T ((hterm i).toLp _)),
    hall] with ω h1 h2 h3
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
    (fun j hj ↦ ⟨C m, fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩), fun T ↦ ?_⟩
  simpa only [ElementaryIntegrand.toProcess_ofSimple] using hlim T

/-- Helper: `L²(P)` distance between an elementary integral and `hW.l2Integral t` of a
`BrownianIntegrable` integrand equals the time-product `L²` distance between their integrands. -/
private theorem eLpNorm_elementaryIntegrand_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (K : ElementaryIntegrand ℱ) {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    eLpNorm (fun ω ↦ K.integral W t ω -
        hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) ω) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ K.toProcess p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure t).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hKm := (K.brownianIntegrable_toProcess (P := P)).memLp_predictableMeasure t
  have hKae := hW.coeFn_l2Integral_elementaryIntegrand K t hKm
  have hsub : (fun ω ↦ K.integral W t ω -
      hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) ω) =ᵐ[P]
      (hW.l2Integral t (hKm.toLp (Function.uncurry K.toProcess)) -
        hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) : Ω → ℝ) :=
    hKae.symm.sub EventuallyEq.rfl
  rw [eLpNorm_congr_ae hsub, ← Lp.edist_def, eDist_eq_eNorm_sub, ← map_sub,
    LinearIsometry.eNorm_map, ← eDist_eq_eNorm_sub, Lp.edist_def]
  have hpred : StronglyMeasurable[ℱ.predictable]
      (Function.uncurry K.toProcess - Function.uncurry H) :=
    K.isStronglyPredictable_toProcess.sub hH.isStronglyPredictable
  rw [eLpNorm_congr_ae (hKm.coeFn_toLp.sub (hH.memLp_predictableMeasure t).coeFn_toLp),
    ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hpred]
  rfl

/-- For a `BrownianIntegrable` integrand, every Itô integral agrees almost surely at every time `t`
with the finite-horizon predictable L² Brownian integral `hW.l2Integral t`. Neither Brownian path
continuity nor progressive measurability of `I` is required. -/
theorem ae_eq_l2Integral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hKlim⟩ := exists_seq_elementaryIntegrand_tendsto_eLpNorm (P := P) hH
  have hKE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖(K m).toProcess s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) :=
    fun _ hε ↦ tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
      (F := fun m s ω ↦ (K m).toProcess s ω - H s ω)
      (fun m ↦ (((K m).isStronglyPredictable_toProcess.sub hH.isStronglyPredictable).mono
        ℱ.predictable_le_prod).measurable) (hKlim t) hε
  let Z : Ω → ℝ := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))
  have hK_L2 : Tendsto (fun m ↦ eLpNorm (fun ω ↦ (K m).integral W t ω - Z ω) 2 P)
      atTop (𝓝 0) := by
    simp_rw [Z, hW.eLpNorm_elementaryIntegrand_sub_l2Integral _ hH t]
    exact hKlim t
  have hKmeas : TendstoInMeasure P (fun m ↦ (K m).integral W t) atTop Z :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hK_L2
  obtain ⟨L, hLE, hLI⟩ := hI.exists_approx t
  exact hW.ae_eq_of_tendsto_lintegral_enorm_sq hH.isStronglyPredictable hLE hKE hLI hKmeas

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
  have h1 := hW.ae_eq_l2Integral_of_isItoIntegral hH₁ hI₁ t
  have h2 := hW.ae_eq_l2Integral_of_isItoIntegral hH₂ hI₂ t
  calc
    ∫ ω, I₁ t ω * I₂ t ω ∂P
        = ∫ ω, hW.l2Integral t f₂ ω * hW.l2Integral t f₁ ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [h1, h2] with ω hω₁ hω₂
          rw [hω₁, hω₂, mul_comm]
    _ = ⟪hW.l2Integral t f₁, hW.l2Integral t f₂⟫_ℝ := by
          rw [L2.inner_def]
          simp_rw [RCLike.inner_apply, conj_trivial]
    _ = ⟪f₁, f₂⟫_ℝ := (hW.l2Integral t).inner_map_map f₁ f₂
    _ = ∫ p, f₂ p * f₁ p ∂ℱ.predictableMeasure P t := by
          rw [L2.inner_def]
          simp_rw [RCLike.inner_apply, conj_trivial]
    _ = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂ℱ.predictableMeasure P t := by
          refine integral_congr_ae ?_
          filter_upwards [(hH₁.memLp_predictableMeasure t).coeFn_toLp,
            (hH₂.memLp_predictableMeasure t).coeFn_toLp] with p hp₁ hp₂
          rw [hp₁, hp₂, Function.uncurry_apply_pair, Function.uncurry_apply_pair, mul_comm]
    _ = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂(timeMeasure t).prod P :=
          ℱ.integral_predictableMeasure P
            (hH₁.isStronglyPredictable.mul hH₂.isStronglyPredictable) t

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
      eLpNorm (fun p : ℝ≥0 × Ω ↦ H₁ p.1 p.2 - H₂ p.1 p.2) 2 ((timeMeasure t).prod P) := by
  have hH : BrownianIntegrable ℱ P (fun s ω ↦ H₁ s ω - H₂ s ω) :=
    ⟨hH₁.isStronglyPredictable.sub hH₂.isStronglyPredictable,
      fun T ↦ (hH₁.memLp T).sub (hH₂.memLp T)⟩
  exact hW.eLpNorm_of_isItoIntegral hH (hI₁.sub hI₂) t

/-- Any strongly adapted Itô integral of a `BrownianIntegrable` integrand is a martingale. -/
theorem martingale_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (hAdap : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hKlim⟩ := exists_seq_elementaryIntegrand_tendsto_eLpNorm (P := P) hH
  refine martingale_of_tendsto_eLpNorm_one (fun m ↦ (K m).martingale_integral hW.martingale)
    hAdap fun t ↦ ?_
  have h2 : Tendsto (fun m ↦ eLpNorm ((K m).integral W t - I t) 2 P) atTop (𝓝 0) := by
    have heq (m : ℕ) : eLpNorm ((K m).integral W t - I t) 2 P =
        eLpNorm (fun p : ℝ≥0 × Ω ↦ (K m).toProcess p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure t).prod P) := by
      have hIae := hW.ae_eq_l2Integral_of_isItoIntegral hH hI t
      rw [eLpNorm_congr_ae (EventuallyEq.rfl.sub hIae)]
      exact hW.eLpNorm_elementaryIntegrand_sub_l2Integral (K m) hH t
    simp_rw [heq]
    exact hKlim t
  exact TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm (by norm_num) h2

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
  have hM : ∀ m, Martingale ((L m).integral W) ℱ P :=
    fun m ↦ (L m).martingale_integral hW.martingale
  have hc : ∀ m, ∀ᵐ ω ∂P, Continuous (fun t ↦ (L m).integral W t ω) :=
    fun m ↦ (L m).ae_continuous_integral hcont
  have hmem : ∀ m t, MemLp ((L m).integral W t) 2 P :=
    fun m t ↦ (L m).memLp_integral hW t
  have hcau : ∀ t, CauchySeq (fun m ↦ (hmem m t).toLp ((L m).integral W t)) := by
    intro t
    refine Tendsto.cauchySeq
      (x := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) ?_
    have hL2 : Tendsto (fun m ↦
        ((L m).brownianIntegrable_toProcess (P := P) |>.memLp_predictableMeasure t).toLp
          (Function.uncurry (L m).toProcess)) atTop
        (𝓝 ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) := by
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
        (fun m ↦ ((L m).brownianIntegrable_toProcess (P := P)).memLp_predictableMeasure t)
        _ (hH.memLp_predictableMeasure t)]
      have heq (m : ℕ) : eLpNorm (Function.uncurry (L m).toProcess - Function.uncurry H) 2
          (ℱ.predictableMeasure P t) =
          eLpNorm (fun p : ℝ≥0 × Ω ↦ (L m).toProcess p.1 p.2 - H p.1 p.2) 2
            ((timeMeasure t).prod P) := by
        have hpred : StronglyMeasurable[ℱ.predictable]
            (Function.uncurry (L m).toProcess - Function.uncurry H) :=
          (L m).isStronglyPredictable_toProcess.sub hH.isStronglyPredictable
        rw [ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hpred]
        rfl
      simp_rw [heq]
      exact hLlim t
    have hmap := ((hW.l2Integral t).continuous.tendsto _).comp hL2
    refine hmap.congr fun m ↦ ?_
    apply Lp.ext
    exact (hW.coeFn_l2Integral_elementaryIntegrand (L m) t _).trans (hmem m t).coeFn_toLp.symm
  obtain ⟨I, hImart, hIpred, hIlim, -, φ, hφ, hpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2) hM hc hmem hcau
  have hIito : IsItoIntegral ℱ P W H I :=
    ⟨hH.isStronglyPredictable, hpath.mono fun _ h ↦ h.1, fun t ↦
      ⟨L, fun _ hε ↦ tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
          (F := fun m s ω ↦ (L m).toProcess s ω - H s ω)
          (fun m ↦ (((L m).isStronglyPredictable_toProcess.sub hH.isStronglyPredictable).mono
            ℱ.predictable_le_prod).measurable) (hLlim t) hε,
        tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hIlim t).2⟩⟩
  exact ⟨I, fun n ↦ L (φ n), hIito, hIpred, hImart, fun t ↦ (hIlim t).1,
    fun T ↦ (hLlim T).comp hφ.tendsto_atTop, hpath⟩

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
      Martingale I ℱ P ∧ ∀ t : ℝ≥0, MemLp (I t) 2 P := by
  obtain ⟨I, -, hIito, hIpred, hImart, hImem, -, -⟩ :=
    hW.exists_approx_continuous_martingale_of_brownianIntegrable hcont hH
  exact ⟨I, hIito, hIpred, hImart, hImem⟩

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
  have hII₀ : I ≡ᵐ[P] I₀ := hW.isItoIntegral_unique hI hI₀ito
  refine ⟨K, hKlim, ?_⟩
  filter_upwards [hpath, hII₀] with ω hω heq T
  have hfun : (fun t ↦ I t ω) = fun t ↦ I₀ t ω := funext heq
  simpa only [hfun] using hω.2 T

end TauCeti.Probability.IsFilteredPreBrownianReal
