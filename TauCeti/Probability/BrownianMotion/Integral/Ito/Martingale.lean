/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Integral.Wiener
import Mathlib.Topology.Sequences
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.BrownianMotion.Integral.Deterministic
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.Finance.SimpleStrategy.Approximation

/-!
# The square-integrable Itô integral process and Itô's covariance

Where `MemLp (Function.uncurry H) 2 ((Probability.timeMeasure t).prod P)`, this file identifies
`TauCeti.Probability.IsItoIntegral` almost surely with `IsFilteredPreBrownianReal.l2Integral`
(`ae_eq_l2Integral`) and deduces zero expectation (`integral_eq_zero`), covariance
(`integral_mul`), increment Itô isometry (`integral_sub_sq_of_memLp`), finite-horizon `L²(P)`
continuity (`continuous_toLp`), and for deterministic `L²` integrands identification with
`wienerIntegral` (`ae_eq_wienerIntegral`) and its centered Gaussian law (`hasLaw_gaussianReal`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., 1991, §3.2.B–C.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ}

namespace Probability.IsItoIntegral

/-- Against a filtered pre-Brownian motion, every Itô integral of an integrand with finite expected
square energy on `(0, t]` agrees almost surely at `t` with `hW.l2Integral t`. -/
theorem ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    I t =ᵐ[P] hW.l2Integral t
      (((ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH).toLp
        (Function.uncurry H)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  choose n τ a C _ hτ ha hb herr using fun m : ℕ ↦
    ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t hI.isStronglyPredictable hH
      (ε := (m : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m))
  have hhold := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le) fun m ↦ (herr m).le
  exact tendstoInMeasure_ae_unique
    (hI.tendstoInMeasure_simpleGains hW (fun m ↦ (hτ m).monotoneOn) ha fun _ hε ↦
      TauCeti.tendsto_measure_lintegral_enorm_pow_of_tendsto_eLpNorm two_ne_zero hhold hε)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (hW.tendsto_eLpNorm_simpleGains_l2Integral hI.isStronglyPredictable hH
        (fun m ↦ (hτ m).monotoneOn) ha
        (fun m j hj ↦ .of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
          (.of_forall (hb m j hj))) hhold))

/-- Against a filtered pre-Brownian motion, every Itô integral of a deterministic `L²` integrand
`u` agrees almost surely at horizon `t` with `hW.toIsPreBrownianReal.wienerIntegral`. -/
theorem ae_eq_wienerIntegral (hW : IsFilteredPreBrownianReal ℱ W P) {u : ℝ≥0 → ℝ}
    (hI : IsItoIntegral ℱ P W (fun s _ ↦ u s) I) {t : ℝ≥0}
    (hu : MemLp u 2 (timeMeasure t)) :
    I t =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral t (hu.toLp u) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have h := hI.ae_eq_l2Integral hW (hu.comp_measurePreserving measurePreserving_fst)
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  rwa [← hW.l2Integral_compMeasurePreserving_fst t (hu.toLp u),
    Lp.toLp_compMeasurePreserving hu (ℱ.measurePreserving_fst_predictableMeasure P t)]

/-- Against a filtered pre-Brownian motion, every Itô integral of a deterministic `L²` integrand
`u` is centered Gaussian at horizon `t` with variance `∫ s, u s ^ 2 ∂Probability.timeMeasure t`. -/
theorem hasLaw_gaussianReal (hW : IsFilteredPreBrownianReal ℱ W P) {u : ℝ≥0 → ℝ}
    (hI : IsItoIntegral ℱ P W (fun s _ ↦ u s) I) {t : ℝ≥0}
    (hu : MemLp u 2 (timeMeasure t)) :
    HasLaw (I t) (gaussianReal 0 (Real.toNNReal (∫ s, u s ^ 2 ∂timeMeasure t))) P := by
  have hvar : ‖hu.toLp u‖₊ ^ 2 = Real.toNNReal (∫ s, u s ^ 2 ∂timeMeasure t) :=
    NNReal.eq <| by
      simpa only [NNReal.coe_pow, coe_nnNorm, Real.norm_eq_abs, sq_abs, hu.norm_toLp_sq] using
        (Real.coe_toNNReal _ (integral_nonneg fun _ ↦ sq_nonneg _)).symm
  exact hvar ▸ (hW.toIsPreBrownianReal.hasLaw_wienerIntegral t (hu.toLp u)).congr
    (hI.ae_eq_wienerIntegral hW hu)

/-- Every Itô integral against `W` with finite expected square energy on `(0, t]` has zero mean. -/
theorem integral_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) : ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH)).trans (hW.integral_l2Integral t _)

/-- **Itô's covariance identity.** Against a filtered pre-Brownian motion, the inner product of two
Itô integrals at horizon `t` with finite expected square energy on `(0, t]` equals the time-product
integral of `H * K` on `(0, t] × Ω`. -/
theorem integral_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P))
    (hK : MemLp (Function.uncurry K) 2 ((timeMeasure t).prod P)) :
    ∫ ω, I t ω * J t ω ∂P =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure t).prod P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hHp := (ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH
  let hKp := (ℱ.memLp_predictableMeasure_iff P hJ.isStronglyPredictable t 2).2 hK
  have hlhs : ∫ ω, I t ω * J t ω ∂P =
      ⟪hW.l2Integral t (hHp.toLp _), hW.l2Integral t (hKp.toLp _)⟫_ℝ :=
    (integral_congr_ae <| (hI.ae_eq_l2Integral hW hH).mp <| (hJ.ae_eq_l2Integral hW hK).mono
      fun _ h₂ h₁ ↦ by simp [h₁, h₂, mul_comm]).trans (L2.inner_def _ _).symm
  rw [hlhs, (hW.l2Integral t).inner_map_map, L2.inner_def]
  exact (integral_congr_ae <| hHp.coeFn_toLp.mp <|
    hKp.coeFn_toLp.mono fun _ h₂ h₁ ↦ by simp [h₁, h₂, Function.uncurry, mul_comm]).trans
    (ℱ.integral_predictableMeasure P (hI.isStronglyPredictable.mul hJ.isStronglyPredictable) t)

/-- **Itô's increment `L²` isometry.** For `s ≤ t`, the expected squared increment
`E[(I_t - I_s)²]` equals the expected square energy of `H` over `(s, t] × Ω`. -/
theorem integral_sub_sq_of_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t)
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    ∫ ω, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p in Ioc s t ×ˢ Set.univ, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  have hcut : IsItoIntegral ℱ P W (fun u ω ↦ if s < u then H u ω else 0)
      (fun u ω ↦ I u ω - I (min s u) ω) := by
    simpa only [one_mul] using hI.ite_lt_mul hW s (ξ := fun _ ↦ 1) stronglyMeasurable_const
  have hH_mem : MemLp (Function.uncurry (fun u ω ↦ if s < u then H u ω else 0)) 2
      ((timeMeasure t).prod P) := by
    refine hH.mono (hcut.isStronglyPredictable.mono ℱ.predictable_le_prod).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ ?_)
    dsimp only [Function.uncurry]
    split_ifs <;> simp
  have hsq := hcut.integral_sq hW hH_mem
  simp only [min_eq_left hst] at hsq
  rw [hsq, ← integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
  refine integral_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae (ae_mem_Ioc_timeMeasure t)]
    with p hp
  by_cases hs : s < p.1
  · simp [hs, hp.2]
  · simp [hs]

/-- **Finite-horizon `L²(P)` continuity of the Itô integral.** When `H` has finite expected square
energy on `(0, T]`, the map taking `t ∈ [0, T]` to the `L²(P)` class of `I t` is continuous. -/
theorem continuous_toLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {T : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure T).prod P)) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    Continuous (fun t : Iic T ↦
      (hI.memLp hW (hH.mono_measure
        (Measure.prod_mono (timeMeasure_mono t.property) le_rfl))).toLp (I t)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let mem (t : Iic T) : MemLp (I t) 2 P :=
    hI.memLp hW (hH.mono_measure (Measure.prod_mono (timeMeasure_mono t.property) le_rfl))
  rw [continuous_iff_seqContinuous]
  intro u t hu
  rw [tendsto_iff_edist_tendsto_0]
  have hmem_sq : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2) ((timeMeasure T).prod P) := by
    simpa only [Function.uncurry_def, Real.norm_eq_abs, sq_abs] using hH.integrable_sq
  -- Control `∫ (I (u n) - I t)^2` via the increment isometry on `(min (u n) t, max (u n) t]`.
  have hsub_sq (n : ℕ) : ∫ ω, (I (u n) ω - I t ω) ^ 2 ∂P =
      ∫ p, (Ioc (min (u n).val t.val) (max (u n).val t.val) ×ˢ Set.univ).indicator
        (fun p ↦ H p.1 p.2 ^ 2) p ∂(timeMeasure T).prod P := by
    have hmax_le : max (u n).val t.val ≤ T := max_le (u n).property t.property
    have hH_max : MemLp (Function.uncurry H) 2 ((timeMeasure (max (u n).val t.val)).prod P) :=
      hH.mono_measure (Measure.prod_mono (timeMeasure_mono hmax_le) le_rfl)
    have hinc := hI.integral_sub_sq_of_memLp hW (min_le_max : min (u n).val t.val ≤ _) hH_max
    have heq_lhs : ∫ ω, (I (u n) ω - I t ω) ^ 2 ∂P =
        ∫ ω, (I (max (u n).val t.val) ω - I (min (u n).val t.val) ω) ^ 2 ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
      rcases le_total (u n).val t.val with hle | hle
      · dsimp only
        rw [max_eq_right hle, min_eq_left hle, sub_sq_comm]
      · dsimp only
        rw [max_eq_left hle, min_eq_right hle]
    have hprod_res : (timeMeasure (max (u n).val t.val)).prod P =
        ((timeMeasure T).prod P).restrict (Ioc 0 (max (u n).val t.val) ×ˢ Set.univ) := by
      rw [← timeMeasure_restrict_of_le hmax_le, Measure.restrict_prod_eq_prod_univ]
    have hinter : (Ioc (min (u n).val t.val) (max (u n).val t.val) ×ˢ (Set.univ : Set Ω)) ∩
        (Ioc 0 (max (u n).val t.val) ×ˢ Set.univ) =
        Ioc (min (u n).val t.val) (max (u n).val t.val) ×ˢ Set.univ := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true,
        and_iff_left_iff_imp]
      exact fun h ↦ ⟨bot_le.trans_lt h.1, h.2⟩
    rw [heq_lhs, hinc, hprod_res,
      Measure.restrict_restrict (measurableSet_Ioc.prod MeasurableSet.univ), hinter,
      ← integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
  have hsingle : timeMeasure T {t.val} = 0 := by
    rw [timeMeasure_apply T (measurableSet_singleton t.val)]
    exact measure_mono_null (fun x ⟨y, hy, hyx⟩ ↦ hyx ▸ congrArg ((↑) : ℝ≥0 → ℝ) hy.1)
      Real.volume_singleton
  have hprod_null : ((timeMeasure T).prod P) ({t.val} ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod, hsingle, zero_mul]
  have hlim_int : Tendsto (fun n ↦ ∫ ω, (I (u n) ω - I t ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simp_rw [hsub_sq]
    have hbound : ∀ n, ∀ᵐ p ∂(timeMeasure T).prod P,
        ‖(Ioc (min (u n).val t.val) (max (u n).val t.val) ×ˢ Set.univ).indicator
          (fun p ↦ H p.1 p.2 ^ 2) p‖ ≤ H p.1 p.2 ^ 2 := by
      intro n
      refine Eventually.of_forall fun p ↦ ?_
      by_cases hp : p ∈ Ioc (min (u n).val t.val) (max (u n).val t.val) ×ˢ Set.univ
      · simp [hp]
      · simp [hp, sq_nonneg]
    have hpt : ∀ᵐ p ∂(timeMeasure T).prod P, Tendsto (fun n ↦
        (Ioc (min (u n).val t.val) (max (u n).val t.val) ×ˢ Set.univ).indicator
          (fun p ↦ H p.1 p.2 ^ 2) p) atTop (𝓝 0) := by
      have hae : ∀ᵐ p : ℝ≥0 × Ω ∂(timeMeasure T).prod P, p.1 ≠ t.val := by
        simpa [ae_iff, Set.prod_univ, Set.preimage] using hprod_null
      have hu_coe : Tendsto (fun n ↦ (u n).val) atTop (𝓝 t.val) :=
        continuous_subtypeVal.continuousAt.tendsto.comp hu
      filter_upwards [hae] with p hp
      apply tendsto_const_nhds.congr'
      rcases lt_or_gt_of_ne hp with hlt | hgt
      · filter_upwards [hu_coe.eventually (eventually_gt_nhds hlt)] with n hn
        have hnot : ¬ min (u n).val t.val < p.1 := not_lt.mpr (le_min hn.le hlt.le)
        simp [hnot]
      · filter_upwards [hu_coe.eventually (eventually_lt_nhds hgt)] with n hn
        have hnot : ¬ p.1 ≤ max (u n).val t.val := not_le.mpr (max_lt hn hgt)
        simp [hnot]
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (f := fun _ ↦ (0 : ℝ)) (fun p ↦ H p.1 p.2 ^ 2)
      (fun n ↦ hmem_sq.aestronglyMeasurable.indicator (measurableSet_Ioc.prod MeasurableSet.univ))
      hmem_sq hbound hpt
  have hlim_edist : Tendsto (fun n ↦ ENNReal.ofReal √(∫ ω, (I (u n) ω - I t ω) ^ 2 ∂P))
      atTop (𝓝 0) := by
    have hcont : Tendsto (fun x ↦ ENNReal.ofReal √x) (𝓝 0) (𝓝 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero] using
        ((ENNReal.continuous_ofReal.comp Real.continuous_sqrt).continuousAt (x := 0)).tendsto
    exact hcont.comp hlim_int
  refine hlim_edist.congr fun n ↦ ?_
  simp only [Function.comp_apply, Lp.edist_toLp_toLp]
  have hdiff_mem : MemLp (I (u n) - I t) 2 P := (mem (u n)).sub (mem t)
  simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using
    (hdiff_mem.eLpNorm_two_eq_ofReal_sqrt_integral).symm

end Probability.IsItoIntegral

end TauCeti
