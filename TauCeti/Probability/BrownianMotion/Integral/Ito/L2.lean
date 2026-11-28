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
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.Probability.BrownianMotion.Integral.Deterministic

/-!
# The square-integrable Itô integral process, time continuity, and Itô's covariance

Extending `TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry`, this module establishes
`L²(P)` continuity in time (`TauCeti.Probability.IsItoIntegral.continuous_toLp`) and zero
expectation (`TauCeti.Probability.IsItoIntegral.integral_eq_zero`) for any continuous Itô integral
of a `BrownianIntegrable` integrand, without assuming path continuity of the integrator `W`.

Where only single-horizon expected square energy
`MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)`
holds, it proves zero expectation (`integral_eq_zero_of_memLp`), covariance
(`integral_mul_of_memLp`), increment square integrability (`memLp_sub`, `memLp_sub_restrict`),
unconditional, event-wise, and conditional increment Itô isometries (`integral_sub_sq_of_memLp`,
`setIntegral_sub_sq_of_memLp`, `condExp_sub_sq_of_memLp`), finite-horizon `L²(P)` continuity
(`continuous_toLp_of_memLp`), and for deterministic `L²` integrands identification with
`wienerIntegral` (`ae_eq_wienerIntegral`) and its centered Gaussian law (`hasLaw_gaussianReal`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–C.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti.Probability.IsItoIntegral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ}

/-- **`L²(P)` time continuity**: the `L²(P)` class `t ↦ (hI.memLp hW hH t).toLp (I t)` of a
continuous Itô integral of a `BrownianIntegrable` integrand varies continuously in `t`, without
assuming path continuity of `W`. -/
theorem continuous_toLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    Continuous fun t : ℝ≥0 ↦ (hI.memLp hW hH t).toLp (I t) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine continuous_iff_continuousAt.2 fun t₀ ↦ tendsto_iff_edist_tendsto_0.2 ?_
  have hne_fst : ∀ᵐ t ∂timeMeasure (t₀ + 1), t ≠ t₀ := by
    simp only [ae_iff, ne_eq, not_not, ofPred_eq_eq_singleton,
      timeMeasure_apply _ (measurableSet_singleton t₀)]
    by_cases h0 : t₀ ∈ Ioc 0 (t₀ + 1) <;> simp [h0]
  have hne : ∀ᵐ p ∂(timeMeasure (t₀ + 1)).prod P, p.1 ≠ t₀ :=
    (Measure.quasiMeasurePreserving_fst (μ := timeMeasure (t₀ + 1)) (ν := P)).ae hne_fst
  have hlim : Tendsto (fun t ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ (uIoc t₀ t).indicator (H · p.2) p.1 - 0) 2
        ((timeMeasure (t₀ + 1)).prod P)) (𝓝 t₀) (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (.of_forall fun t ↦ (hH.memLp_timeMeasure (t₀ + 1)).aestronglyMeasurable.indicator
        ((measurableSet_uIoc (a := t₀) (b := t)).prod MeasurableSet.univ) |>.congr
          (.of_forall fun p ↦ by
            by_cases hp : p.1 ∈ uIoc t₀ t <;> simp [Function.uncurry_def, hp]))
      (hH.memLp_timeMeasure (t₀ + 1))
      (.of_forall fun t ↦ .of_forall fun p ↦ by
        simpa only [Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul, Function.uncurry_def] using
          eNorm_indicator_le_eNorm_self (H · p.2) p.1)
      (hne.mono fun p hp ↦ tendsto_const_nhds.congr' <| by
        rcases lt_or_gt_of_ne hp with hlt | hgt
        · filter_upwards [eventually_gt_nhds hlt] with t ht
          rw [Set.indicator_of_notMem (by simp [Set.mem_uIoc, hlt.not_gt, ht.not_gt])]
        · filter_upwards [eventually_lt_nhds hgt] with t ht
          rw [Set.indicator_of_notMem (by simp [Set.mem_uIoc, hgt.not_ge, ht.not_ge])])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ ↦ zero_le)
    (Eventually.mono (Iio_mem_nhds (lt_add_one t₀)) fun t (ht : t < t₀ + 1) ↦ ?_)
  rw [Lp.edist_toLp_toLp]
  simp only [sub_zero]
  rcases le_total t₀ t with hle | hle
  · rw [hI.eLpNorm_sub_eq hW hH hle, uIoc_of_le hle]
    exact eLpNorm_mono_measure _ (Measure.prod_mono (timeMeasure_mono ht.le) le_rfl)
  · rw [← eLpNorm_neg, neg_sub, hI.eLpNorm_sub_eq hW hH hle, uIoc_of_ge hle]
    exact eLpNorm_mono_measure _ (Measure.prod_mono (timeMeasure_mono le_self_add) le_rfl)

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand has expectation zero at every
horizon, without assuming path continuity of `W` or adaptation of `I`. -/
theorem integral_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH T)).trans (hW.integral_l2Integral T _)

/-- Against a filtered pre-Brownian motion, every Itô integral of a deterministic `L²` integrand
`u` agrees almost surely at horizon `t` with `hW.toIsPreBrownianReal.wienerIntegral`. -/
theorem ae_eq_wienerIntegral (hW : IsFilteredPreBrownianReal ℱ W P) {u : ℝ≥0 → ℝ}
    (hI : IsItoIntegral ℱ P W (fun s _ ↦ u s) I) {t : ℝ≥0}
    (hu : MemLp u 2 (timeMeasure t)) :
    I t =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral t (hu.toLp u) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have h := hI.ae_eq_l2Integral_of_memLp hW (hu.comp_measurePreserving measurePreserving_fst)
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
theorem integral_eq_zero_of_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) : ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral_of_memLp hW hH)).trans (hW.integral_l2Integral t _)

/-- **Itô's covariance identity.** Against a filtered pre-Brownian motion, the inner product of two
Itô integrals at horizon `t` with finite expected square energy on `(0, t]` equals the time-product
integral of `H * K` on `(0, t] × Ω`. -/
theorem integral_mul_of_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
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
    (integral_congr_ae <| (hI.ae_eq_l2Integral_of_memLp hW hH).mp <|
      (hJ.ae_eq_l2Integral_of_memLp hW hK).mono fun _ h₂ h₁ ↦ by simp [h₁, h₂, mul_comm]).trans
      (L2.inner_def _ _).symm
  rw [hlhs, (hW.l2Integral t).inner_map_map, L2.inner_def]
  exact (integral_congr_ae <| hHp.coeFn_toLp.mp <|
    hKp.coeFn_toLp.mono fun _ h₂ h₁ ↦ by simp [h₁, h₂, Function.uncurry, mul_comm]).trans
    (ℱ.integral_predictableMeasure P (hI.isStronglyPredictable.mul hJ.isStronglyPredictable) t)

private theorem isItoIntegral_ite_lt_indicator_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (hH : MemLp (Function.uncurry H) 2 (((timeMeasure t).prod P).restrict (Ioc s t ×ˢ A))) :
    IsItoIntegral ℱ P W (fun u ω ↦ if s < u then A.indicator (fun _ ↦ 1) ω * H u ω else 0)
        (fun u ω ↦ A.indicator (fun _ ↦ 1) ω * (I u ω - I (min s u) ω)) ∧
      MemLp (Function.uncurry (fun u ω ↦
        if s < u then A.indicator (fun _ ↦ 1) ω * H u ω else 0)) 2 ((timeMeasure t).prod P) := by
  have hξ : StronglyMeasurable[ℱ s] (A.indicator fun _ ↦ (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hA
  refine ⟨hI.ite_lt_mul hW s hξ, ((memLp_indicator_iff_restrict
      (measurableSet_Ioc.prod (ℱ.le s A hA)).nullMeasurableSet).2 hH).ae_eq ?_⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae (ae_mem_Ioc_timeMeasure t)]
    with p hp
  by_cases hs : s < p.1 <;> by_cases hpA : p.2 ∈ A <;> simp [Function.uncurry, hs, hp.2, hpA]

/-- For `s ≤ t` and an event `A ∈ ℱ s`, if `H` has finite expected square energy on `(s, t] × A`,
then the increment `I t - I s` is square integrable on `A`. -/
theorem memLp_sub_restrict (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (hH : MemLp (Function.uncurry H) 2 (((timeMeasure t).prod P).restrict (Ioc s t ×ˢ A))) :
    MemLp (I t - I s) 2 (P.restrict A) := by
  obtain ⟨hcut, hH_mem⟩ := isItoIntegral_ite_lt_indicator_memLp hW hI hA hH
  refine (memLp_indicator_iff_restrict (ℱ.le s A hA).nullMeasurableSet).1 ?_
  convert hcut.memLp_of_memLp hW hH_mem using 1
  ext ω
  by_cases hω : ω ∈ A <;> simp [hω, min_eq_left hst]

/-- For `s ≤ t`, if `H` has finite expected square energy on `(s, t]`, then the increment
`I t - I s` is square integrable. -/
theorem memLp_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t)
    (hH : MemLp (Function.uncurry H) 2 (((timeMeasure t).prod P).restrict (Ioc s t ×ˢ Set.univ))) :
    MemLp (I t - I s) 2 P := by
  simpa only [Measure.restrict_univ] using
    hI.memLp_sub_restrict hW hst (MeasurableSet.univ : MeasurableSet[ℱ s] Set.univ) hH

/-- **Event-wise Itô increment `L²` isometry.** For `s ≤ t` and an event `A ∈ ℱ s`, if `H` has
finite expected square energy on `(s, t] × A`, then the squared increment integrated over `A` equals
the expected square energy of `H` over `(s, t] × A`. -/
theorem setIntegral_sub_sq_of_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (hH : MemLp (Function.uncurry H) 2 (((timeMeasure t).prod P).restrict (Ioc s t ×ˢ A))) :
    ∫ ω in A, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p in Ioc s t ×ˢ A, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  obtain ⟨hcut, hH_mem⟩ := isItoIntegral_ite_lt_indicator_memLp hW hI hA hH
  have hsq := hcut.integral_sq_of_memLp hW hH_mem
  simp only [min_eq_left hst] at hsq
  have hAm : MeasurableSet A := ℱ.le s A hA
  have hlhs : ∫ ω, (A.indicator (fun _ ↦ (1 : ℝ)) ω * (I t ω - I s ω)) ^ 2 ∂P =
      ∫ ω in A, (I t ω - I s ω) ^ 2 ∂P := by
    rw [← integral_indicator hAm]
    refine integral_congr_ae (.of_forall fun ω ↦ ?_)
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [hlhs] at hsq
  rw [hsq, ← integral_indicator (measurableSet_Ioc.prod hAm)]
  refine integral_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae (ae_mem_Ioc_timeMeasure t)]
    with p hp
  by_cases hs : s < p.1 <;> by_cases hpA : p.2 ∈ A <;> simp [hs, hp.2, hpA]

/-- **Itô's increment `L²` isometry.** For `s ≤ t`, the expected squared increment
`E[(I_t - I_s)²]` equals the expected square energy of `H` over `(s, t] × Ω`. -/
theorem integral_sub_sq_of_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t)
    (hH : MemLp (Function.uncurry H) 2 (((timeMeasure t).prod P).restrict (Ioc s t ×ˢ Set.univ))) :
    ∫ ω, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p in Ioc s t ×ˢ Set.univ, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  simpa only [setIntegral_univ] using
    hI.setIntegral_sub_sq_of_memLp hW hst (MeasurableSet.univ : MeasurableSet[ℱ s] Set.univ) hH

/-- **Conditional Itô increment `L²` isometry.** For `s ≤ t`, if `H` has finite expected square
energy on `(s, t]`, then the conditional second moment of `I t - I s` given `ℱ s` equals the
conditional expectation of the pathwise square energy of `H` over `(s, t]` given `ℱ s`. -/
theorem condExp_sub_sq_of_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t)
    (hH : MemLp (Function.uncurry H) 2 (((timeMeasure t).prod P).restrict (Ioc s t ×ˢ Set.univ))) :
    P[fun ω ↦ (I t ω - I s ω) ^ 2 | ℱ s] =ᵐ[P]
      P[fun ω ↦ ∫ u in Ioc s t, H u ω ^ 2 ∂timeMeasure t | ℱ s] := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hsq_mem : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
      (((timeMeasure t).restrict (Ioc s t)).prod P) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    simpa only [Function.uncurry_def, Real.norm_eq_abs, sq_abs] using hH.integrable_sq
  have henergy : Integrable (fun ω ↦ ∫ u in Ioc s t, H u ω ^ 2 ∂timeMeasure t) P :=
    hsq_mem.integral_prod_right
  have hsub_sq : Integrable (fun ω ↦ (I t ω - I s ω) ^ 2) P :=
    (hI.memLp_sub hW hst hH).integrable_sq
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) hsub_sq
    (fun _ _ _ ↦ integrable_condExp.integrableOn) (fun A hA _ ↦ ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  rw [setIntegral_condExp (ℱ.le s) henergy hA,
    hI.setIntegral_sub_sq_of_memLp hW hst hA
      (hH.mono_measure (Measure.restrict_mono (Set.prod_mono_right (Set.subset_univ _)) le_rfl)),
    ← Measure.prod_restrict (Ioc s t) A,
    (integral_prod_symm (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
      (hsq_mem.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self))).symm]

/-- Expected squared increment of an Itô integral between two times `u, t ≤ T` equals the
integral of `H²` over the time slab `(min u t, max u t] × Ω`. -/
private theorem integral_sub_sq_eq_integral_indicator_Ioc
    (hW : IsFilteredPreBrownianReal ℱ W P) (hI : IsItoIntegral ℱ P W H I)
    {T u t : ℝ≥0} (hu : u ≤ T) (ht : t ≤ T)
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure T).prod P)) :
    ∫ ω, (I u ω - I t ω) ^ 2 ∂P =
      ∫ p, (Ioc (min u t) (max u t) ×ˢ Set.univ).indicator
        (fun p ↦ H p.1 p.2 ^ 2) p ∂(timeMeasure T).prod P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hmax_le : max u t ≤ T := max_le hu ht
  have hH_max : MemLp (Function.uncurry H) 2
      (((timeMeasure (max u t)).prod P).restrict (Ioc (min u t) (max u t) ×ˢ Set.univ)) :=
    (hH.mono_measure (Measure.prod_mono (timeMeasure_mono hmax_le) le_rfl)).restrict _
  have hinc := hI.integral_sub_sq_of_memLp hW (min_le_max : min u t ≤ max u t) hH_max
  have heq_lhs : ∫ ω, (I u ω - I t ω) ^ 2 ∂P =
      ∫ ω, (I (max u t) ω - I (min u t) ω) ^ 2 ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω ↦ by
      dsimp only
      rcases le_total u t with hle | hle
      · rw [max_eq_right hle, min_eq_left hle, sub_sq_comm]
      · rw [max_eq_left hle, min_eq_right hle])
  have hprod_res : (timeMeasure (max u t)).prod P =
      ((timeMeasure T).prod P).restrict (Ioc 0 (max u t) ×ˢ Set.univ) := by
    rw [← timeMeasure_restrict_of_le hmax_le, Measure.restrict_prod_eq_prod_univ]
  have hinter : (Ioc (min u t) (max u t) ×ˢ (Set.univ : Set Ω)) ∩
      (Ioc 0 (max u t) ×ˢ Set.univ) = Ioc (min u t) (max u t) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true,
      and_iff_left_iff_imp]
    exact fun h ↦ ⟨bot_le.trans_lt h.1, h.2⟩
  rw [heq_lhs, hinc, hprod_res,
    Measure.restrict_restrict (measurableSet_Ioc.prod MeasurableSet.univ), hinter,
    ← integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]

/-- **Finite-horizon `L²(P)` continuity of the Itô integral.** When `H` has finite expected square
energy on `(0, T]`, the map taking `t ∈ [0, T]` to the `L²(P)` class of `I t` is continuous. -/
theorem continuous_toLp_of_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {T : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure T).prod P)) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    Continuous (fun t : Iic T ↦
      (hI.memLp_of_memLp hW (hH.mono_measure
        (Measure.prod_mono (timeMeasure_mono t.property) le_rfl))).toLp (I t)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let mem (t : Iic T) : MemLp (I t) 2 P :=
    hI.memLp_of_memLp hW (hH.mono_measure (Measure.prod_mono (timeMeasure_mono t.property) le_rfl))
  rw [continuous_iff_seqContinuous]
  intro u t hu
  rw [tendsto_iff_edist_tendsto_0]
  have hmem_sq : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2) ((timeMeasure T).prod P) := by
    simpa only [Function.uncurry_def, Real.norm_eq_abs, sq_abs] using hH.integrable_sq
  have hlim_int : Tendsto (fun n ↦ ∫ ω, (I (u n) ω - I t ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simp_rw [fun n ↦ hI.integral_sub_sq_eq_integral_indicator_Ioc hW
      (u n).property t.property hH]
    exact TauCeti.tendsto_integral_indicator_Ioc_prod_univ hmem_sq
      (continuous_subtypeVal.continuousAt.tendsto.comp hu) (measure_singleton _)
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

end TauCeti.Probability.IsItoIntegral
