/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Integral.Square
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
public import TauCeti.Probability.Process.AccumulatedEnergy
public import TauCeti.MeasureTheory.Measure.NNReal
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.LpLimit
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# L² theory and existence of the Itô stochastic integral

For a `TauCeti.BrownianIntegrable` integrand `H` and a filtered pre-Brownian motion `W`, any
Itô integral `I` satisfying `TauCeti.Probability.IsItoIntegral ℱ P W H I` agrees almost surely at
each finite horizon `T` with the terminal L² integral `hW.l2Integral T`. In particular, `I T` is
square integrable with mean zero, satisfies the Itô isometry and cross-isometry against the
time-product inner product, and—when strongly adapted to `ℱ`—is a true `L²` martingale whose
square minus elapsed pathwise square energy `∫ s, H s ω ^ 2 ∂timeMeasure t` is again a true
martingale on the raw filtration. None of these identification, moment, or martingale properties
require path continuity of `W` or usual conditions on `ℱ`.

When `W` also has almost surely continuous paths, approximating `H` by bounded simple holdings in
time-product `L²` and passing to the continuous martingale limit via
`MeasureTheory.exists_continuous_martingale_of_cauchySeq_Lp` constructs a predictable, continuous
`L²` martingale that satisfies `IsItoIntegral ℱ P W H I`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace

namespace TauCeti.BrownianIntegrable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}

/-- A Brownian-integrable process belongs to `L²` of the finite-horizon predictable measure. -/
theorem memLp_predictableMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 (ℱ.predictableMeasure P T) :=
  (ℱ.memLp_predictableMeasure_iff P hH.isStronglyPredictable T 2).mpr
    (by simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hH.memLp T)

end TauCeti.BrownianIntegrable

namespace MeasureTheory.IsStronglyPredictable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

/-- Pathwise Bochner square energy on `timeMeasure t` equals the real part of the `nnvolume`
accumulated energy. -/
theorem integral_sq_timeMeasure_eq_toReal_accumulatedEnergy
    (hH : IsStronglyPredictable ℱ H) (t : ℝ≥0) (ω : Ω) :
    (∫ s, H s ω ^ 2 ∂TauCeti.Probability.timeMeasure t) =
      (TauCeti.nnvolume.accumulatedEnergy H t ω).toReal := by
  have hHmeas : Measurable (fun s ↦ H s ω) :=
    ((hH.mono ℱ.predictable_le_prod).comp_measurable measurable_prodMk_right).measurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (hHmeas.pow_const 2).aestronglyMeasurable,
    TauCeti.nnvolume.accumulatedEnergy_eq_setLIntegral_Ioc,
    TauCeti.Probability.timeMeasure_def, ← TauCeti.nnvolume_def]
  congr 1
  refine lintegral_congr fun s ↦ ?_
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]

/-- The elapsed pathwise Bochner square energy of a predictable process is again predictable. -/
theorem isStronglyPredictable_integral_sq_timeMeasure (hH : IsStronglyPredictable ℱ H) :
    IsStronglyPredictable ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂TauCeti.Probability.timeMeasure t) := by
  have hpred : IsStronglyPredictable ℱ
      (fun t ω ↦ (TauCeti.nnvolume.accumulatedEnergy H t ω).toReal) :=
    (ENNReal.measurable_toReal.comp
      (hH.isStronglyProgressive.isStronglyPredictable_accumulatedEnergy
        TauCeti.nnvolume).measurable).stronglyMeasurable
  have hfun : (fun t ω ↦ ∫ s, H s ω ^ 2 ∂TauCeti.Probability.timeMeasure t) =
      fun t ω ↦ (TauCeti.nnvolume.accumulatedEnergy H t ω).toReal :=
    funext fun t ↦ funext fun ω ↦ hH.integral_sq_timeMeasure_eq_toReal_accumulatedEnergy t ω
  rwa [hfun]

end MeasureTheory.IsStronglyPredictable

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H K I J : ℝ≥0 → Ω → ℝ}

/-! ### Private helpers for elementary L² identification and energy Markov bounds -/

private theorem stronglyMeasurable_Ioc_prod (s u : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1) := by
  let τ : ℕ → ℝ≥0 := fun j ↦ if j = 0 then s else u
  have hpred : StronglyMeasurable[ℱ.predictable]
      (Function.uncurry (Finance.simpleHolding τ 1 (fun _ ↦ ξ))) :=
    Finance.isStronglyPredictable_simpleHolding (ℱ := ℱ) (τ := τ) (n := 1)
      (a := fun _ ↦ ξ) fun j hj ↦ by
        have hj0 : j = 0 := Nat.lt_one_iff.mp hj
        subst hj0
        simpa [τ] using hξ
  have heq : (fun p : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1) =
      Function.uncurry (Finance.simpleHolding τ 1 (fun _ ↦ ξ)) := by
    ext ⟨t, ω⟩
    simp [Finance.simpleHolding_def, τ]
  rwa [heq]

private theorem memLp_Ioc_prod_predictableMeasure [SFinite P] (T s u : ℝ≥0)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1) 2
      (ℱ.predictableMeasure P T) := by
  let τ : ℕ → ℝ≥0 := fun j ↦ if j = 0 then s else u
  have hmem := Finance.memLp_simpleHolding_predictableMeasure (ℱ := ℱ) (P := P) (τ := τ) (n := 1)
    (a := fun _ ↦ ξ) (fun j hj ↦ by
      have hj0 : j = 0 := Nat.lt_one_iff.mp hj
      subst hj0
      simpa [τ] using hξ)
    (fun _ _ ↦ hξ₂) T
  have heq : (fun p : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1) =
      Function.uncurry (Finance.simpleHolding τ 1 (fun _ ↦ ξ)) := by
    ext ⟨t, ω⟩
    simp [Finance.simpleHolding_def, τ]
  rwa [heq]

private theorem coeFn_l2Integral_Ioc_finsetSum (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s u : ℝ≥0) (S : Finset ℝ) (A : ℝ → Set Ω) (hA : ∀ c, MeasurableSet[ℱ s] (A c)) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    have hg : StronglyMeasurable[ℱ s] (fun ω ↦ ∑ c ∈ S, (A c).indicator (fun _ ↦ c) ω) :=
      Finset.stronglyMeasurable_fun_sum S fun c _ ↦ stronglyMeasurable_const.indicator (hA c)
    have hg₂ : MemLp (fun ω ↦ ∑ c ∈ S, (A c).indicator (fun _ ↦ c) ω) 2 P :=
      memLp_finsetSum S fun c _ ↦
        (memLp_const c).indicator (ℱ.le s _ (hA c)).nullMeasurableSet
    hW.l2Integral T ((memLp_Ioc_prod_predictableMeasure T s u hg hg₂).toLp _) =ᵐ[P]
      fun ω ↦ (∑ c ∈ S, (A c).indicator (fun _ ↦ c) ω) * (W (max s (min u T)) ω - W s ω) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  dsimp only
  have hg : StronglyMeasurable[ℱ s] (fun ω ↦ ∑ c ∈ S, (A c).indicator (fun _ ↦ c) ω) :=
    Finset.stronglyMeasurable_fun_sum S fun c _ ↦ stronglyMeasurable_const.indicator (hA c)
  have hg₂ : MemLp (fun ω ↦ ∑ c ∈ S, (A c).indicator (fun _ ↦ c) ω) 2 P :=
    memLp_finsetSum S fun c _ ↦ (memLp_const c).indicator (ℱ.le s _ (hA c)).nullMeasurableSet
  let term (c : ℝ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s u (hA c)) (measure_ne_top _ _) c
  have hsum : (memLp_Ioc_prod_predictableMeasure T s u hg hg₂).toLp _ = ∑ c ∈ S, term c := by
    apply Lp.ext
    have hterms : ∀ c ∈ S, (term c : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P T]
        (Ioc s u ×ˢ A c).indicator (fun _ ↦ c) := fun _ _ ↦ indicatorConstLp_coeFn
    refine (memLp_Ioc_prod_predictableMeasure T s u hg hg₂).coeFn_toLp.trans ?_
    filter_upwards [Lp.coeFn_finsetSum (s := S) term, eventuallyEq_sum hterms] with p hp hps
    rw [hp, hps]
    simp only [Finset.sum_apply]
    by_cases ht : p.1 ∈ Ioc s u
    · rw [indicator_of_mem ht]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      by_cases hω : p.2 ∈ A c <;> simp [ht, hω]
    · rw [indicator_of_notMem ht]
      exact (Finset.sum_eq_zero fun c _ ↦ by simp [ht]).symm
  rw [hsum, map_sum]
  have heach : ∀ c ∈ S, (hW.l2Integral T (term c) : Ω → ℝ) =ᵐ[P]
      fun ω ↦ (A c).indicator (fun _ ↦ c) ω * (W (max s (min u T)) ω - W s ω) :=
    fun c _ ↦ hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T s u (hA c) c
  filter_upwards [Lp.coeFn_finsetSum (s := S) (fun c ↦ hW.l2Integral T (term c)),
    eventuallyEq_sum heach] with ω hω hsumω
  rw [hω, hsumω]
  simp only [Finset.sum_apply, ← Finset.sum_mul]

private theorem coeFn_l2Integral_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s u : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    hW.l2Integral T ((memLp_Ioc_prod_predictableMeasure T s u hξ hξ₂).toLp _) =ᵐ[P]
      fun ω ↦ ξ ω * (W (max s (min u T)) ω - W s ω) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have happrox_aux : ∀ (m : MeasurableSpace Ω) (μ : @Measure Ω m),
      @StronglyMeasurable Ω ℝ _ m ξ → eLpNorm ξ 2 μ < ∞ →
      ∃ (S : ℕ → Finset ℝ) (A : ℕ → ℝ → Set Ω),
        (∀ k c, MeasurableSet[m] (A k c)) ∧
        Tendsto (fun k ↦ eLpNorm
          ((fun ω ↦ ∑ c ∈ S k, (A k c).indicator (fun _ ↦ c) ω) - ξ) 2 μ) atTop (𝓝 0) := by
    intro m μ hξ' hξ_lt
    let : MeasurableSpace Ω := m
    let φ := SimpleFunc.approxOn ξ hξ'.measurable (univ : Set ℝ) 0 (mem_univ 0)
    have hhi : eLpNorm (fun ω ↦ ξ ω - 0) 2 μ < ∞ := by simpa only [sub_zero] using hξ_lt
    have hlim := SimpleFunc.tendsto_approxOn_Lp_eLpNorm hξ'.measurable (mem_univ (0 : ℝ))
      (by norm_num) (Eventually.of_forall fun _ ↦ by simp) hhi
    refine ⟨fun k ↦ (φ k).range, fun k c ↦ (φ k) ⁻¹' {c},
      fun k c ↦ (φ k).measurableSet_fiber c, hlim.congr fun k ↦ ?_⟩
    congr 1; ext ω; dsimp only [Pi.sub_apply]; congr 1
    rw [Finset.sum_eq_single (φ k ω)]
    · simp [φ]
    · intro c _ hne; simp [Ne.symm hne]
    · intro hnot; exact (hnot ((φ k).mem_range_self ω)).elim
  have hξ_trim : eLpNorm ξ 2 (P.trim (ℱ.le s)) < ∞ := by
    rw [eLpNorm_trim (ℱ.le s) hξ]
    exact hξ₂.eLpNorm_lt_top
  obtain ⟨S, A, hA, hg_lim_trim⟩ := happrox_aux (ℱ s) (P.trim (ℱ.le s)) hξ hξ_trim
  let g (k : ℕ) (ω : Ω) : ℝ := ∑ c ∈ S k, (A k c).indicator (fun _ ↦ c) ω
  have hg_sm (k : ℕ) : StronglyMeasurable[ℱ s] (g k) :=
    Finset.stronglyMeasurable_fun_sum (S k) fun c _ ↦ stronglyMeasurable_const.indicator (hA k c)
  have hg_lim : Tendsto (fun k ↦ eLpNorm (g k - ξ) 2 P) atTop (𝓝 0) :=
    hg_lim_trim.congr fun k ↦ eLpNorm_trim (ℱ.le s) ((hg_sm k).sub hξ)
  have hg_mem (k : ℕ) : MemLp (g k) 2 P :=
    memLp_finsetSum (S k) fun c _ ↦ (memLp_const c).indicator (ℱ.le s _ (hA k c)).nullMeasurableSet
  let lhs (k : ℕ) : Lp ℝ 2 P :=
    hW.l2Integral T ((memLp_Ioc_prod_predictableMeasure T s u (hg_sm k) (hg_mem k)).toLp _)
  let rhs_lim : Lp ℝ 2 P :=
    (hW.memLp_mul_sub (le_max_left s (min u T)) hξ hξ₂).toLp
      (fun ω ↦ ξ ω * (W (max s (min u T)) ω - W s ω))
  have hlhs_lim : Tendsto lhs atTop
      (𝓝 (hW.l2Integral T ((memLp_Ioc_prod_predictableMeasure T s u hξ hξ₂).toLp _))) := by
    refine (hW.l2Integral T).continuous.continuousAt.tendsto.comp ?_
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    have hle (k : ℕ) : eLpNorm (fun p : ℝ≥0 × Ω ↦
          (Ioc s u).indicator (fun _ ↦ g k p.2) p.1 -
            (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1) 2 (ℱ.predictableMeasure P T) ≤
        (timeMeasure T univ) ^ (1 / 2 : ℝ) * eLpNorm (g k - ξ) 2 P := by
      have hpt : (fun p : ℝ≥0 × Ω ↦
          (Ioc s u).indicator (fun _ ↦ g k p.2) p.1 - (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1) =
          fun p : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ (g k - ξ) p.2) p.1 := by
        ext ⟨t, ω⟩
        by_cases ht : t ∈ Ioc s u <;> simp [ht]
      rw [hpt, ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod
        (stronglyMeasurable_Ioc_prod s u ((hg_sm k).sub hξ))]
      refine (eLpNorm_mono (g := fun p : ℝ≥0 × Ω ↦ (g k - ξ) p.2)
        (((stronglyMeasurable_Ioc_prod s u ((hg_sm k).sub hξ)).mono
          ℱ.predictable_le_prod).aestronglyMeasurable) fun p ↦ ?_).trans_eq ?_
      · by_cases ht : p.1 ∈ Ioc s u <;> simp [ht]
      · have hsm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ (g k - ξ) p.2) :=
          (((hg_sm k).sub hξ).mono (ℱ.le s)).comp_measurable measurable_snd
        rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
            hsm.aestronglyMeasurable,
          eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
            ((hg_mem k).sub hξ₂).aestronglyMeasurable,
          lintegral_prod_symm _ (hsm.measurable.eNorm.pow_const _).aemeasurable]
        simp only [lintegral_const, ENNReal.toReal_ofNat, mul_comm _ (timeMeasure T univ)]
        rw [lintegral_const_mul _ ((((hg_sm k).sub hξ).mono (ℱ.le s)).measurable.eNorm.pow_const _),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / 2)]
    have hconst_ne : (timeMeasure T univ) ^ (1 / 2 : ℝ) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top (timeMeasure T) univ)
    have hrhs : Tendsto (fun k ↦ (timeMeasure T univ) ^ (1 / 2 : ℝ) *
        eLpNorm (g k - ξ) 2 P) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hg_lim (Or.inr hconst_ne)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs (fun _ ↦ zero_le) hle
  have hrhs_lim : Tendsto (fun k ↦ lhs k) atTop (𝓝 rhs_lim) := by
    have hlhs_eq (k : ℕ) : lhs k =
        (hW.memLp_mul_sub (le_max_left s (min u T)) (hg_sm k) (hg_mem k)).toLp
          (fun ω ↦ g k ω * (W (max s (min u T)) ω - W s ω)) :=
      Lp.ext ((coeFn_l2Integral_Ioc_finsetSum hW T s u (S k) (A k) (hA k)).trans
        (hW.memLp_mul_sub (le_max_left s (min u T)) (hg_sm k) (hg_mem k)).coeFn_toLp.symm)
    simp_rw [hlhs_eq]
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    have heLp2 {f : Ω → ℝ} (hf : MemLp f 2 P) :
        eLpNorm f 2 P ^ 2 = ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) := by
      have hp := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
        hf.aestronglyMeasurable
      simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at hp
      have hpt (ω : Ω) : ENNReal.ofReal (f ω ^ 2) = ‖f ω‖ₑ ^ 2 := by
        rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]
      rw [hp, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ sq_nonneg _)
        (hf.aestronglyMeasurable.pow 2), ENNReal.ofReal_toReal]
      · exact lintegral_congr fun ω ↦ (hpt ω).symm
      · have hlt : (∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P) < ∞ := by
          rw [← hp]
          exact ENNReal.pow_lt_top hf.eLpNorm_lt_top
        exact (lt_of_eq_of_lt (lintegral_congr hpt) hlt).ne
    have hnorm (k : ℕ) :
        eLpNorm ((fun ω ↦ g k ω * (W (max s (min u T)) ω - W s ω)) -
            (fun ω ↦ ξ ω * (W (max s (min u T)) ω - W s ω))) 2 P =
          ENNReal.ofReal ((max s (min u T) : ℝ≥0) - (s : ℝ)) ^ (1 / 2 : ℝ) *
            eLpNorm (g k - ξ) 2 P := by
      have hfactor : ((fun ω ↦ g k ω * (W (max s (min u T)) ω - W s ω)) -
            (fun ω ↦ ξ ω * (W (max s (min u T)) ω - W s ω))) =
          fun ω ↦ (g k - ξ) ω * (W (max s (min u T)) ω - W s ω) := by
        ext ω; simp [sub_mul]
      rw [hfactor]
      have hsq := hW.integral_sq_mul_sub (le_max_left s (min u T)) ((hg_sm k).sub hξ)
      have hmem1 := hW.memLp_mul_sub (le_max_left s (min u T))
        ((hg_sm k).sub hξ) ((hg_mem k).sub hξ₂)
      have hsq_eq : eLpNorm (fun ω ↦ (g k - ξ) ω * (W (max s (min u T)) ω - W s ω)) 2 P ^ 2 =
          (ENNReal.ofReal ((max s (min u T) : ℝ≥0) - (s : ℝ)) ^ (1 / 2 : ℝ) *
            eLpNorm (g k - ξ) 2 P) ^ 2 := by
        rw [heLp2 hmem1, hsq,
          ENNReal.ofReal_mul (integral_nonneg fun _ ↦ sq_nonneg _),
          ← heLp2 ((hg_mem k).sub hξ₂), mul_pow,
          ← ENNReal.rpow_natCast (ENNReal.ofReal _ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul, mul_comm]
        norm_num
      have hpow_inj : ∀ x y : ℝ≥0∞, x ^ 2 = y ^ 2 → x = y := fun x y hxy ↦ by
        have h := congrArg (fun z : ℝ≥0∞ ↦ z ^ (1 / 2 : ℝ)) hxy
        rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_natCast y 2,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h
        norm_num at h
        exact h
      exact hpow_inj _ _ hsq_eq
    simp_rw [hnorm]
    have hconst_ne : ENNReal.ofReal ((max s (min u T) : ℝ≥0) - (s : ℝ)) ^ (1 / 2 : ℝ) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hg_lim (Or.inr hconst_ne)
  have heq : hW.l2Integral T ((memLp_Ioc_prod_predictableMeasure T s u hξ hξ₂).toLp _) = rhs_lim :=
    tendsto_nhds_unique hlhs_lim hrhs_lim
  rw [heq]
  exact (hW.memLp_mul_sub (le_max_left s (min u T)) hξ hξ₂).coeFn_toLp

private theorem tendsto_measure_lintegral_eNorm_sq_of_tendsto_eLpNorm [SFinite P]
    {F : ℕ → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hF : ∀ k, StronglyMeasurable (Function.uncurry (F k)))
    (hlim : Tendsto (fun k ↦ eLpNorm (Function.uncurry (F k)) 2 ((timeMeasure T).prod P))
      atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖F k s ω‖ₑ ^ 2 ∂timeMeasure T}) atTop (𝓝 0) := by
  have hlint_eq (k : ℕ) : (∫⁻ ω, ∫⁻ s, ‖F k s ω‖ₑ ^ 2 ∂timeMeasure T ∂P) =
      eLpNorm (Function.uncurry (F k)) 2 ((timeMeasure T).prod P) ^ 2 := by
    have hprod := lintegral_prod_symm (fun p : ℝ≥0 × Ω ↦ ‖Function.uncurry (F k) p‖ₑ ^ 2)
      ((hF k).eNorm.pow_const 2).aemeasurable (μ := timeMeasure T) (ν := P)
    have hp := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      (hF k).aestronglyMeasurable (μ := (timeMeasure T).prod P)
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat,
      Function.uncurry_apply_pair] at hprod hp
    exact hprod.symm.trans hp.symm
  by_cases htop : ε = ∞
  · subst htop
    have hzero : ∀ᶠ k in atTop,
        P {ω | ∞ ≤ ∫⁻ s, ‖F k s ω‖ₑ ^ 2 ∂timeMeasure T} = 0 := by
      filter_upwards [hlim.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))] with k hk
      have hfin : (∫⁻ ω, ∫⁻ s, ‖F k s ω‖ₑ ^ 2 ∂timeMeasure T ∂P) < ∞ := by
        rw [hlint_eq k]
        exact ENNReal.pow_lt_top (hk.trans ENNReal.one_lt_top)
      have hae : ∀ᵐ ω ∂P, ¬ (∞ ≤ ∫⁻ s, ‖F k s ω‖ₑ ^ 2 ∂timeMeasure T) :=
        (ae_lt_top ((hF k).measurable.eNorm.pow_const 2 |>.lintegral_prod_left') hfin.ne).mono
          fun _ hω ↦ not_le.mpr hω
      simpa only [not_not] using ae_iff.mp hae
    exact tendsto_const_nhds.congr' (hzero.mono fun _ h ↦ h.symm)
  · have hbound (k : ℕ) : P {ω | ε ≤ ∫⁻ s, ‖F k s ω‖ₑ ^ 2 ∂timeMeasure T} ≤
        eLpNorm (Function.uncurry (F k)) 2 ((timeMeasure T).prod P) ^ 2 / ε := by
      rw [ENNReal.le_div_iff_mul_le (.inl hε.ne') (.inl htop), mul_comm]
      exact (mul_meas_ge_le_lintegral
        ((hF k).measurable.eNorm.pow_const 2 |>.lintegral_prod_left') ε).trans_eq (hlint_eq k)
    have hrhs : Tendsto (fun k ↦
        eLpNorm (Function.uncurry (F k)) 2 ((timeMeasure T).prod P) ^ 2 / ε) atTop (𝓝 0) := by
      have hsq : Tendsto (fun k ↦
          eLpNorm (Function.uncurry (F k)) 2 ((timeMeasure T).prod P) ^ 2) atTop (𝓝 0) := by
        simpa only [sq, mul_zero] using
          ENNReal.Tendsto.mul hlim (.inr ENNReal.zero_ne_top) hlim (.inr ENNReal.zero_ne_top)
      simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hsq (.inr hε.ne')
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun _ ↦ zero_le) hbound

private theorem martingale_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₁ : ∀ j < n, Integrable (a j) P) :
    Martingale (Finance.simpleGains τ n a W) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  induction n with
  | zero =>
    convert martingale_zero ℝ ℱ P using 1
    ext t ω
    simp [Finance.simpleGains_def]
  | succ n ih =>
    have hτn : MonotoneOn τ (Iic n) := hτ.mono (Iic_subset_Iic.mpr n.le_succ)
    have hprev := ih hτn (fun j hj ↦ ha j (hj.trans n.lt_succ_self))
      (fun j hj ↦ ha₁ j (hj.trans n.lt_succ_self))
    have hstep := hW.martingale_mul_sub_min
      (hτ (by simp) (by simp) n.le_succ) (ha n n.lt_succ_self) (ha₁ n n.lt_succ_self)
    convert hprev.add hstep using 1
    ext t ω
    simp [Finance.simpleGains_def, Finset.sum_range_succ]

/-! ### Identification with the terminal L² integral and moments -/

/-- On a monotone deterministic grid with square-integrable left-measurable heights, the terminal
`L²` Brownian integral agrees almost surely with the elementary gains process. -/
theorem coeFn_l2Integral_simpleHolding (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    hW.l2Integral T ((Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp _) =ᵐ[P]
      Finance.simpleGains τ n a W T := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hterm (j : ℕ) (hj : j < n) :
      MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j p.2) p.1) 2
        (ℱ.predictableMeasure P T) :=
    memLp_Ioc_prod_predictableMeasure T (τ j) (τ (j + 1)) (ha j hj) (ha₂ j hj)
  let f : ℕ → Lp ℝ 2 (ℱ.predictableMeasure P T) := fun j ↦
    if hj : j < n then (hterm j hj).toLp _ else 0
  have hsum : (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
      (Function.uncurry (Finance.simpleHolding τ n a)) = ∑ j ∈ Finset.range n, f j := by
    apply Lp.ext
    have hcoe := Lp.coeFn_finsetSum (s := Finset.range n) f
    have hterms : ∀ j ∈ Finset.range n, (f j : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P T]
        fun p ↦ (Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j p.2) p.1 := fun j hj ↦ by
      have hj' := Finset.mem_range.mp hj
      have hfj : f j = (hterm j hj').toLp _ := by simp [f, hj']
      rw [hfj]
      exact (hterm j hj').coeFn_toLp
    refine (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).coeFn_toLp.trans ?_
    filter_upwards [hcoe, eventuallyEq_sum hterms] with p hp hps
    rw [hp, hps]
    simp [Function.uncurry_def, Finance.simpleHolding_def]
  rw [hsum, map_sum]
  have heach : ∀ j ∈ Finset.range n, (hW.l2Integral T (f j) : Ω → ℝ) =ᵐ[P]
      fun ω ↦ a j ω * (W (min (τ (j + 1)) T) ω - W (min (τ j) T) ω) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hle : τ j ≤ τ (j + 1) :=
      hτ (mem_Iic.mpr hj'.le) (mem_Iic.mpr hj') (Nat.le_succ j)
    have h1 := coeFn_l2Integral_Ioc hW T (τ j) (τ (j + 1)) (ha j hj') (ha₂ j hj')
    have hfj : f j = (hterm j hj').toLp _ := by simp [f, hj']
    rw [hfj]
    filter_upwards [h1] with ω hω
    refine hω.trans ?_
    by_cases hT : τ j ≤ T
    · rw [min_eq_left hT, max_eq_right (le_min hle hT)]
    · have hT' : T ≤ τ j := (not_le.mp hT).le
      simp [min_eq_right hT', min_eq_right (hT'.trans hle), max_eq_left hT']
  filter_upwards [Lp.coeFn_finsetSum (s := Finset.range n) (fun j ↦ hW.l2Integral T (f j)),
    eventuallyEq_sum heach] with ω hω hsumω
  rw [hω, hsumω]
  simp [Finance.simpleGains_def]

private theorem eLpNorm_simpleGains_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    eLpNorm (fun ω ↦ Finance.simpleGains τ n a W T ω -
        hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) ω) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let fK := (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
    (Function.uncurry (Finance.simpleHolding τ n a))
  let fH := (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)
  have h1 : eLpNorm (fun ω ↦ Finance.simpleGains τ n a W T ω - hW.l2Integral T fH ω) 2 P =
      edist (hW.l2Integral T fK) (hW.l2Integral T fH) := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae
      ((hW.coeFn_l2Integral_simpleHolding hτ ha ha₂ T).symm.sub EventuallyEq.rfl)
  rw [h1, (hW.l2Integral T).isometry.edist_eq, Lp.edist_def]
  have h2 : eLpNorm (⇑(fK - fH)) 2 (ℱ.predictableMeasure P T) =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        (ℱ.predictableMeasure P T) :=
    eLpNorm_congr_ae ((Lp.coeFn_sub fK fH).trans
      ((Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).coeFn_toLp.sub
        (hH.memLp_predictableMeasure T).coeFn_toLp))
  have hsub : eLpNorm (⇑fK - ⇑fH) 2 (ℱ.predictableMeasure P T) =
      eLpNorm (⇑(fK - fH)) 2 (ℱ.predictableMeasure P T) :=
    eLpNorm_congr_ae (Lp.coeFn_sub fK fH).symm
  rw [hsub, h2, ℱ.predictableMeasure_def]
  exact eLpNorm_trim ℱ.predictable_le_prod
    ((Finance.isStronglyPredictable_simpleHolding ha).sub hH.isStronglyPredictable)

/-- **Agreement with the terminal L² integral.** For a Brownian-integrable integrand, any Itô
integral agrees almost surely at each finite horizon `T` with `hW.l2Integral T`. Path continuity
of `W` is not required. -/
theorem ae_eq_l2Integral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    I T =ᵐ[P] hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
    (memLp_const (C k)).mono' ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable
      (Eventually.of_forall (hb k j hj))
  have hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure T}) atTop (𝓝 0) := fun ε hε ↦
    tendsto_measure_lintegral_eNorm_sq_of_tendsto_eLpNorm
      (F := fun k s ω ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω)
      (fun k ↦ ((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod)
      (hlim T) hε
  have hL2 : Tendsto (fun k ↦ eLpNorm (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W T ω -
      hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) ω) 2 P)
      atTop (𝓝 0) := by
    simpa only [fun k ↦ hW.eLpNorm_simpleGains_sub_l2Integral hH (hτ k).monotoneOn (ha k) (ha₂ k) T]
      using hlim T
  exact hW.ae_eq_of_isItoIntegral hI (fun k ↦ (hτ k).monotoneOn) ha hE
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hL2)

/-- **L² characterization of Itô integrals.** For a Brownian-integrable integrand `H`, an almost
surely continuous process `I` is an Itô integral of `H` if and only if `I T` agrees almost surely
with the terminal `L²` integral `hW.l2Integral T` at every horizon `T`. Path continuity of `W` is
not required. -/
theorem isItoIntegral_iff_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hIcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) :
    IsItoIntegral ℱ P W H I ↔
      ∀ T : ℝ≥0, I T =ᵐ[P]
        hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  refine ⟨fun hI T ↦ hW.ae_eq_l2Integral_of_isItoIntegral hH hI T, fun hT ↦ ?_⟩
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
    (memLp_const (C k)).mono' ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable
      (Eventually.of_forall (hb k j hj))
  refine ⟨hH.isStronglyPredictable, hIcont, fun T ↦
    ⟨n, τ, a, fun k ↦ (hτ k).monotoneOn, ha, fun k j hj ↦ ⟨C k, hb k j hj⟩, fun ε hε ↦ ?_, ?_⟩⟩
  · exact tendsto_measure_lintegral_eNorm_sq_of_tendsto_eLpNorm
      (F := fun k s ω ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω)
      (fun k ↦ ((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod)
      (hlim T) hε
  · refine tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ?_
    have heq (k : ℕ) : eLpNorm (Finance.simpleGains (τ k) (n k) (a k) W T - I T) 2 P =
        eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)
          2 ((timeMeasure T).prod P) := by
      rw [eLpNorm_congr_ae (EventuallyEq.rfl.sub (hT T))]
      exact hW.eLpNorm_simpleGains_sub_l2Integral hH (hτ k).monotoneOn (ha k) (ha₂ k) T
    simpa only [heq] using hlim T

/-- Every Itô integral of a Brownian-integrable process is square integrable at each horizon. -/
theorem memLp_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm

/-- Every Itô integral of a Brownian-integrable process has expectation zero at each horizon. -/
theorem integral_eq_zero_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t)).trans
    (hW.integral_l2Integral t _)

/-- **Itô cross-isometry.** The covariance of two Brownian-integrable Itô integrals at horizon `t`
equals the time-product inner product of their integrands on `(0, t]`. -/
theorem integral_mul_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (t : ℝ≥0) :
    ∫ ω, I t ω * J t ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure t).prod P := by
  let f := (hH.memLp_predictableMeasure t).toLp (Function.uncurry H)
  let g := (hK.memLp_predictableMeasure t).toLp (Function.uncurry K)
  have h1 : ∫ ω, I t ω * J t ω ∂P = ⟪hW.l2Integral t f, hW.l2Integral t g⟫_ℝ := by
    rw [real_inner_comm, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hW.ae_eq_l2Integral_of_isItoIntegral hH hI t,
      hW.ae_eq_l2Integral_of_isItoIntegral hK hJ t] with ω hωI hωJ
    simp [f, g, hωI, hωJ]
  rw [h1, (hW.l2Integral t).inner_map_map, real_inner_comm, L2.inner_def]
  have h2 : ∫ p, inner ℝ (g p) (f p) ∂ℱ.predictableMeasure P t =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂ℱ.predictableMeasure P t := by
    refine integral_congr_ae ?_
    filter_upwards [(hH.memLp_predictableMeasure t).coeFn_toLp,
      (hK.memLp_predictableMeasure t).coeFn_toLp] with p hpH hpK
    simp only [RCLike.inner_apply, conj_trivial, f, g, hpH, hpK]
    rfl
  rw [h2]
  exact ℱ.integral_predictableMeasure P
    (hH.isStronglyPredictable.mul hK.isStronglyPredictable) t

/-- **Itô isometry.** The second moment of a Brownian-integrable Itô integral at horizon `t`
equals the expected square energy of its integrand on `(0, t]`. -/
theorem integral_sq_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  simpa only [sq] using hW.integral_mul_of_isItoIntegral hH hH hI hI t

/-! ### L² martingale property, square compensation, and existence -/

/-- Any strongly adapted Itô integral of a Brownian-integrable process is a true martingale on
the raw filtration. Path continuity of `W` is not required. -/
theorem martingale_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adapt : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
    (memLp_const (C k)).mono' ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable
      (Eventually.of_forall (hb k j hj))
  have hM (k : ℕ) : Martingale (Finance.simpleGains (τ k) (n k) (a k) W) ℱ P :=
    hW.martingale_simpleGains (hτ k).monotoneOn (ha k)
      (fun j hj ↦ (ha₂ k j hj).integrable one_le_two)
  refine martingale_of_tendsto_eLpNorm_one hM hI_adapt fun t ↦ ?_
  refine TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two ?_
  have heq (k : ℕ) : eLpNorm (Finance.simpleGains (τ k) (n k) (a k) W t - I t) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)
        2 ((timeMeasure t).prod P) := by
    rw [eLpNorm_congr_ae (EventuallyEq.rfl.sub (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t))]
    exact hW.eLpNorm_simpleGains_sub_l2Integral hH (hτ k).monotoneOn (ha k) (ha₂ k) t
  simpa only [heq] using hlim t

private theorem simpleHolding_energy_eq_integral_sq {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n)) (t : ℝ≥0) (ω : Ω) :
    (∑ j ∈ Finset.range n, a j ω ^ 2 * (↑(min (τ (j + 1)) t) - ↑(min (τ j) t))) =
      ∫ s, Finance.simpleHolding τ n a s ω ^ 2 ∂timeMeasure t := by
  have hKmeas : Measurable (fun s ↦ Finance.simpleHolding τ n a s ω) := by
    simp only [Finance.simpleHolding_def]
    exact Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ioc
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ sq_nonneg _)
    (hKmeas.pow_const 2).aestronglyMeasurable]
  have hlint : (∫⁻ s, ENNReal.ofReal (Finance.simpleHolding τ n a s ω ^ 2) ∂timeMeasure t) =
      ∑ j ∈ Finset.range n, ‖a j ω‖ₑ ^ 2 *
        ENNReal.ofReal ((min (τ (j + 1)) t : ℝ≥0) - (τ j : ℝ)) := by
    rw [← Finance.lintegral_enorm_sq_simpleHolding_timeMeasure hτ]
    refine lintegral_congr fun s ↦ ?_
    rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]
  rw [hlint, ENNReal.toReal_sum (fun j _ ↦
    ENNReal.mul_ne_top (ENNReal.pow_ne_top eNorm_ne_top) ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  have hle : τ j ≤ τ (j + 1) := hτ (mem_Iic.mpr hj'.le) (mem_Iic.mpr hj') (Nat.le_succ j)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_eNorm, Real.norm_eq_abs, sq_abs]
  by_cases hT : τ j ≤ t
  · have hsub : (0 : ℝ) ≤ (min (τ (j + 1)) t : ℝ≥0) - (τ j : ℝ) :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr (le_min hle hT))
    rw [ENNReal.toReal_ofReal hsub, min_eq_left hT]
  · have hT' : t ≤ τ j := (not_le.mp hT).le
    have hsub : ((min (τ (j + 1)) t : ℝ≥0) : ℝ) - (τ j : ℝ) ≤ 0 :=
      sub_nonpos.mpr (NNReal.coe_le_coe.mpr ((min_le_right _ _).trans hT'))
    rw [ENNReal.ofReal_of_nonpos hsub]
    simp [min_eq_right hT', min_eq_right (hT'.trans hle)]

private theorem stronglyMeasurable_simpleHolding_energy {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) (t : ℝ≥0) :
    StronglyMeasurable[ℱ t] (fun ω ↦
      ∑ j ∈ Finset.range n, a j ω ^ 2 * (↑(min (τ (j + 1)) t) - ↑(min (τ j) t))) := by
  refine Finset.stronglyMeasurable_fun_sum _ fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  by_cases hT : τ j ≤ t
  · exact (((ha j hj').mono (ℱ.mono hT)).pow 2).mul stronglyMeasurable_const
  · have hT' : t ≤ τ j := (not_le.mp hT).le
    have hle' : τ j ≤ τ (j + 1) := hτ (mem_Iic.mpr hj'.le) (mem_Iic.mpr hj') (Nat.le_succ j)
    have h0 : (fun ω ↦ a j ω ^ 2 * (↑(min (τ (j + 1)) t) - ↑(min (τ j) t))) = 0 := by
      ext ω; simp [min_eq_right hT', min_eq_right (hT'.trans hle')]
    rw [h0]
    exact stronglyMeasurable_zero

/-- **L² Itô square compensation (quadratic variation bracket).** For a Brownian-integrable
integrand and a strongly adapted Itô integral `I`, the process
`I t ^ 2 - ∫ s, H s ^ 2 ∂timeMeasure t` is a true martingale on the raw filtration.
Path continuity of `W` is not required. -/
theorem martingale_sq_sub_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adapt : StronglyAdapted ℱ I) :
    Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hA_adapt : StronglyAdapted ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) :=
    hH.isStronglyPredictable.isStronglyPredictable_integral_sq_timeMeasure
      |>.isStronglyProgressive.stronglyAdapted
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
    (memLp_const (C k)).mono' ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable
      (Eventually.of_forall (hb k j hj))
  let B (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j ∈ Finset.range (n k), a k j ω ^ 2 * (↑(min (τ k (j + 1)) t) - ↑(min (τ k j) t))
  have hM (k : ℕ) : Martingale (fun t ω ↦
      Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - B k t ω) ℱ P :=
    hW.martingale_sq_simpleGains_sub (hτ k).monotoneOn (ha k) (ha₂ k)
  refine martingale_of_tendsto_eLpNorm_one hM (fun t ↦ (hI_adapt t).pow 2 |>.sub (hA_adapt t))
    fun t ↦ ?_
  have hgain_L2 : Tendsto (fun k ↦ eLpNorm
      (Finance.simpleGains (τ k) (n k) (a k) W t - I t) 2 P) atTop (𝓝 0) := by
    have heq (k : ℕ) : eLpNorm (Finance.simpleGains (τ k) (n k) (a k) W t - I t) 2 P =
        eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)
          2 ((timeMeasure t).prod P) := by
      rw [eLpNorm_congr_ae (EventuallyEq.rfl.sub (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t))]
      exact hW.eLpNorm_simpleGains_sub_l2Integral hH (hτ k).monotoneOn (ha k) (ha₂ k) t
    simpa only [heq] using hlim t
  have hsq_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - I t ω ^ 2) 1 P)
      atTop (𝓝 0) :=
    TauCeti.tendsto_eLpNorm_sq_sub_one (hW.memLp_of_isItoIntegral hH hI t).eLpNorm_ne_top hgain_L2
  have henergy_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P) atTop (𝓝 0) := by
    have hHmem : MemLp (fun p : ℝ≥0 × Ω ↦ H p.1 p.2) 2 ((timeMeasure t).prod P) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def, Function.uncurry_def] using
        hH.memLp t
    have hprod_lim : Tendsto (fun k ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 ^ 2 - H p.1 p.2 ^ 2)
        1 ((timeMeasure t).prod P)) atTop (𝓝 0) :=
      TauCeti.tendsto_eLpNorm_sq_sub_one hHmem.eLpNorm_ne_top (hlim t)
    have hle (k : ℕ) : eLpNorm (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P ≤
        eLpNorm (fun p : ℝ≥0 × Ω ↦
          Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 ^ 2 - H p.1 p.2 ^ 2)
          1 ((timeMeasure t).prod P) := by
      have hBm := stronglyMeasurable_simpleHolding_energy (hτ k).monotoneOn (ha k) t
      have hBA_sm : AEStronglyMeasurable
          (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) P :=
        ((hBm.mono (ℱ.le t)).sub ((hA_adapt t).mono (ℱ.le t))).aestronglyMeasurable
      have hdiff_sm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦
          Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 ^ 2 - H p.1 p.2 ^ 2) :=
        (((Finance.isStronglyPredictable_simpleHolding (ha k)).mono
          ℱ.predictable_le_prod).pow 2).sub
            ((hH.isStronglyPredictable.mono ℱ.predictable_le_prod).pow 2)
      rw [eLpNorm_one_eq_lintegral_eNorm hBA_sm,
        eLpNorm_one_eq_lintegral_eNorm hdiff_sm.aestronglyMeasurable,
        lintegral_prod_symm _ hdiff_sm.measurable.eNorm.aemeasurable]
      refine lintegral_mono_ae ?_
      filter_upwards [hH.locallyBrownianIntegrable.ae_memLp] with ω hω
      have hH2 : MemLp (fun s ↦ H s ω) 2 (timeMeasure t) := by
        simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using hω t
      have hK2 : MemLp (fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω) 2
          (timeMeasure t) := by
        simp only [Finance.simpleHolding_def]
        exact memLp_finsetSum _ fun j _ ↦
          (memLp_const (a k j ω)).indicator measurableSet_Ioc.nullMeasurableSet
      dsimp only [B]
      rw [simpleHolding_energy_eq_integral_sq (hτ k).monotoneOn t ω,
        ← integral_sub hK2.integrable_sq hH2.integrable_sq]
      exact eNorm_integral_le_lintegral_eNorm _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprod_lim
      (fun _ ↦ zero_le) hle
  have hle (k : ℕ) : eLpNorm ((fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - B k t ω) -
      (fun ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t)) 1 P ≤
      eLpNorm (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - I t ω ^ 2) 1 P +
        eLpNorm (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P := by
    have hsplit : ((fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - B k t ω) -
        (fun ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t)) =
        (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - I t ω ^ 2) -
          (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) := by
      ext ω; simp; ring
    rw [hsplit]
    exact eLpNorm_sub_le le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hsq_lim.add henergy_lim) (fun _ ↦ zero_le) hle

/-- **Existence of the L² Itô stochastic integral.** Every Brownian-integrable process against a
continuous filtered pre-Brownian motion admits a predictable, almost surely continuous `L²`
martingale that is its Itô integral. No usual conditions on the filtration are required. -/
theorem exists_isItoIntegral_of_brownianIntegrable (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ,
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
    (memLp_const (C k)).mono' ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable
      (Eventually.of_forall (hb k j hj))
  let M (k : ℕ) : ℝ≥0 → Ω → ℝ := Finance.simpleGains (τ k) (n k) (a k) W
  have hM (k : ℕ) : Martingale (M k) ℱ P :=
    hW.martingale_simpleGains (hτ k).monotoneOn (ha k)
      (fun j hj ↦ (ha₂ k j hj).integrable one_le_two)
  have hMcont (k : ℕ) : ∀ᵐ ω ∂P, Continuous (fun t ↦ M k t ω) := by
    filter_upwards [hcont] with ω hω
    simp only [M, Finance.simpleGains_def]
    exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul
      ((hω.comp (continuous_const.min continuous_id)).sub
        (hω.comp (continuous_const.min continuous_id)))
  have hMmem (k : ℕ) (t : ℝ≥0) : MemLp (M k t) 2 P :=
    (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (hτ k).monotoneOn (ha k) (ha₂ k) t)
  have hMcau (t : ℝ≥0) : CauchySeq (fun k ↦ (hMmem k t).toLp (M k t)) := by
    refine Tendsto.cauchySeq
      (x := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) ?_
    have heq (k : ℕ) : (hMmem k t).toLp (M k t) =
        hW.l2Integral t ((Finance.memLp_simpleHolding_predictableMeasure (ha k) (ha₂ k) t).toLp
          (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k)))) :=
      Lp.ext ((hMmem k t).coeFn_toLp.trans
        (hW.coeFn_l2Integral_simpleHolding (hτ k).monotoneOn (ha k) (ha₂ k) t).symm)
    simp_rw [heq]
    refine (hW.l2Integral t).continuous.continuousAt.tendsto.comp ?_
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    have htrim (k : ℕ) : eLpNorm (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k)) -
          Function.uncurry H) 2 (ℱ.predictableMeasure P t) =
        eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)
          2 ((timeMeasure t).prod P) := by
      rw [ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod
        ((Finance.isStronglyPredictable_simpleHolding (ha k)).sub hH.isStronglyPredictable)]
      rfl
    simpa only [htrim] using hlim t
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  obtain ⟨I, hImart, hIpred, hIL2, _, ⟨_, _, hIpath⟩⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp hM hMcont hMmem hMcau
  refine ⟨I, ⟨hH.isStronglyPredictable, hIpath.mono fun _ h ↦ h.1, fun t ↦ ?_⟩, hIpred, hImart⟩
  refine ⟨n, τ, a, fun k ↦ (hτ k).monotoneOn, ha, fun k j hj ↦ ⟨C k, hb k j hj⟩,
    fun ε hε ↦ ?_, tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hIL2 t).2⟩
  exact tendsto_measure_lintegral_eNorm_sq_of_tendsto_eLpNorm
    (F := fun k s ω ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω)
    (fun k ↦ ((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
      hH.isStronglyPredictable).mono ℱ.predictable_le_prod)
    (hlim t) hε

end TauCeti.Probability.IsFilteredPreBrownianReal
