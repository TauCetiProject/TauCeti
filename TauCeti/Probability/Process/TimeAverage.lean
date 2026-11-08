/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan

/-!
# Predictable backward time averages

Integrating a progressively measurable process in time gives an adapted process. When every
path is locally integrable, the primitive is continuous, so its backward difference quotients
are predictable. These averages approximate the original process at almost every positive
time on each path. They provide continuous predictable approximants without completing the
filtration or changing its information.

For real-valued processes a bounded arctangent transform removes the path-integrability
assumption. Taking a measurable limit of backward averages and undoing that transform gives
a predictable representative of every progressive process, equal at almost every positive
time on every path. Fubini then gives equality for time × measure on every finite horizon.
This permits progressive coefficients to be used as predictable stochastic integrands while
preserving their time-product almost-everywhere identities. The differentiation step uses
Mathlib's `LocallyIntegrable.ae_hasDerivAt_integral`.

Time is nonnegative real. In real time integrals the process is extended to negative times
by its initial value. The backward averages use the interval `[(t - ε)⁺, t]` and the fixed
normalization `1 / ε`; in particular, they vanish at time zero. No fixed-time modification or
indistinguishability conclusion is asserted by almost-everywhere convergence in time.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace MeasureTheory.IsStronglyProgressive

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : ℝ≥0 → Ω → E}

omit [CompleteSpace E] in
/-- The time primitive of a strongly progressive process is strongly adapted. No pathwise
integrability hypothesis is needed for this measurability assertion. -/
theorem stronglyAdapted_timeIntegral (hH : IsStronglyProgressive ℱ H) :
    StronglyAdapted ℱ (fun t ω ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal ω) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have hm : StronglyMeasurable[MeasurableSpace.prod inferInstance (ℱ t)]
      (fun p : ℝ × Ω ↦ H (min p.1.toNNReal t) p.2) :=
    (hH t).comp_measurable
      (((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk
        (h := fun _ ↦ min_le_right _ _) |>.prodMk measurable_snd)
  have hi := hm.integral_prod_left' (μ := volume.restrict (Ioc 0 (t : ℝ)))
  convert hi using 1
  ext ω
  dsimp only
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  have hst : s.toNNReal ≤ t := by simpa using Real.toNNReal_le_toNNReal hs.2
  dsimp only
  rw [min_eq_left hst]

omit [CompleteSpace E] in
/-- For locally integrable paths, backward time averages of a progressive process are
strongly adapted and continuous on every path, hence strongly predictable. -/
theorem isStronglyPredictable_backwardAverage (hH : IsStronglyProgressive ℱ H)
    (hloc : ∀ ω, LocallyIntegrable (fun s : ℝ ↦ H s.toNNReal ω) volume) (ε : ℝ≥0) :
    IsStronglyPredictable ℱ (fun t ω ↦ (ε : ℝ)⁻¹ •
      ((∫ s in (0 : ℝ)..t, H s.toNNReal ω) -
        ∫ s in (0 : ℝ)..(t - ε : ℝ≥0), H s.toNNReal ω)) := by
  have hi := hH.stronglyAdapted_timeIntegral
  have had : StronglyAdapted ℱ (fun t ω ↦
      ∫ s in (0 : ℝ)..(t - ε : ℝ≥0), H s.toNNReal ω) :=
    fun t ↦ (hi (t - ε)).mono (ℱ.mono tsub_le_self)
  refine ((hi.sub had).smul (ε : ℝ)⁻¹).isStronglyPredictable_of_continuous ?_
  intro ω
  have hc : Continuous (fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal ω) :=
    intervalIntegral.continuous_primitive
      (fun a b ↦ ((hloc ω).integrableOn_isCompact isCompact_uIcc).intervalIntegrable) 0
  exact (hc.comp NNReal.continuous_coe |>.sub
    (hc.comp (NNReal.continuous_coe.comp (continuous_id.sub continuous_const)))).const_smul _

/-- A progressive process with locally integrable paths has a predictable representative
agreeing at Lebesgue-almost every positive time on every path. This is a time-a.e.
representative, not a fixed-time modification. -/
theorem exists_isStronglyPredictable_ae_time_of_locallyIntegrable (hH : IsStronglyProgressive ℱ H)
    (hloc : ∀ ω, LocallyIntegrable (fun s : ℝ ↦ H s.toNNReal ω) volume) :
    ∃ G : ℝ≥0 → Ω → E, IsStronglyPredictable ℱ G ∧
      ∀ ω, ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), G t.toNNReal ω = H t.toNNReal ω := by
  let ε (n : ℕ) : ℝ≥0 := 1 / (n + 1)
  let A (n : ℕ) (t : ℝ≥0) (ω : Ω) : E := (ε n : ℝ)⁻¹ •
    ((∫ s in (0 : ℝ)..t, H s.toNNReal ω) -
      ∫ s in (0 : ℝ)..(t - ε n : ℝ≥0), H s.toNNReal ω)
  have hA (n : ℕ) : IsStronglyPredictable ℱ (A n) :=
    hH.isStronglyPredictable_backwardAverage hloc (ε n)
  refine ⟨fun t ω ↦ limUnder atTop (fun n ↦ A n t ω), ?_, ?_⟩
  · let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    exact StronglyMeasurable.limUnder hA
  · intro ω
    filter_upwards [ae_restrict_of_ae (_root_.LocallyIntegrable.ae_hasDerivAt_integral (hloc ω)),
      ae_restrict_mem measurableSet_Ioi] with t ht ht0
    apply Tendsto.limUnder_eq
    have hε : Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝 0) := by
      simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
    have hpos (n : ℕ) : (0 : ℝ) < ε n := by dsimp [ε]; positivity
    have hleft : Tendsto (fun n ↦ -(ε n : ℝ)) atTop (𝓝[<] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa using hε.neg,
        Eventually.of_forall fun n ↦ neg_neg_of_pos (hpos n)⟩
    have h := (ht 0).tendsto_slope_zero_left.comp hleft
    refine h.congr' ?_
    filter_upwards [hε.eventually_lt_const ht0] with n hn
    have htε : (ε n : ℝ) ≤ t := hn.le
    have hnn : ε n ≤ t.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal t ht0.le]
      exact htε
    have hsub : ((t.toNNReal - ε n : ℝ≥0) : ℝ) = t - ε n := by
      rw [NNReal.coe_sub hnn, Real.coe_toNNReal t ht0.le]
    dsimp only [Function.comp_apply, A]
    rw [Real.coe_toNNReal t ht0.le, hsub, inv_neg, neg_smul, ← smul_neg, neg_sub]
    rfl

/-- Every real progressive process admits a predictable representative agreeing at almost
every positive time on every path. No integrability, probability measure or usual conditions
on the filtration are required. The exceptional times can depend on the path. -/
theorem exists_isStronglyPredictable_ae_time {H : ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyProgressive ℱ H) :
    ∃ G : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ G ∧
      ∀ ω, ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), G t.toNNReal ω = H t.toNNReal ω := by
  have hB : IsStronglyProgressive ℱ (fun t ω ↦ Real.arctan (H t ω)) :=
    fun t ↦ Real.continuous_arctan.comp_stronglyMeasurable (hH t)
  -- A bounded injective transform makes every path locally integrable, including paths
  -- on which the original coefficients have infinite energy.
  have hloc (ω : Ω) : LocallyIntegrable (fun s : ℝ ↦ Real.arctan (H s.toNNReal ω)) volume := by
    intro x
    let T : ℝ≥0 := (x + 1).toNNReal
    have hm : StronglyMeasurable (fun s : ℝ ↦ Real.arctan (H (min s.toNNReal T) ω)) :=
      (hB T).comp_measurable
        (((measurable_real_toNNReal.min measurable_const).subtype_mk
          (h := fun _ ↦ min_le_right _ _)).prodMk measurable_const)
    refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
    have hint : IntegrableOn (fun s : ℝ ↦ Real.arctan (H (min s.toNNReal T) ω))
        (Icc (x - 1) (x + 1)) volume :=
      (integrableOn_const (C := Real.pi / 2) isCompact_Icc.measure_ne_top).mono'
        hm.aestronglyMeasurable
        (Eventually.of_forall fun s ↦ by
          rw [Real.norm_eq_abs]
          exact (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩).le)
    apply hint.congr_fun (fun s hs ↦ ?_) measurableSet_Icc
    rw [min_eq_left (Real.toNNReal_le_toNNReal hs.2)]
  obtain ⟨G, hG, heq⟩ := hB.exists_isStronglyPredictable_ae_time_of_locallyIntegrable hloc
  refine ⟨fun t ω ↦ Real.tan (G t ω), ?_, fun ω ↦ ?_⟩
  · have ht : Measurable (fun x : ℝ ↦ Real.tan x) := by
      simp_rw [Real.tan_eq_sin_div_cos]
      exact Real.measurable_sin.div Real.measurable_cos
    exact (ht.comp hG.measurable).stronglyMeasurable
  · filter_upwards [heq ω] with t ht
    rw [ht, Real.tan_arctan]

/-- A real progressive process has one predictable representative equal to it for
time × measure almost every point on every finite horizon. The same representative works
for all horizons, and no completion or right continuity is assumed. -/
theorem exists_isStronglyPredictable_ae_prod {H : ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyProgressive ℱ H) (P : Measure Ω) [SFinite P] :
    ∃ G : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ G ∧ ∀ T : ℝ≥0,
      (fun p : ℝ × Ω ↦ G p.1.toNNReal p.2) =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod P]
        (fun p ↦ H p.1.toNNReal p.2) := by
  obtain ⟨G, hG, heq⟩ := hH.exists_isStronglyPredictable_ae_time
  refine ⟨G, hG, fun T ↦ ?_⟩
  -- Cap time at T to obtain ambient-product measurability from progressivity on [0,T].
  have hcap {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyProgressive ℱ X) :
      Measurable (fun p : ℝ × Ω ↦ X (min p.1.toNNReal T) p.2) :=
    ((hX T).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le T))).measurable.comp
      (((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk
        (h := fun _ ↦ min_le_right _ _) |>.prodMk measurable_snd)
  have hm := measurableSet_eq_fun (hcap hG.isStronglyProgressive) (hcap hH)
  have hc : (fun p : ℝ × Ω ↦ G (min p.1.toNNReal T) p.2) =ᵐ[
      (volume.restrict (Ioc 0 (T : ℝ))).prod P]
        (fun p ↦ H (min p.1.toNNReal T) p.2) := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    apply (Measure.ae_ae_comm hm).mpr
    exact Eventually.of_forall fun ω ↦ by
      have hω : ∀ᵐ t ∂volume.restrict (Ioc 0 (T : ℝ)),
          G t.toNNReal ω = H t.toNNReal ω := (heq ω).filter_mono
        (ae_mono (Measure.restrict_mono_set volume Ioc_subset_Ioi_self))
      filter_upwards [hω, ae_restrict_mem measurableSet_Ioc] with t ht htT
      have ht' : t.toNNReal ≤ T := by simpa using Real.toNNReal_le_toNNReal htT.2
      simpa only [min_eq_left ht'] using ht
  have htime : ∀ᵐ p : ℝ × Ω ∂(volume.restrict (Ioc 0 (T : ℝ))).prod P,
      p.1.toNNReal ≤ T := by
    have ht : ∀ᵐ t ∂volume.restrict (Ioc 0 (T : ℝ)), t.toNNReal ≤ T := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa using Real.toNNReal_le_toNNReal ht.2
    exact Measure.quasiMeasurePreserving_fst.ae ht
  filter_upwards [hc, htime] with p hp ht
  simpa only [min_eq_left ht] using hp

end MeasureTheory.IsStronglyProgressive
