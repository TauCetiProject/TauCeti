/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Stopping
public import Mathlib.Probability.Process.LocalProperty
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.TimeAverage

/-!
# Local Brownian Itô integral process

This file constructs the continuous, strongly progressive Brownian Itô integral process for every
`LocallyBrownianIntegrable` integrand against an almost surely continuous filtered pre-Brownian
motion on a raw filtration, characterizes the domain of Itô integrability, handles strongly
progressive inputs via predictable representatives, proves that every strongly progressive Itô
integral is a continuous local martingale, and extends stopping compatibility, interval
restrictions, and the bounded left-measurable multiplier rule to the full local domain.

Closed-level raw energy localizers `τ n := nnvolume.energyLocalizer H (n + 1)` reduce a locally
Brownian-integrable integrand `H` to `BrownianIntegrable` cutoffs `Hloc n` without augmenting the
filtration. On each stage, `TauCeti.BrownianIntegrable.exists_isItoIntegral` constructs a continuous
square-integrable martingale `U n`, and `L²` stopping compatibility
(`isItoIntegral_stoppedProcess_of_brownianIntegrable`) yields stage consistency
`stoppedProcess (U m) (τ n) ≡ᵐ[P] U n` for `n ≤ m`. Patching these stages produces a single
strongly progressive, almost surely continuous process `I` satisfying `IsItoIntegral ℱ P W H I` and
`Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P`.

## Main results

* `TauCeti.Probability.IsFilteredPreBrownianReal.exists_isItoIntegral`: against an almost surely
  continuous filtered pre-Brownian motion, every locally Brownian-integrable integrand admits a
  strongly progressive Itô integral that is a local martingale.
* `exists_isItoIntegral_iff_locallyBrownianIntegrable`: `H` admits an Itô integral if and only if
  `H` is `LocallyBrownianIntegrable`.
* `TauCeti.Probability.IsFilteredPreBrownianReal.exists_isItoIntegral_of_isStronglyProgressive`:
  every strongly progressive process with a.s. finite pathwise square energy admits a
  `LocallyBrownianIntegrable` predictable representative agreeing `(timeMeasure T).prod P`-a.e.
  on every horizon `T` together with a local-martingale Itô integral (independent of the
  representative choice by `itoIntegral_congr_progressive` / `itoIntegral_local_congr`).
* `TauCeti.Probability.IsFilteredPreBrownianReal.itoIntegral_localMartingale`: against an almost
  surely continuous filtered pre-Brownian motion, every strongly progressive Itô integral is a
  local martingale.
* `TauCeti.Probability.IsFilteredPreBrownianReal.isItoIntegral_stoppedProcess`,
  `isItoIntegral_stoppedProcess_Ioc`, `isItoIntegral_stoppedProcess_sub`,
  `isItoIntegral_ite_Ioc_mul`, and `IsItoIntegral.mul_ite_Ioc`: stopping compatibility, `(σ, τ]` and
  `(s, t]` interval restrictions, and the bounded `ℱ s`-measurable multiplier rule on the full
  local domain.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- The `n`-th closed-level raw energy localizer `nnvolume.energyLocalizer H (n + 1)`. -/
private abbrev energyLevelLocalizer (H : ℝ≥0 → Ω → ℝ) (n : ℕ) : Ω → WithTop ℝ≥0 :=
  nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)

/-- The `n`-th localized cutoff integrand `1_{[0, τ n]} · finiteEnergyCutoff H`. -/
private abbrev energyLevelCutoff (H : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) ≤ energyLevelLocalizer H n ω then nnvolume.finiteEnergyCutoff H t ω else 0

private theorem energyLevelLocalizer_mono (H : ℝ≥0 → Ω → ℝ) {n m : ℕ} (hnm : n ≤ m) (ω : Ω) :
    energyLevelLocalizer H n ω ≤ energyLevelLocalizer H m ω :=
  nnvolume.monotone_energyLocalizer H ω (add_le_add (Nat.cast_le.mpr hnm) le_rfl)

/-- If `I` has almost surely continuous paths and agrees with a sequence of localized Itô
integrals `U n` of `energyLevelCutoff H n` when stopped at `energyLevelLocalizer H n`, then `I`
is an Itô integral of `H`. -/
private theorem isItoIntegral_of_localized_stages
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : LocallyBrownianIntegrable ℱ P H)
    (hIcont : ∀ᵐ ω ∂P, Continuous (I · ω))
    {U : ℕ → ℝ≥0 → Ω → ℝ} (hUito : ∀ n, IsItoIntegral ℱ P W (energyLevelCutoff H n) (U n))
    (hIstop : ∀ n, stoppedProcess I (energyLevelLocalizer H n) ≡ᵐ[P] U n) :
    IsItoIntegral ℱ P W H I := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hloc := hH.isLocalizingSequence_energyLocalizer
  have hHloc (n : ℕ) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P) ((n : ℝ≥0) + 1)
  refine ⟨hH.isStronglyPredictable, hIcont, fun t ↦ ?_⟩
  -- Step 1: approximate each localized stage `energyLevelCutoff H n` in `L²` by a bounded simple
  -- holding within `(n + 1)⁻¹`, and transfer convergence to the integrals via isometry.
  choose m s a C _ hs ha hb hK_lt using fun n : ℕ ↦
    ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t (hHloc n).isStronglyPredictable
      ((hHloc n).memLp_timeMeasure t) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _))
  have hK_L2 : Tendsto (fun n ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (s n) (m n) (a n) p.1 p.2 -
        energyLevelCutoff H n p.1 p.2) 2 ((timeMeasure t).prod P)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
      (fun _ ↦ zero_le) fun n ↦ (hK_lt n).le
  have hK_brown (n : ℕ) : BrownianIntegrable ℱ P (Finance.simpleHolding (s n) (m n) (a n)) :=
    brownianIntegrable_iff_memLp_predictableMeasure.mpr
      ⟨Finance.isStronglyPredictable_simpleHolding (ha n),
        fun T ↦ Finance.memLp_simpleHolding_predictableMeasure (ha n)
          (Finance.memLp_of_bound_stronglyMeasurable (ha n) (hb n)) T⟩
  have hK_I_L2 : Tendsto
      (fun n ↦ eLpNorm (Finance.simpleGains (s n) (m n) (a n) W t - U n t) 2 P) atTop (𝓝 0) :=
    hK_L2.congr fun n ↦
      (((isItoIntegral_simpleGains hcont (hs n).monotoneOn (ha n)).sub (hUito n)).eLpNorm_eq hW
        ((hK_brown n).sub (hHloc n)) t).symm
  -- Step 2: the bad events `B n = {τ n ≤ t}` decrease to a null set as `n → ∞`.
  let B (n : ℕ) : Set Ω := {ω | energyLevelLocalizer H n ω ≤ (t : WithTop ℝ≥0)}
  have hB_inter : P (⋂ n, B n) = 0 :=
    measure_mono_null (t := {ω | ¬ Tendsto (energyLevelLocalizer H · ω) atTop (𝓝 ⊤)})
      (fun ω hω hlim ↦ by
        obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).exists
        exact not_lt_of_ge (Set.mem_iInter.mp hω n) hn) hloc.tendsto_top
  have hB_lim : Tendsto (fun n ↦ P (B n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hB_inter] using tendsto_measure_iInter_atTop (s := B)
      (fun n ↦ (ℱ.le t _ (hloc.isStoppingTime n t)).nullMeasurableSet)
      (fun _ _ hnm ω hω ↦ (energyLevelLocalizer_mono H hnm ω).trans hω) ⟨0, measure_ne_top P _⟩
  -- Step 3: off `B n` and a fixed null set, `I t = U n t` and the pathwise energies agree.
  have hgood : ∀ᵐ ω ∂P, ∀ n, ω ∉ B n → I t ω = U n t ω ∧
        (∫⁻ s', ‖Finance.simpleHolding (s n) (m n) (a n) s' ω - H s' ω‖ₑ ^ 2 ∂timeMeasure t) =
          ∫⁻ s', ‖Finance.simpleHolding (s n) (m n) (a n) s' ω -
            energyLevelCutoff H n s' ω‖ₑ ^ 2 ∂timeMeasure t := by
    filter_upwards [hH.ae_accumulatedEnergy_lt_top, ae_all_iff.mpr hIstop] with ω hfin hst n hB
    have ht_lt : (t : WithTop ℝ≥0) < energyLevelLocalizer H n ω := lt_of_not_ge hB
    refine ⟨by simpa only [stoppedProcess_eq_of_le ht_lt.le] using hst n t,
      lintegral_congr_ae ((ae_mem_Ioc_timeMeasure t).mono fun s' hs' ↦ ?_)⟩
    simp only [energyLevelCutoff, (WithTop.coe_le_coe.mpr hs'.2).trans ht_lt.le, ite_true,
      nnvolume.finiteEnergyCutoff_eqOn (hfin t) hs'.2]
  -- Step 4: transfer energy and integral convergence in probability via the vanishing bad sets.
  have hunion {A C : ℕ → Set Ω} (hC : Tendsto (fun n ↦ P (C n)) atTop (𝓝 0))
      (hsub : ∀ n, A n ≤ᵐ[P] (B n ∪ C n : Set Ω)) :
      Tendsto (fun n ↦ P (A n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using hB_lim.add hC) (fun _ ↦ zero_le) fun n ↦
        (measure_mono_ae (hsub n)).trans (measure_union_le (B n) (C n))
  refine ⟨m, s, a, fun n ↦ (hs n).monotoneOn, ha,
    fun ε hε ↦ hunion
      (tendsto_measure_le_lintegral_enorm_sq_sub
        (fun n ↦ Finance.isStronglyPredictable_simpleHolding (ha n))
        (fun n ↦ (hHloc n).isStronglyPredictable) hK_L2 ε hε)
      fun n ↦ hgood.mono fun ω hω hA ↦ (Classical.em (ω ∈ B n)).imp id fun hB ↦ by
        simpa only [Set.mem_ofPred_eq, ← (hω n hB).2] using hA,
    fun ε hε ↦ hunion
      ((tendstoInMeasure_of_tendsto_eLpNorm (p := 2)
        (f := fun n ↦ Finance.simpleGains (s n) (m n) (a n) W t - U n t)
        (g := 0) (by norm_num) (by simpa only [sub_zero] using hK_I_L2)) ε hε)
      fun n ↦ hgood.mono fun ω hω hA ↦ (Classical.em (ω ∈ B n)).imp id fun hB ↦ by
        simpa only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, eDist_eq_eNorm_sub,
          sub_zero, (hω n hB).1] using hA⟩

/-- Helper: construct a strongly progressive, almost surely continuous local-martingale Itô
integral of a `LocallyBrownianIntegrable` integrand `H` against an almost surely continuous `W`,
together with the identification of its stages stopped at the closed-level raw energy
localizers. -/
private theorem exists_isItoIntegral_aux
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyProgressive ℱ I ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P ∧
      ∀ n, IsItoIntegral ℱ P W (energyLevelCutoff H n)
        (stoppedProcess I (energyLevelLocalizer H n)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hloc := hH.isLocalizingSequence_energyLocalizer
  have hHloc (n : ℕ) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P) ((n : ℝ≥0) + 1)
  -- Step 1: build the localized `L²` martingale Itô integrals `U n` for each cutoff stage.
  choose U hUito hUpred hUmart using fun n ↦
    (hHloc n).exists_isItoIntegral hW hcont
  -- Step 2: verify stage consistency `stoppedProcess (U m) (τ n) ≡ᵐ[P] U n` for `n ≤ m`.
  have hcompat (n m : ℕ) (hnm : n ≤ m) :
      stoppedProcess (U m) (energyLevelLocalizer H n) ≡ᵐ[P] U n := by
    have hstop := hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont (hHloc m) (hUito m)
      (hloc.isStoppingTime n)
    have hEq : (fun (t : ℝ≥0) ω ↦ if (t : WithTop ℝ≥0) ≤ energyLevelLocalizer H n ω then
        energyLevelCutoff H m t ω else 0) =
        fun (t : ℝ≥0) ω ↦ if (t : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω then
          nnvolume.finiteEnergyCutoff H t ω else 0 := by
      ext t ω; dsimp only [energyLevelCutoff]
      by_cases ht : (t : WithTop ℝ≥0) ≤ energyLevelLocalizer H n ω
      · simp only [ht, ht.trans (energyLevelLocalizer_mono H hnm ω), ite_true]
      · simp only [ht, ite_false]
    exact isItoIntegral_unique hW (by rw [← hEq]; exact hstop) (hUito n)
  -- Step 3: patch the stages into a single strongly progressive continuous process `I`.
  obtain ⟨I, hIprog, hIcont, hIstop⟩ :=
    exists_isStronglyProgressive_patch_stoppedProcess hloc.tendsto_top
      (fun n ↦ (hUpred n).isStronglyProgressive) (fun n ↦ (hUito n).ae_continuous) hcompat
  have hIloc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P :=
    hIprog.locally_martingale_of_ae_stopped_eq hloc hUmart fun n t ↦ by
      -- Every closed-level energy localizer is strictly positive, so the `{⊥ < τ n}` indicator is
      -- `I`.
      have hind :
          (fun s ↦ {ω | (⊥ : WithTop ℝ≥0) < energyLevelLocalizer H n ω}.indicator (I s)) = I :=
        funext fun s ↦ funext fun ω ↦
          Set.indicator_of_mem (nnvolume.energyLocalizer_pos H (by positivity) ω) _
      rw [hind]
      exact (hIstop n).mono fun ω hω ↦ (hω t).symm
  exact ⟨I, hW.isItoIntegral_of_localized_stages hcont hH hIcont hUito hIstop,
    hIprog, hIloc, fun n ↦ (hUito n).congr (hIstop n).symm⟩

/-- **Existence of the continuous local Brownian Itô integral process.** Against an almost surely
continuous filtered pre-Brownian motion `W`, every `LocallyBrownianIntegrable` integrand on a raw
filtration admits a strongly progressive Itô integral process which is a local martingale. Neither
completeness nor right continuity of the filtration is required. -/
theorem exists_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω)) {H : ℝ≥0 → Ω → ℝ} (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyProgressive ℱ I ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P :=
  let ⟨I, hIito, hIprog, hIloc, _⟩ := hW.exists_isItoIntegral_aux hcont hH
  ⟨I, hIito, hIprog, hIloc⟩

/-- **Domain characterization for Brownian Itô integration.** Against an almost surely continuous
filtered pre-Brownian motion `W`, a process `H` admits an Itô integral if and only if `H` is
`LocallyBrownianIntegrable`. -/
theorem exists_isItoIntegral_iff_locallyBrownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H : ℝ≥0 → Ω → ℝ} :
    (∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I) ↔ LocallyBrownianIntegrable ℱ P H :=
  ⟨fun ⟨_, hI⟩ ↦ hI.locallyBrownianIntegrable,
    fun hH ↦ let ⟨I, hI, _, _⟩ := hW.exists_isItoIntegral hcont hH; ⟨I, hI⟩⟩

/-- **Existence of the Brownian Itô integral for a strongly progressive integrand.** Against an
almost surely continuous filtered pre-Brownian motion `W`, every strongly progressive process `H`
with almost surely finite pathwise square energy on every finite horizon admits a
`LocallyBrownianIntegrable` predictable representative `H'` agreeing with `H` almost everywhere with
respect to `(timeMeasure T).prod P` on every finite horizon `T`, together with a strongly
progressive local-martingale Itô integral `I` of `H'`. -/
theorem exists_isItoIntegral_of_isStronglyProgressive
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyProgressive ℱ H)
    (hfin : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, MemLp (fun t ↦ H t ω) 2 (timeMeasure T)) :
    ∃ H' I : ℝ≥0 → Ω → ℝ,
      LocallyBrownianIntegrable ℱ P H' ∧
      (∀ T : ℝ≥0, Function.uncurry H' =ᵐ[(timeMeasure T).prod P] Function.uncurry H) ∧
      IsItoIntegral ℱ P W H' I ∧ IsStronglyProgressive ℱ I ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨H', hH'pred, heq⟩ := hH.exists_isStronglyPredictable_ae_time
  -- Transfer pathwise Lebesgue-a.e. agreement to `timeMeasure T` on every path `ω`.
  have hpath (ω : Ω) (T : ℝ≥0) : (fun t ↦ H' t ω) =ᵐ[timeMeasure T] (fun t ↦ H t ω) := by
    have hω : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) T), H' x.toNNReal ω = H x.toNNReal ω :=
      (heq ω).filter_mono (ae_mono (Measure.restrict_mono_set volume Ioc_subset_Ioi_self))
    change ∀ᵐ t ∂timeMeasure T, H' t ω = H t ω
    rw [ae_iff] at hω ⊢
    rw [timeMeasure_def, ← NNReal.comap_volume_restrict_Ioc,
      (NNReal.isClosedEmbedding_coe.measurableEmbedding).comap_apply]
    refine measure_mono_null (fun x hx ↦ ?_) hω
    rcases hx with ⟨t, ht, rfl⟩
    simpa using ht
  have hH'loc : LocallyBrownianIntegrable ℱ P H' := by
    refine ⟨hH'pred, ?_⟩
    filter_upwards [hfin] with ω hω T
    rw [NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def]
    exact (hω T).ae_eq (hpath ω T).symm
  -- Cap time at `T` so product measurability comes from progressivity on `[0, T]`.
  have hprod (T : ℝ≥0) :
      Function.uncurry H' =ᵐ[(timeMeasure T).prod P] Function.uncurry H := by
    have hcap {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyProgressive ℱ X) :
        Measurable (fun p : ℝ≥0 × Ω ↦ X (min p.1 T) p.2) :=
      ((hX T).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le T))).measurable.comp
        (((measurable_fst.min measurable_const).subtype_mk
          (h := fun _ ↦ min_le_right _ _)).prodMk measurable_snd)
    have hm := measurableSet_eq_fun (hcap hH'pred.isStronglyProgressive) (hcap hH)
    have hc : (fun p : ℝ≥0 × Ω ↦ H' (min p.1 T) p.2) =ᵐ[(timeMeasure T).prod P]
        (fun p ↦ H (min p.1 T) p.2) := by
      change ∀ᵐ p : ℝ≥0 × Ω ∂(timeMeasure T).prod P, H' (min p.1 T) p.2 = H (min p.1 T) p.2
      rw [Measure.ae_prod_iff_ae_ae hm, Measure.ae_ae_comm hm]
      exact Eventually.of_forall fun ω ↦ by
        filter_upwards [hpath ω T, ae_mem_Ioc_timeMeasure T] with t ht htT
        simp only [min_eq_left htT.2, ht]
    have htime : ∀ᵐ p : ℝ≥0 × Ω ∂(timeMeasure T).prod P, p.1 ≤ T :=
      (Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := P)).ae
        ((ae_mem_Ioc_timeMeasure T).mono fun _ h ↦ h.2)
    filter_upwards [hc, htime] with p hp ht
    simpa only [Function.uncurry, min_eq_left ht] using hp
  obtain ⟨I, hIito, hIprog, hIloc⟩ := hW.exists_isItoIntegral hcont hH'loc
  exact ⟨H', I, hH'loc, hprod, hIito, hIprog, hIloc⟩

/-- **Representative independence for progressive integrands.** Any two Itô integrals `I₁` and
`I₂` associated with predictable representatives `H₁` and `H₂` that agree
`(timeMeasure T).prod P`-a.e. with a common process `H` on every finite horizon are
indistinguishable. -/
theorem itoIntegral_congr_progressive (hW : IsFilteredPreBrownianReal ℱ W P)
    {H H₁ H₂ I₁ I₂ : ℝ≥0 → Ω → ℝ}
    (hH₁ : ∀ T : ℝ≥0, Function.uncurry H₁ =ᵐ[(timeMeasure T).prod P] Function.uncurry H)
    (hH₂ : ∀ T : ℝ≥0, Function.uncurry H₂ =ᵐ[(timeMeasure T).prod P] Function.uncurry H)
    (hI₁ : IsItoIntegral ℱ P W H₁ I₁) (hI₂ : IsItoIntegral ℱ P W H₂ I₂) :
    I₁ ≡ᵐ[P] I₂ :=
  hW.itoIntegral_local_congr hI₁ hI₂ fun T ↦ (hH₁ T).trans (hH₂ T).symm

/-- **Local martingale property of Brownian Itô integrals.** Against an almost surely continuous
filtered pre-Brownian motion `W`, every strongly progressive Itô integral is a local martingale on
the raw filtration. -/
theorem itoIntegral_localMartingale (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω)) {H I : ℝ≥0 → Ω → ℝ}
    (hI : IsItoIntegral ℱ P W H I) (hProg : IsStronglyProgressive ℱ I) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P :=
  let ⟨_, hJito, _, hJloc⟩ := hW.exists_isItoIntegral hcont hI.locallyBrownianIntegrable
  hProg.locally_martingale_of_indist hJloc (isItoIntegral_unique hW hJito hI)

/-- **Stopping compatibility for local Brownian Itô integrals.** Against an almost surely
continuous filtered pre-Brownian motion `W`, stopping any Itô integral at any stopping time `σ` on
the raw filtration produces an Itô integral of the cutoff integrand `1_{[0, σ]} · H`. -/
theorem isItoIntegral_stoppedProcess (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω)) {H I : ℝ≥0 → Ω → ℝ}
    (hI : IsItoIntegral ℱ P W H I) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (stoppedProcess I σ) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hH : LocallyBrownianIntegrable ℱ P H := hI.locallyBrownianIntegrable
  let Hσ : ℝ≥0 → Ω → ℝ := fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0
  have hHσ : LocallyBrownianIntegrable ℱ P Hσ := hH.ite_le hσ
  -- Step 1: obtain localized `L²` Itô integrals for `I` and for an auxiliary integral `J` of `Hσ`.
  obtain ⟨I₀, hI₀ito, -, -, hI₀stop⟩ := hW.exists_isItoIntegral_aux hcont hH
  have hIstop (n : ℕ) :
      IsItoIntegral ℱ P W (energyLevelCutoff H n) (stoppedProcess I (energyLevelLocalizer H n)) :=
    (hI₀stop n).congr
      ((isItoIntegral_unique hW hI₀ito hI).stoppedProcess (energyLevelLocalizer H n))
  obtain ⟨J, hJito, -, -, hJstop⟩ := hW.exists_isItoIntegral_aux hcont hHσ
  -- Step 2: compare `stoppedProcess I σ` and `J` along the joint localizers
  -- `η n = min (τ_H n) (τ_{Hσ} n)`.
  let η := min (energyLevelLocalizer H) (energyLevelLocalizer Hσ)
  have hη_top : ∀ᵐ ω ∂P, Tendsto (η · ω) atTop (𝓝 ⊤) :=
    (hH.isLocalizingSequence_energyLocalizer.min
      hHσ.isLocalizingSequence_energyLocalizer).tendsto_top
  have hcompat (n : ℕ) :
      stoppedProcess (stoppedProcess I σ) (η n) ≡ᵐ[P] stoppedProcess J (η n) := by
    have hLHS_ito : IsItoIntegral ℱ P W
        (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ min (σ ω) (energyLevelLocalizer Hσ n ω) then
          energyLevelCutoff H n t ω else 0) (stoppedProcess (stoppedProcess I σ) (η n)) := by
      -- Reassociate `stoppedProcess (stoppedProcess I σ) (min τ_H τ_{Hσ})` by `min` commutativity.
      have hLHS_eq : stoppedProcess (stoppedProcess I σ) (η n) =
          stoppedProcess (stoppedProcess I (energyLevelLocalizer H n))
            (fun ω ↦ min (σ ω) (energyLevelLocalizer Hσ n ω)) := by
        rw [stoppedProcess_stoppedProcess', stoppedProcess_stoppedProcess']
        congr 1; ext ω; ac_rfl
      rw [hLHS_eq]
      exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont
        (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
        (hIstop n) (hσ.min (hHσ.isLocalizingSequence_energyLocalizer.isStoppingTime n))
    have hRHS_ito : IsItoIntegral ℱ P W
        (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ energyLevelLocalizer H n ω then
          energyLevelCutoff Hσ n t ω else 0) (stoppedProcess J (η n)) := by
      -- Reassociate `stoppedProcess J (min τ_H τ_{Hσ})` as `J` stopped at `τ_{Hσ}` then
      -- `τ_H`.
      have hRHS_eq : stoppedProcess J (η n) =
          stoppedProcess (stoppedProcess J (energyLevelLocalizer Hσ n))
            (energyLevelLocalizer H n) :=
        stoppedProcess_stoppedProcess'.symm
      rw [hRHS_eq]
      exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont
        (hHσ.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
        (hJstop n) (hH.isLocalizingSequence_energyLocalizer.isStoppingTime n)
    refine hW.itoIntegral_local_congr hLHS_ito hRHS_ito fun T ↦ ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := P)).ae
        ((ae_mem_Ioc_timeMeasure T).mono fun _ h ↦ h.2),
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).ae
        (hH.ae_accumulatedEnergy_lt_top.mono fun _ h ↦ h T),
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).ae
        (hHσ.ae_accumulatedEnergy_lt_top.mono fun _ h ↦ h T)] with ⟨t, ω⟩ ht hfinH hfinHσ
    dsimp only [Function.uncurry_apply_pair, energyLevelCutoff] at ht hfinH hfinHσ ⊢
    simp only [nnvolume.finiteEnergyCutoff_eqOn hfinH ht,
      nnvolume.finiteEnergyCutoff_eqOn hfinHσ ht, Hσ, le_min_iff]
    split_ifs <;> first | rfl | tauto
  -- Step 3: conclude by patching `stoppedProcess I σ ≡ᵐ[P] J` from `η n → ∞`.
  exact hJito.congr (indist_of_ae_eq_before_lifetimes hη_top fun n ↦
    (hcompat n).mono fun ω hω t ht ↦ by simpa only [stoppedProcess_eq_of_le ht] using hω t).symm

/-- **Stochastic-interval restriction for local Brownian Itô integrals.** For stopping times
`σ ≤ τ`, the difference `stoppedProcess I τ - stoppedProcess I σ` is an Itô integral of the
`(σ, τ]` restriction `1_{(σ, τ]} · H`. -/
theorem isItoIntegral_stoppedProcess_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω)) {H I : ℝ≥0 → Ω → ℝ}
    (hI : IsItoIntegral ℱ P W H I) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) :
    IsItoIntegral ℱ P W
      (fun u ω ↦ if σ ω < u ∧ (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0)
      (stoppedProcess I τ - stoppedProcess I σ) := by
  have hH_eq : (fun (u : ℝ≥0) ω ↦ if σ ω < u ∧ (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) =
      fun (u : ℝ≥0) ω ↦ (if (u : WithTop ℝ≥0) ≤ τ ω then H u ω else 0) -
        (if (u : WithTop ℝ≥0) ≤ σ ω then H u ω else 0) := by
    ext u ω
    by_cases h1 : (u : WithTop ℝ≥0) ≤ σ ω <;> by_cases h2 : (u : WithTop ℝ≥0) ≤ τ ω
    · rw [ite_eq_right (fun h ↦ h1.not_gt h.1), ite_eq_left h2, ite_eq_left h1, sub_self]
    · exact absurd (h1.trans (hστ ω)) h2
    · rw [ite_eq_left ⟨lt_of_not_ge h1, h2⟩, ite_eq_left h2, ite_eq_right h1, sub_zero]
    · rw [ite_eq_right (fun h ↦ h2 h.2), ite_eq_right h2, ite_eq_right h1, sub_self]
  rw [hH_eq]
  exact (hW.isItoIntegral_stoppedProcess hcont hI hτ).sub
    (hW.isItoIntegral_stoppedProcess hcont hI hσ)

/-- **Deterministic-interval restriction for local Brownian Itô integrals.** For `s ≤ t`, the
difference of stopped integrals `u ↦ I (min u t) - I (min u s)` is an Itô integral of the
`(s, t]` restriction `1_{(s, t]} · H`. -/
theorem isItoIntegral_stoppedProcess_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω)) {H I : ℝ≥0 → Ω → ℝ}
    (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t) :
    IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then H u ω else 0)
      (fun u ω ↦ I (min u t) ω - I (min u s) ω) := by
  have hH_eq : (fun (u : ℝ≥0) ω ↦ if s < u ∧ u ≤ t then H u ω else 0) =
      fun (u : ℝ≥0) ω ↦ if (s : WithTop ℝ≥0) < u ∧ (u : WithTop ℝ≥0) ≤ t then H u ω else 0 := by
    ext u ω
    simp only [WithTop.coe_lt_coe, WithTop.coe_le_coe]
  rw [hH_eq]
  exact (hW.isItoIntegral_stoppedProcess_Ioc hcont hI
    (isStoppingTime_const ℱ s) (isStoppingTime_const ℱ t)
    fun _ ↦ WithTop.coe_le_coe.mpr hst).congr (.of_forall fun ω u ↦ by
      simp only [Pi.sub_apply, stoppedProcess, ← WithTop.coe_min]
      rfl)

/-- **Bounded left-measurable multiplier rule for local interval integrals.** For `s ≤ t`, a
bounded `ℱ s`-measurable random variable `ξ` factors out of the `(s, t]` Itô integral:
`u ↦ ξ · (I (min u t) - I (min u s))` is an Itô integral of `1_{(s, t]} · ξ · H`. -/
theorem isItoIntegral_ite_Ioc_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω)) {H I : ℝ≥0 → Ω → ℝ}
    (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) {Cξ : ℝ} (hCξ : ∀ ω, ‖ξ ω‖ ≤ Cξ) :
    IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0)
      (fun u ω ↦ ξ ω * (I (min u t) ω - I (min u s) ω)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hH : LocallyBrownianIntegrable ℱ P H := hI.locallyBrownianIntegrable
  let K : ℝ≥0 → Ω → ℝ := fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0
  have hξ_pred : IsStronglyPredictable ℱ (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω else 0) := by
    change StronglyMeasurable[ℱ.predictable]
      (Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω else 0)
    rw [show (Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω else 0) =
        (fun p : ℝ≥0 × Ω ↦ (Set.Ioc s t).indicator (fun _ ↦ ξ p.2) p.1) from by
      ext ⟨u, ω⟩; simp [Set.indicator_apply]]
    exact ℱ.stronglyMeasurable_indicator_Ioc_predictable s t hξ
  have hK_pred : IsStronglyPredictable ℱ K := by
    convert hξ_pred.mul hH.isStronglyPredictable using 2 with u ω
    dsimp only [K]; split_ifs <;> simp
  have hK : LocallyBrownianIntegrable ℱ P K := by
    refine ⟨hK_pred, ?_⟩
    filter_upwards [hH.ae_memLp] with ω hω T
    refine ((hω T).const_mul (max Cξ 0)).mono
      ((hK_pred.stronglyMeasurable_section ω).mono le_rfl).aestronglyMeasurable
      (.of_forall fun u ↦ ?_)
    dsimp only [K]
    split_ifs
    · rw [norm_mul, norm_mul, Real.norm_of_nonneg (le_max_right Cξ 0)]
      exact mul_le_mul_of_nonneg_right ((hCξ ω).trans (le_max_left _ _)) (norm_nonneg _)
    · simp only [norm_zero, norm_mul]; positivity
  -- Step 1: obtain localized `L²` Itô integrals for `I` and for an auxiliary integral `J` of `K`.
  obtain ⟨I₀, hI₀ito, -, -, hI₀stop⟩ := hW.exists_isItoIntegral_aux hcont hH
  have hIstop (n : ℕ) :
      IsItoIntegral ℱ P W (energyLevelCutoff H n) (stoppedProcess I (energyLevelLocalizer H n)) :=
    (hI₀stop n).congr
      ((isItoIntegral_unique hW hI₀ito hI).stoppedProcess (energyLevelLocalizer H n))
  obtain ⟨J, hJito, -, -, hJstop⟩ := hW.exists_isItoIntegral_aux hcont hK
  -- Step 2: compare `M` and `J` along the joint localizers `η n = min (τ_H n) (τ_K n)`.
  let M : ℝ≥0 → Ω → ℝ := fun u ω ↦ ξ ω * (I (min u t) ω - I (min u s) ω)
  let η := min (energyLevelLocalizer H) (energyLevelLocalizer K)
  have hη_top : ∀ᵐ ω ∂P, Tendsto (η · ω) atTop (𝓝 ⊤) :=
    (hH.isLocalizingSequence_energyLocalizer.min
      hK.isLocalizingSequence_energyLocalizer).tendsto_top
  have hcompat (n : ℕ) : stoppedProcess M (η n) ≡ᵐ[P] stoppedProcess J (η n) := by
    let M_n : ℝ≥0 → Ω → ℝ := fun u ω ↦ ξ ω *
      (stoppedProcess I (energyLevelLocalizer H n) (min u t) ω -
        stoppedProcess I (energyLevelLocalizer H n) (min u s) ω)
    have hM_n_ito : IsItoIntegral ℱ P W
        (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * energyLevelCutoff H n u ω else 0) M_n :=
      hW.isItoIntegral_ite_Ioc_mul_of_brownianIntegrable hcont
        (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
        (hIstop n) hst hξ hCξ
    have hLHS_eq : stoppedProcess M (η n) = stoppedProcess M_n (energyLevelLocalizer K n) := by
      ext u ω
      simp only [stoppedProcess, M, M_n, η, Pi.inf_apply]
      have hmin_coe (u₀ : ℝ≥0) (a : WithTop ℝ≥0) :
          ((min (u₀ : WithTop ℝ≥0) a).untopA : WithTop ℝ≥0) = min (u₀ : WithTop ℝ≥0) a := by
        induction a using WithTop.recTopCoe <;> rfl
      have hmin3 (a b : WithTop ℝ≥0) (x y : ℝ≥0) :
          min (min (x : WithTop ℝ≥0) (min a b)).untopA y =
            (min (↑(min (min (x : WithTop ℝ≥0) b).untopA y) : WithTop ℝ≥0) a).untopA := by
        rw [← WithTop.coe_inj, WithTop.coe_min, hmin_coe, hmin_coe, WithTop.coe_min, hmin_coe]
        ac_rfl
      rw [hmin3, hmin3]
    have hK_n : BrownianIntegrable ℱ P
        (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * energyLevelCutoff H n u ω else 0) := by
      rw [show (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * energyLevelCutoff H n u ω else 0) =
          (fun u ω ↦ energyLevelCutoff H n u ω * if s < u ∧ u ≤ t then ξ ω else 0) from by
        ext u ω; split_ifs <;> ring]
      exact (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer
        (P := P) ((n : ℝ≥0) + 1)).mul_of_bound hξ_pred (max Cξ 0) fun u ω ↦ by
          split_ifs
          · exact (hCξ ω).trans (le_max_left _ _)
          · simpa only [norm_zero] using le_max_right Cξ 0
    have hLHS_ito : IsItoIntegral ℱ P W
        (fun u ω ↦ if (u : WithTop ℝ≥0) ≤ energyLevelLocalizer K n ω then
          (if s < u ∧ u ≤ t then ξ ω * energyLevelCutoff H n u ω else 0) else 0)
        (stoppedProcess M (η n)) := by
      rw [hLHS_eq]
      exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont
        hK_n hM_n_ito (hK.isLocalizingSequence_energyLocalizer.isStoppingTime n)
    have hRHS_ito : IsItoIntegral ℱ P W
        (fun u ω ↦ if (u : WithTop ℝ≥0) ≤ energyLevelLocalizer H n ω then
          energyLevelCutoff K n u ω else 0) (stoppedProcess J (η n)) := by
      have hRHS_eq : stoppedProcess J (η n) =
          stoppedProcess (stoppedProcess J (energyLevelLocalizer K n))
            (energyLevelLocalizer H n) :=
        stoppedProcess_stoppedProcess'.symm
      rw [hRHS_eq]
      exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont
        (hK.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
        (hJstop n) (hH.isLocalizingSequence_energyLocalizer.isStoppingTime n)
    refine hW.itoIntegral_local_congr hLHS_ito hRHS_ito fun T ↦ ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := P)).ae
        ((ae_mem_Ioc_timeMeasure T).mono fun _ h ↦ h.2),
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).ae
        (hH.ae_accumulatedEnergy_lt_top.mono fun _ h ↦ h T),
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).ae
        (hK.ae_accumulatedEnergy_lt_top.mono fun _ h ↦ h T)] with ⟨u, ω⟩ hu hfinH hfinK
    dsimp only [Function.uncurry_apply_pair, energyLevelCutoff] at hu hfinH hfinK ⊢
    simp only [nnvolume.finiteEnergyCutoff_eqOn hfinH hu,
      nnvolume.finiteEnergyCutoff_eqOn hfinK hu, K]
    split_ifs <;> first | rfl | simp
  -- Step 3: conclude by patching `M ≡ᵐ[P] J` from `η n → ∞`.
  exact hJito.congr (indist_of_ae_eq_before_lifetimes hη_top fun n ↦
    (hcompat n).mono fun ω hω u hu ↦ by simpa only [stoppedProcess_eq_of_le hu] using hω u).symm

/-- **Bounded left-measurable multiplier rule for local interval integrals** stated directly for
any Itô integral `J` of the `(s, t]` cutoff `1_{(s, t]} · H`. -/
theorem _root_.TauCeti.Probability.IsItoIntegral.mul_ite_Ioc
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H J : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t)
    (hJ : IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then H u ω else 0) J)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) {Cξ : ℝ} (hCξ : ∀ ω, ‖ξ ω‖ ≤ Cξ) :
    IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0)
      (fun u ω ↦ ξ ω * J u ω) := by
  have hJs : stoppedProcess J (fun _ ↦ (s : WithTop ℝ≥0)) ≡ᵐ[P] 0 := by
    have hstop := hW.isItoIntegral_stoppedProcess hcont hJ (isStoppingTime_const ℱ s)
    have hzero : (fun (u : ℝ≥0) ω ↦ if (u : WithTop ℝ≥0) ≤ s then
        (if s < u ∧ u ≤ t then H u ω else 0) else 0) = 0 := by
      ext u ω
      by_cases h1 : (u : WithTop ℝ≥0) ≤ s <;> by_cases h2 : s < u ∧ u ≤ t
      · exact absurd (WithTop.coe_le_coe.mp h1) h2.1.not_ge
      · rw [ite_eq_left h1, ite_eq_right (fun h ↦ h2 h)]; rfl
      · rw [ite_eq_right h1]; rfl
      · rw [ite_eq_right h1]; rfl
    rw [hzero] at hstop
    exact isItoIntegral_unique hW hstop (IsItoIntegral.zero ℱ P W)
  have hJt : stoppedProcess J (fun _ ↦ (t : WithTop ℝ≥0)) ≡ᵐ[P] J := by
    have hstop := hW.isItoIntegral_stoppedProcess hcont hJ (isStoppingTime_const ℱ t)
    have hid : (fun (u : ℝ≥0) ω ↦ if (u : WithTop ℝ≥0) ≤ t then
        (if s < u ∧ u ≤ t then H u ω else 0) else 0) =
        fun (u : ℝ≥0) ω ↦ if s < u ∧ u ≤ t then H u ω else 0 := by
      ext u ω
      by_cases h1 : (u : WithTop ℝ≥0) ≤ t <;> by_cases h2 : s < u ∧ u ≤ t
      · rw [ite_eq_left h1]
      · rw [ite_eq_left h1]
      · exact absurd (WithTop.coe_le_coe.mpr h2.2) h1
      · rw [ite_eq_right h1, ite_eq_right (fun h ↦ h2 h)]
    rw [hid] at hstop
    exact isItoIntegral_unique hW hstop hJ
  have hmul := hW.isItoIntegral_ite_Ioc_mul hcont hJ hst hξ hCξ
  have hK : (fun (u : ℝ≥0) ω ↦ if s < u ∧ u ≤ t then
      ξ ω * (if s < u ∧ u ≤ t then H u ω else 0) else 0) =
      fun (u : ℝ≥0) ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0 := by
    ext u ω
    by_cases h : s < u ∧ u ≤ t <;> simp [h]
  rw [hK] at hmul
  refine hmul.congr ?_
  filter_upwards [hJs, hJt] with ω hsω htω u
  have hJu : J (min u t) ω = J u ω := by
    have h := htω u
    simp only [stoppedProcess, ← WithTop.coe_min] at h
    exact h
  have hJs0 : J (min u s) ω = 0 := by
    have h := hsω u
    simp only [stoppedProcess, ← WithTop.coe_min, Pi.zero_apply] at h
    exact h
  rw [hJu, hJs0, sub_zero]

end TauCeti.Probability.IsFilteredPreBrownianReal
