/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Stopping
public import Mathlib.Probability.Process.LocalProperty
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.Probability.BrownianMotion.Integral.Continuous
import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
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
integral is a continuous local martingale, compares raw-filtration integrals under filtration
enlargements, and extends stopping compatibility, interval restrictions, and the bounded
left-measurable multiplier rule to the full local domain.

Closed-level raw energy localizers `τ n := nnvolume.energyLocalizer H (n + 1)` reduce a locally
Brownian-integrable integrand `H` to `BrownianIntegrable` cutoffs `Hloc n` without augmenting the
filtration. On each stage, `TauCeti.BrownianIntegrable.exists_isItoIntegral` constructs a continuous
square-integrable martingale `U n`, and `L²` stopping compatibility yields stage consistency
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
* `itoIntegral_congr_filtration`: uniqueness comparison under filtration enlargements.
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

private theorem isStronglyPredictable_ite_Ioc {s t : ℝ≥0} {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsStronglyPredictable ℱ (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω else 0) := by
  have hind : (Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω else 0) =
      fun p : ℝ≥0 × Ω ↦ (Set.Ioc s t).indicator (fun _ ↦ ξ p.2) p.1 := by
    ext ⟨u, ω⟩
    simp only [Function.uncurry_apply_pair, Set.indicator_apply, Set.mem_Ioc]
  rw [IsStronglyPredictable, hind]
  exact ℱ.stronglyMeasurable_indicator_Ioc_predictable s t hξ

private theorem ite_Ioc_mul_eq (s t : ℝ≥0) (ξ : Ω → ℝ) (H : ℝ≥0 → Ω → ℝ) :
    (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0) =
      (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω else 0) * H := by
  ext u ω
  simp only [Pi.mul_apply, ite_mul, zero_mul]

/-- Evaluating `stoppedProcess` at a constant finite stopping time `t` reduces to `I (min u t)`. -/
private theorem stoppedProcess_const_time (I : ℝ≥0 → Ω → ℝ) (t u : ℝ≥0) (ω : Ω) :
    stoppedProcess I (fun _ ↦ (t : WithTop ℝ≥0)) u ω = I (min u t) ω := by
  rw [stoppedProcess, ← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
    WithTop.untop_coe]

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
  refine isItoIntegral_of_approx_simpleHolding hH.isStronglyPredictable hIcont fun t ↦ ?_
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

/-- **Internal `L²` stage lemma:** stopping an Itô integral of a `BrownianIntegrable` integrand
at any stopping time `τ` produces an Itô integral of the cutoff integrand `1_{[0, τ]} · H`. -/
private theorem isItoIntegral_stoppedProcess_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (stoppedProcess I τ) := by
  obtain ⟨J, hJito, -, -⟩ := (hH.ite_le hτ).exists_isItoIntegral hW hcont
  exact hJito.congr (TauCeti.indist_of_ae_continuous
    (hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess) hJito.ae_continuous fun T ↦
      (hW.stoppedProcess_ae_eq_l2Integral hcont hH hI hτ T).trans
        (hW.ae_eq_l2Integral_of_isItoIntegral (hH.ite_le hτ) hJito T).symm).symm

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
  obtain ⟨H', hH'pred, hprod_real⟩ := hH.exists_isStronglyPredictable_ae_prod P
  have hprod (T : ℝ≥0) :
      Function.uncurry H' =ᵐ[(timeMeasure T).prod P] Function.uncurry H := by
    have hmp : MeasurePreserving (Prod.map ((↑) : ℝ≥0 → ℝ) id)
        ((timeMeasure T).prod P) ((volume.restrict (Ioc 0 (T : ℝ))).prod P) :=
      (measurePreserving_coe_timeMeasure T).prod (MeasurePreserving.id P)
    exact (hmp.quasiMeasurePreserving.ae_eq_comp (hprod_real T)).mono fun ⟨t, ω⟩ h ↦ by
      simpa only [Function.comp_apply, Prod.map_apply, id_eq, Real.toNNReal_coe,
        Function.uncurry_apply_pair] using h
  have hH'loc : LocallyBrownianIntegrable ℱ P H' := by
    refine locallyBrownianIntegrable_iff_nat.mpr ⟨hH'pred, fun n ↦ ?_⟩
    have hswap :
        (fun p : Ω × ℝ≥0 ↦ H' p.2 p.1) =ᵐ[P.prod (timeMeasure n)]
          fun p : Ω × ℝ≥0 ↦ H p.2 p.1 :=
      (Measure.measurePreserving_swap (μ := P)
        (ν := timeMeasure n)).quasiMeasurePreserving.ae_eq_comp (hprod n)
    filter_upwards [hfin, Measure.ae_ae_of_ae_prod hswap] with ω hω heq
    rw [← NNReal.coe_natCast n, NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def]
    exact (hω n).ae_eq (Filter.EventuallyEq.symm heq)
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

/-- **Filtration-enlargement comparison for Itô integrals.** If `ℱ ≤ 𝒢` and `W` remains filtered
pre-Brownian relative to `𝒢`, any `ℱ`-Itô integral and any `𝒢`-Itô integral of the same integrand
are indistinguishable. -/
theorem itoIntegral_congr_filtration {𝒢 : Filtration ℝ≥0 mΩ}
    (hW𝒢 : IsFilteredPreBrownianReal 𝒢 W P) (hℱ𝒢 : ℱ ≤ 𝒢)
    {H I J : ℝ≥0 → Ω → ℝ}
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral 𝒢 P W H J) :
    I ≡ᵐ[P] J :=
  isItoIntegral_unique hW𝒢 (hI.mono_filtration hℱ𝒢) hJ

/-- **Internal `L²` stage lemma:** bounded left-measurable multiplier rule for `BrownianIntegrable`
integrands on `(s, t]`. -/
private theorem isItoIntegral_ite_Ioc_mul_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    {Cξ : ℝ} (hCξ : ∀ ω, ‖ξ ω‖ ≤ Cξ) :
    IsItoIntegral ℱ P W (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0)
      (fun u ω ↦ ξ ω * (I (min u t) ω - I (min u s) ω)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hpred : IsStronglyPredictable ℱ (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0) := by
    rw [ite_Ioc_mul_eq]
    exact (isStronglyPredictable_ite_Ioc hξ).mul hH.isStronglyPredictable
  have hcont_mul : ∀ᵐ ω ∂P, Continuous fun u ↦ ξ ω * (I (min u t) ω - I (min u s) ω) :=
    hI.ae_continuous.mono fun ω hω ↦ continuous_const.mul
      ((hω.comp (continuous_id.min continuous_const)).sub
        (hω.comp (continuous_id.min continuous_const)))
  refine isItoIntegral_of_approx_simpleHolding hpred hcont_mul fun T ↦ ?_
  obtain ⟨K, hKlim, hunif⟩ :=
    hW.exists_seq_elementaryIntegrand_tendstoUniformlyOn hcont hH hI
  choose hσ hb_meas hb_hold hb_gain using fun k ↦
    Finance.simpleHolding_clip_Ioc_mul ℱ ((K k).monotone_dates.monotoneOn _)
      (K k).measurable_positions hst hξ
  let σ (k : ℕ) : ℕ → ℝ≥0 := fun j ↦ Set.projIcc s t hst ((K k).dates j)
  let b (k j : ℕ) (ω : Ω) : ℝ := if (K k).dates j ≤ t then ξ ω * (K k).positions j ω else 0
  have hL2 : Tendsto (fun k ↦ eLpNorm
      (Function.uncurry (Finance.simpleHolding (σ k) (K k).n (b k)) -
        Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0) 2
      ((timeMeasure T).prod P)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun k ↦ ENNReal.ofReal (max Cξ 0) * eLpNorm
        (fun p : ℝ≥0 × Ω ↦ (K k).toProcess p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P)) atTop (𝓝 (ENNReal.ofReal (max Cξ 0) * 0)) :=
      ENNReal.Tendsto.const_mul (hKlim T) (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hconst
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconst (fun _ ↦ zero_le)
      fun k ↦ ?_
    have hfm : AEStronglyMeasurable
        (Function.uncurry (Finance.simpleHolding (σ k) (K k).n (b k)) -
          Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0)
        ((timeMeasure T).prod P) :=
      (((Finance.isStronglyPredictable_simpleHolding (hb_meas k)).sub hpred).mono
        ℱ.predictable_le_prod).aestronglyMeasurable
    calc eLpNorm (Function.uncurry (Finance.simpleHolding (σ k) (K k).n (b k)) -
          Function.uncurry fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0) 2
          ((timeMeasure T).prod P)
        ≤ eLpNorm (max Cξ 0 •
            (fun p : ℝ≥0 × Ω ↦ (K k).toProcess p.1 p.2 - H p.1 p.2)) 2
            ((timeMeasure T).prod P) := by
          refine eLpNorm_mono_eNorm hfm fun ⟨u, ω⟩ ↦ ?_
          dsimp only [σ, b]
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.uncurry_apply_pair,
            hb_hold k u ω, ElementaryIntegrand.toProcess_eq_simpleHolding, Set.indicator_apply,
            Set.mem_Ioc, eNorm_mul, Real.eNorm_eq_ofReal_abs, abs_of_nonneg (le_max_right Cξ 0)]
          split_ifs
          · rw [← mul_sub, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
            exact mul_le_mul_of_nonneg_right
              (ENNReal.ofReal_le_ofReal ((hCξ ω).trans (le_max_left _ _))) (by positivity)
          · simp only [sub_self, abs_zero, ENNReal.ofReal_zero, zero_le]
      _ = ENNReal.ofReal (max Cξ 0) * eLpNorm
            (fun p : ℝ≥0 × Ω ↦ (K k).toProcess p.1 p.2 - H p.1 p.2) 2
            ((timeMeasure T).prod P) := by
          rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal_abs, abs_of_nonneg (le_max_right Cξ 0)]
  refine ⟨fun k ↦ (K k).n, σ, b, hσ, hb_meas,
    tendsto_measure_le_lintegral_enorm_sq_sub
      (fun k ↦ Finance.isStronglyPredictable_simpleHolding (hb_meas k)) (fun _ ↦ hpred) hL2,
    tendstoInMeasure_of_tendsto_ae (fun k ↦
      ((Finance.stronglyAdapted_simpleGains (hσ k) (hb_meas k)
        hW.adapted.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable)
      (hunif.mono fun ω hω ↦ ?_)⟩
  have h1 := (hω (max (min T t) (min T s))).tendsto_at (Set.mem_Iic.mpr (le_max_left _ _))
  have h2 := (hω (max (min T t) (min T s))).tendsto_at (Set.mem_Iic.mpr (le_max_right _ _))
  dsimp only [σ, b]
  simpa only [fun k ↦ hb_gain k W T ω, ElementaryIntegrand.integral_eq_simpleGains] using
    (tendsto_const_nhds (x := ξ ω)).mul (h1.sub h2)

/-- Identify the localized `L²` stages of any Itô integral along `energyLevelLocalizer H`. -/
private theorem exists_isItoIntegral_stoppedProcess_energyLevelLocalizer
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hI : IsItoIntegral ℱ P W H I) :
    ∀ n, IsItoIntegral ℱ P W (energyLevelCutoff H n)
      (stoppedProcess I (energyLevelLocalizer H n)) := by
  obtain ⟨I₀, hI₀ito, -, -, hI₀stop⟩ :=
    hW.exists_isItoIntegral_aux hcont hI.locallyBrownianIntegrable
  exact fun n ↦ (hI₀stop n).congr
    ((isItoIntegral_unique hW hI₀ito hI).stoppedProcess (energyLevelLocalizer H n))

/-- Prove `IsItoIntegral ℱ P W K M` by comparing `M` against the auxiliary integral of `K` along
the joint localizers `min (energyLevelLocalizer H) (energyLevelLocalizer K)`. -/
private theorem isItoIntegral_of_stoppedProcess_min_energyLevelLocalizer
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H K M : ℝ≥0 → Ω → ℝ} (hH : LocallyBrownianIntegrable ℱ P H)
    (hK : LocallyBrownianIntegrable ℱ P K)
    {L : ℕ → ℝ≥0 → Ω → ℝ}
    (hLHS : ∀ n, IsItoIntegral ℱ P W (L n)
      (stoppedProcess M (min (energyLevelLocalizer H) (energyLevelLocalizer K) n)))
    (hHeq : ∀ n (u : ℝ≥0) (ω : Ω) (T : ℝ≥0), u ≤ T →
      nnvolume.accumulatedEnergy H T ω < ⊤ → nnvolume.accumulatedEnergy K T ω < ⊤ →
      L n u ω = if (u : WithTop ℝ≥0) ≤ energyLevelLocalizer H n ω then
        energyLevelCutoff K n u ω else 0) :
    IsItoIntegral ℱ P W K M := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨J, hJito, -, -, hJstop⟩ := hW.exists_isItoIntegral_aux hcont hK
  let η := min (energyLevelLocalizer H) (energyLevelLocalizer K)
  have hη_top : ∀ᵐ ω ∂P, Tendsto (η · ω) atTop (𝓝 ⊤) :=
    (hH.isLocalizingSequence_energyLocalizer.min
      hK.isLocalizingSequence_energyLocalizer).tendsto_top
  have hcompat (n : ℕ) : stoppedProcess M (η n) ≡ᵐ[P] stoppedProcess J (η n) := by
    have hRHS_ito : IsItoIntegral ℱ P W
        (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ energyLevelLocalizer H n ω then
          energyLevelCutoff K n t ω else 0) (stoppedProcess J (η n)) := by
      have hRHS_eq : stoppedProcess J (η n) =
          stoppedProcess (stoppedProcess J (energyLevelLocalizer K n))
            (energyLevelLocalizer H n) :=
        stoppedProcess_stoppedProcess'.symm
      rw [hRHS_eq]
      exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont
        (hK.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
        (hJstop n) (hH.isLocalizingSequence_energyLocalizer.isStoppingTime n)
    refine hW.itoIntegral_local_congr (hLHS n) hRHS_ito fun T ↦ ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := P)).ae
        ((ae_mem_Ioc_timeMeasure T).mono fun _ h ↦ h.2),
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).ae
        (hH.ae_accumulatedEnergy_lt_top.mono fun _ h ↦ h T),
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).ae
        (hK.ae_accumulatedEnergy_lt_top.mono fun _ h ↦ h T)] with ⟨u, ω⟩ hu hfinH hfinK
    exact hHeq n u ω T hu hfinH hfinK
  exact hJito.congr (indist_of_ae_eq_before_lifetimes hη_top fun n ↦
    (hcompat n).mono fun ω hω t ht ↦ by simpa only [stoppedProcess_eq_of_le ht] using hω t).symm

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
  have hIstop := hW.exists_isItoIntegral_stoppedProcess_energyLevelLocalizer hcont hI
  refine hW.isItoIntegral_of_stoppedProcess_min_energyLevelLocalizer hcont hH hHσ
      (L := fun n t ω ↦ if (t : WithTop ℝ≥0) ≤ min (σ ω) (energyLevelLocalizer Hσ n ω) then
        energyLevelCutoff H n t ω else 0) (fun n ↦ ?_) fun n u ω _ hu hfinH hfinHσ ↦ ?_
  · have hLHS_eq :
        stoppedProcess (stoppedProcess I σ)
          (min (energyLevelLocalizer H) (energyLevelLocalizer Hσ) n) =
        stoppedProcess (stoppedProcess I (energyLevelLocalizer H n))
          (fun ω ↦ min (σ ω) (energyLevelLocalizer Hσ n ω)) := by
      rw [stoppedProcess_stoppedProcess', stoppedProcess_stoppedProcess']
      congr 1; ext ω; ac_rfl
    rw [hLHS_eq]
    exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont
      (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
      (hIstop n) (hσ.min (hHσ.isLocalizingSequence_energyLocalizer.isStoppingTime n))
  · simp only [energyLevelCutoff, nnvolume.finiteEnergyCutoff_eqOn hfinH hu,
      nnvolume.finiteEnergyCutoff_eqOn hfinHσ hu, Hσ, le_min_iff]
    split_ifs <;> first | rfl | tauto

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
  rw [eq_sub_iff_add_eq'.mpr (ite_le_eq_add_ite_Ioc hστ H).symm]
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
      simp only [Pi.sub_apply, stoppedProcess_const_time])

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
  let Ξ : ℝ≥0 → Ω → ℝ := fun u ω ↦ if s < u ∧ u ≤ t then ξ ω else 0
  have hΞ_pred : IsStronglyPredictable ℱ Ξ := isStronglyPredictable_ite_Ioc hξ
  have hΞ_bound (u : ℝ≥0) (ω : Ω) : ‖Ξ u ω‖ ≤ max Cξ 0 := by
    dsimp only [Ξ]
    split_ifs
    · exact (hCξ ω).trans (le_max_left _ _)
    · simpa only [norm_zero] using le_max_right Cξ 0
  let K : ℝ≥0 → Ω → ℝ := fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * H u ω else 0
  have hK : LocallyBrownianIntegrable ℱ P K := by
    have hK_eq : K = fun u ω ↦ H u ω * Ξ u ω := by
      ext u ω
      dsimp only [K, Ξ]
      split_ifs <;> simp [mul_comm]
    rw [hK_eq]
    exact hH.mul_of_locally_bounded hΞ_pred
      (.of_forall fun ω _ ↦ ⟨max Cξ 0, fun u _ ↦ hΞ_bound u ω⟩)
  have hIstop := hW.exists_isItoIntegral_stoppedProcess_energyLevelLocalizer hcont hI
  let M : ℝ≥0 → Ω → ℝ := fun u ω ↦ ξ ω * (I (min u t) ω - I (min u s) ω)
  let stopS : Ω → WithTop ℝ≥0 := fun _ ↦ (s : WithTop ℝ≥0)
  let stopT : Ω → WithTop ℝ≥0 := fun _ ↦ (t : WithTop ℝ≥0)
  have hM_eq : M = (fun _ ↦ ξ) * (stoppedProcess I stopT - stoppedProcess I stopS) := by
    ext u ω
    simp only [M, Pi.mul_apply, Pi.sub_apply, stopS, stopT, stoppedProcess_const_time]
  refine hW.isItoIntegral_of_stoppedProcess_min_energyLevelLocalizer hcont hH hK (M := M)
      (L := fun n u ω ↦ if (u : WithTop ℝ≥0) ≤ energyLevelLocalizer K n ω then
        (if s < u ∧ u ≤ t then ξ ω * energyLevelCutoff H n u ω else 0) else 0)
      (fun n ↦ ?_) fun n u ω _ hu hfinH hfinK ↦ ?_
  · let M_n : ℝ≥0 → Ω → ℝ := fun u ω ↦ ξ ω *
      (stoppedProcess I (energyLevelLocalizer H n) (min u t) ω -
        stoppedProcess I (energyLevelLocalizer H n) (min u s) ω)
    have hM_n_ito : IsItoIntegral ℱ P W
        (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * energyLevelCutoff H n u ω else 0) M_n :=
      hW.isItoIntegral_ite_Ioc_mul_of_brownianIntegrable hcont
        (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1))
        (hIstop n) hst hξ hCξ
    have hM_n_eq : M_n = (fun _ ↦ ξ) *
        (stoppedProcess (stoppedProcess I (energyLevelLocalizer H n)) stopT -
          stoppedProcess (stoppedProcess I (energyLevelLocalizer H n)) stopS) := by
      ext u ω
      simp only [M_n, Pi.mul_apply, Pi.sub_apply, stopS, stopT, stoppedProcess_const_time]
    have hLHS_eq :
        stoppedProcess M (min (energyLevelLocalizer H) (energyLevelLocalizer K) n) =
          stoppedProcess M_n (energyLevelLocalizer K n) := by
      rw [hM_eq, hM_n_eq]
      simp only [stoppedProcess_mul, stoppedProcess_sub, stoppedProcess_const,
        stoppedProcess_stoppedProcess]
      have h1 :
          min (energyLevelLocalizer H) (energyLevelLocalizer K) n ⊓ stopT =
            energyLevelLocalizer K n ⊓ (stopT ⊓ energyLevelLocalizer H n) := by
        ext ω; simp only [Pi.inf_apply]; ac_rfl
      have h2 :
          min (energyLevelLocalizer H) (energyLevelLocalizer K) n ⊓ stopS =
            energyLevelLocalizer K n ⊓ (stopS ⊓ energyLevelLocalizer H n) := by
        ext ω; simp only [Pi.inf_apply]; ac_rfl
      rw [h1, h2]
    have hK_n : BrownianIntegrable ℱ P
        (fun u ω ↦ if s < u ∧ u ≤ t then ξ ω * energyLevelCutoff H n u ω else 0) := by
      rw [ite_Ioc_mul_eq, mul_comm]
      exact (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer
        (P := P) ((n : ℝ≥0) + 1)).mul_of_bound hΞ_pred (max Cξ 0) hΞ_bound
    rw [hLHS_eq]
    exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont
      hK_n hM_n_ito (hK.isLocalizingSequence_energyLocalizer.isStoppingTime n)
  · simp only [energyLevelCutoff, nnvolume.finiteEnergyCutoff_eqOn hfinH hu,
      nnvolume.finiteEnergyCutoff_eqOn hfinK hu, K]
    split_ifs <;> first | rfl | simp

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
    simpa only [stoppedProcess_const_time] using htω u
  have hJs0 : J (min u s) ω = 0 := by
    simpa only [stoppedProcess_const_time, Pi.zero_apply] using hsω u
  rw [hJu, hJs0, sub_zero]

end TauCeti.Probability.IsFilteredPreBrownianReal
