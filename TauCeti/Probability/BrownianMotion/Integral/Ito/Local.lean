/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Stopping
public import Mathlib.Probability.Process.LocalProperty
import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Process.Indistinguishable

/-!
# Local Brownian Itô integral process

This file constructs the continuous, strongly progressive Brownian Itô integral process for every
`LocallyBrownianIntegrable` integrand on a raw filtration, proves that every strongly progressive
Itô integral of a locally Brownian-integrable integrand is a continuous local martingale, and
extends stopping compatibility to the full local domain.

Closed-level raw energy localizers `τ n := nnvolume.energyLocalizer H (n + 1)` reduce a locally
Brownian-integrable integrand `H` to `BrownianIntegrable` cutoffs `Hloc n` without augmenting the
filtration. On each stage, `exists_isItoIntegral_of_brownianIntegrable` constructs a continuous
square-integrable martingale `U n`, and `L²` stopping compatibility
(`isItoIntegral_stoppedProcess_of_brownianIntegrable`) yields stage consistency
`stoppedProcess (U m) (τ n) ≡ᵐ[P] U n` for `n ≤ m`. Patching these stages produces a single
strongly progressive, almost surely continuous process `I` satisfying `IsItoIntegral ℱ P W H I` and
`Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P`.

## Main results

* `TauCeti.Probability.IsFilteredPreBrownianReal.exists_isItoIntegral`: every locally
  Brownian-integrable integrand admits a strongly progressive Itô integral that is a local
  martingale.
* `TauCeti.Probability.IsFilteredPreBrownianReal.itoIntegral_localMartingale`: every strongly
  progressive Itô integral of a locally Brownian-integrable integrand is a local martingale.
* `TauCeti.Probability.IsFilteredPreBrownianReal.isItoIntegral_stoppedProcess`: stopping an Itô
  integral of a locally Brownian-integrable integrand at any stopping time `σ` produces an Itô
  integral of `1_{[0, σ]} · H`.

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

/-- Helper: construct a strongly progressive, almost surely continuous local-martingale Itô
integral of a `LocallyBrownianIntegrable` integrand `H` together with the identification of its
stages stopped at the closed-level raw energy localizers. -/
private theorem exists_isItoIntegral_aux
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : LocallyBrownianIntegrable ℱ P H) :
    let τ (n : ℕ) : Ω → WithTop ℝ≥0 := nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
    let Hloc (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
      if (t : WithTop ℝ≥0) ≤ τ n ω then nnvolume.finiteEnergyCutoff H t ω else 0
    ∃ I : ℝ≥0 → Ω → ℝ,
      IsItoIntegral ℱ P W H I ∧ IsStronglyProgressive ℱ I ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P ∧
      ∀ n, IsItoIntegral ℱ P W (Hloc n) (stoppedProcess I (τ n)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ (n : ℕ) : Ω → WithTop ℝ≥0 := nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
  let Hloc (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    if (t : WithTop ℝ≥0) ≤ τ n ω then nnvolume.finiteEnergyCutoff H t ω else 0
  have hloc : IsLocalizingSequence ℱ τ P := hH.isLocalizingSequence_energyLocalizer
  have hτ (n : ℕ) : IsStoppingTime ℱ (τ n) := hloc.isStoppingTime n
  have hτ_mono : ∀ ⦃n m : ℕ⦄, n ≤ m → ∀ ω, τ n ω ≤ τ m ω := fun _ _ hnm ω ↦
    nnvolume.monotone_energyLocalizer H ω (add_le_add (Nat.cast_le.mpr hnm) le_rfl)
  have hHloc (n : ℕ) : BrownianIntegrable ℱ P (Hloc n) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1)
  have hex (n : ℕ) := hW.exists_isItoIntegral_of_brownianIntegrable hcont (hHloc n)
  choose U hUito hUpred hUmart _ using hex
  have hcompat (n m : ℕ) (hnm : n ≤ m) : stoppedProcess (U m) (τ n) ≡ᵐ[P] U n := by
    have hstop :=
      hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont (hHloc m) (hUito m) (hτ n)
    have hEq : (fun (t : ℝ≥0) ω ↦
        if (t : WithTop ℝ≥0) ≤ τ n ω then Hloc m t ω else 0) = Hloc n := by
      ext t ω
      dsimp only [Hloc]
      by_cases ht : (t : WithTop ℝ≥0) ≤ τ n ω
      · simp only [ht, ht.trans (hτ_mono hnm ω), ite_true]
      · simp only [ht, ite_false]
    rw [hEq] at hstop
    exact hW.isItoIntegral_unique hstop (hUito n)
  obtain ⟨I, hIprog, hIcont, hIstop⟩ :=
    exists_isStronglyProgressive_patch_stoppedProcess hloc.tendsto_top
      (fun n ↦ (hUpred n).isStronglyProgressive) (fun n ↦ (hUito n).ae_continuous) hcompat
  have hIloc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
    refine hIprog.locally_martingale_of_ae_stopped_eq hloc hUmart fun n t ↦ ?_
    have hind : (fun s ↦ {ω | (⊥ : WithTop ℝ≥0) < τ n ω}.indicator (I s)) = I := by
      ext s ω
      exact Set.indicator_of_mem (nnvolume.energyLocalizer_pos H (by positivity) ω) _
    rw [hind]
    exact (hIstop n).mono fun ω hω ↦ (hω t).symm
  have hIito : IsItoIntegral ℱ P W H I := by
    refine ⟨hH.isStronglyPredictable, hIcont, fun t ↦ ?_⟩
    have hexK (n : ℕ) : ∃ K : ElementaryIntegrand ℱ,
        eLpNorm (fun p : ℝ≥0 × Ω ↦ K.toProcess p.1 p.2 - Hloc n p.1 p.2) 2
          ((timeMeasure t).prod P) < (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
      have hmem : MemLp (Function.uncurry (Hloc n)) 2 ((timeMeasure t).prod P) := by
        simpa only [NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def] using (hHloc n).memLp t
      have hpos : (0 : ℝ≥0∞) < (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) :=
        ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
      obtain ⟨m, s, a, C, -, hs, ha, hb, herr⟩ :=
        ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t
          (hHloc n).isStronglyPredictable hmem hpos
      refine ⟨ElementaryIntegrand.ofSimple m s a hs.monotoneOn ha
        (fun j hj ↦ ⟨C, fun ω ↦ by simpa only [Real.norm_eq_abs] using hb j hj ω⟩), ?_⟩
      simpa only [ElementaryIntegrand.toProcess_ofSimple] using herr
    choose K hK_lt using hexK
    have hinv_lim : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ≥0∞)⁻¹)) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hK_L2 : Tendsto (fun n ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ (K n).toProcess p.1 p.2 - Hloc n p.1 p.2) 2
          ((timeMeasure t).prod P)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv_lim
        (fun _ ↦ zero_le) fun n ↦ (hK_lt n).le
    have hK_I_L2 : Tendsto (fun n ↦ eLpNorm ((K n).integral W t - U n t) 2 P) atTop (𝓝 0) := by
      have heq (n : ℕ) : eLpNorm ((K n).integral W t - U n t) 2 P =
          eLpNorm (fun p : ℝ≥0 × Ω ↦ (K n).toProcess p.1 p.2 - Hloc n p.1 p.2) 2
            ((timeMeasure t).prod P) :=
        hW.eLpNorm_sub_of_isItoIntegral ((K n).brownianIntegrable_toProcess (P := P)) (hHloc n)
          ((K n).isItoIntegral hcont) (hUito n) t
      exact hK_L2.congr fun n ↦ (heq n).symm
    let B (n : ℕ) : Set Ω := {ω | τ n ω ≤ (t : WithTop ℝ≥0)}
    have hB_meas (n : ℕ) : MeasurableSet (B n) := ℱ.le t _ (hτ n t)
    have hB_anti : Antitone B := fun n m hnm ω hω ↦ (hτ_mono hnm ω).trans hω
    have hB_inter : P (⋂ n, B n) = 0 := by
      refine measure_mono_null (t := {ω | ¬ Tendsto (τ · ω) atTop (𝓝 ⊤)}) (fun ω hω hlim ↦ ?_)
        hloc.tendsto_top
      obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).exists
      exact not_lt_of_ge (Set.mem_iInter.mp hω n) hn
    have hB_lim : Tendsto (fun n ↦ P (B n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, hB_inter] using
        tendsto_measure_iInter_atTop (fun n ↦ (hB_meas n).nullMeasurableSet) hB_anti
          ⟨0, measure_ne_top P _⟩
    let N : Set Ω := {ω | ¬(nnvolume.accumulatedEnergy H t ω < ∞ ∧
      ∀ n s, stoppedProcess I (τ n) s ω = U n s ω)}
    have hN_zero : P N = 0 := by
      have hae : ∀ᵐ ω ∂P, nnvolume.accumulatedEnergy H t ω < ∞ ∧
          ∀ n s, stoppedProcess I (τ n) s ω = U n s ω := by
        filter_upwards [hH.ae_accumulatedEnergy_lt_top, ae_all_iff.mpr hIstop] with ω hfin hst
        exact ⟨hfin t, hst⟩
      exact hae
    have hgood (n : ℕ) {ω : Ω} (hB : ω ∉ B n) (hN : ω ∉ N) :
        I t ω = U n t ω ∧
          (∫⁻ s, ‖(K n).toProcess s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t) =
            ∫⁻ s, ‖(K n).toProcess s ω - Hloc n s ω‖ₑ ^ 2 ∂timeMeasure t := by
      have ht_lt : (t : WithTop ℝ≥0) < τ n ω := lt_of_not_ge hB
      have hN' : nnvolume.accumulatedEnergy H t ω < ∞ ∧
          ∀ m s, stoppedProcess I (τ m) s ω = U m s ω :=
        not_not.mp hN
      refine ⟨?_, ?_⟩
      · simpa only [stoppedProcess_eq_of_le ht_lt.le] using hN'.2 n t
      · refine lintegral_congr_ae ((ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ ?_)
        have hst : s ≤ t := hs.2
        have hle : (s : WithTop ℝ≥0) ≤ τ n ω := (WithTop.coe_le_coe.mpr hst).trans ht_lt.le
        have hcut : nnvolume.finiteEnergyCutoff H s ω = H s ω :=
          nnvolume.finiteEnergyCutoff_eqOn hN'.1 hst
        simp only [Hloc, hle, ite_true, hcut]
    refine ⟨K, fun ε hε ↦ ?_, ?_⟩
    · have hE_loc :=
        tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
          (F := fun n s ω ↦ (K n).toProcess s ω - Hloc n s ω)
          (fun n ↦ (((K n).isStronglyPredictable_toProcess.sub
            (hHloc n).isStronglyPredictable).mono ℱ.predictable_le_prod).measurable) hK_L2 hε
      have hsum : Tendsto (fun n ↦ P (B n) +
          P {ω | ε ≤ ∫⁻ s, ‖(K n).toProcess s ω - Hloc n s ω‖ₑ ^ 2 ∂timeMeasure t})
          atTop (𝓝 0) := by
        simpa only [add_zero] using hB_lim.add hE_loc
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun _ ↦ zero_le) fun n ↦ ?_
      have hsub : {ω | ε ≤ ∫⁻ s, ‖(K n).toProcess s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t} ⊆
          B n ∪ N ∪ {ω | ε ≤ ∫⁻ s, ‖(K n).toProcess s ω - Hloc n s ω‖ₑ ^ 2 ∂timeMeasure t} := by
        intro ω hω
        by_cases hB : ω ∈ B n
        · exact Or.inl (Or.inl hB)
        · by_cases hN : ω ∈ N
          · exact Or.inl (Or.inr hN)
          · refine Or.inr ?_
            simpa only [Set.mem_ofPred_eq, ← (hgood n hB hN).2] using hω
      calc
        P {ω | ε ≤ ∫⁻ s, ‖(K n).toProcess s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}
            ≤ P (B n ∪ N) +
                P {ω | ε ≤ ∫⁻ s, ‖(K n).toProcess s ω - Hloc n s ω‖ₑ ^ 2 ∂timeMeasure t} :=
              (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ P (B n) + P N +
                P {ω | ε ≤ ∫⁻ s, ‖(K n).toProcess s ω - Hloc n s ω‖ₑ ^ 2 ∂timeMeasure t} :=
              add_le_add (measure_union_le _ _) le_rfl
        _ = P (B n) +
                P {ω | ε ≤ ∫⁻ s, ‖(K n).toProcess s ω - Hloc n s ω‖ₑ ^ 2 ∂timeMeasure t} := by
              rw [hN_zero, add_zero]
    · intro ε hε
      have hdiff_meas : TendstoInMeasure P (fun n ↦ (K n).integral W t - U n t) atTop 0 :=
        tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
          (by simpa only [sub_zero] using hK_I_L2)
      have hsum : Tendsto (fun n ↦ P (B n) +
          P {ω | ε ≤ edist ((K n).integral W t ω - U n t ω) 0}) atTop (𝓝 0) := by
        simpa only [add_zero, Pi.sub_apply, Pi.zero_apply] using hB_lim.add (hdiff_meas ε hε)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun _ ↦ zero_le) fun n ↦ ?_
      have hsub : {ω | ε ≤ edist ((K n).integral W t ω) (I t ω)} ⊆
          B n ∪ N ∪ {ω | ε ≤ edist ((K n).integral W t ω - U n t ω) 0} := by
        intro ω hω
        by_cases hB : ω ∈ B n
        · exact Or.inl (Or.inl hB)
        · by_cases hN : ω ∈ N
          · exact Or.inl (Or.inr hN)
          · refine Or.inr ?_
            have hEq : edist ((K n).integral W t ω - U n t ω) 0 =
                edist ((K n).integral W t ω) (I t ω) := by
              rw [(hgood n hB hN).1, eDist_eq_eNorm_sub, sub_zero, eDist_eq_eNorm_sub]
            simpa only [Set.mem_ofPred_eq, hEq] using hω
      calc
        P {ω | ε ≤ edist ((K n).integral W t ω) (I t ω)}
            ≤ P (B n ∪ N) + P {ω | ε ≤ edist ((K n).integral W t ω - U n t ω) 0} :=
              (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ P (B n) + P N + P {ω | ε ≤ edist ((K n).integral W t ω - U n t ω) 0} :=
              add_le_add (measure_union_le _ _) le_rfl
        _ = P (B n) + P {ω | ε ≤ edist ((K n).integral W t ω - U n t ω) 0} := by
              rw [hN_zero, add_zero]
  exact ⟨I, hIito, hIprog, hIloc, fun n ↦ (hUito n).congr_indist (hIstop n).symm⟩

/-- **Existence of the continuous local Brownian Itô integral process.** Every
`LocallyBrownianIntegrable` integrand on a raw filtration admits a strongly progressive Itô
integral process which is a local martingale. Neither completeness nor right continuity of the
filtration is required. -/
theorem exists_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ,
      IsItoIntegral ℱ P W H I ∧ IsStronglyProgressive ℱ I ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
  obtain ⟨I, hIito, hIprog, hIloc, -⟩ := hW.exists_isItoIntegral_aux hcont hH
  exact ⟨I, hIito, hIprog, hIloc⟩

/-- **Local martingale property of Brownian Itô integrals.** Every strongly progressive Itô
integral of a `LocallyBrownianIntegrable` integrand is a local martingale on the raw filtration. -/
theorem itoIntegral_localMartingale (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (hProg : IsStronglyProgressive ℱ I) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P := by
  obtain ⟨J, hJito, -, hJloc⟩ := hW.exists_isItoIntegral hcont hH
  exact hProg.locally_martingale_of_indist hJloc (hW.isItoIntegral_unique hJito hI)

/-- **Stopping compatibility for local Brownian Itô integrals.** Stopping any Itô integral of a
`LocallyBrownianIntegrable` integrand at any stopping time `σ` on the raw filtration produces an
Itô integral of the cutoff integrand `1_{[0, σ]} · H`. -/
theorem isItoIntegral_stoppedProcess (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (stoppedProcess I σ) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let Hσ : ℝ≥0 → Ω → ℝ := fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0
  have hHσ : LocallyBrownianIntegrable ℱ P Hσ := hH.ite_le hσ
  let τ (n : ℕ) : Ω → WithTop ℝ≥0 := nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
  let ρ (n : ℕ) : Ω → WithTop ℝ≥0 := nnvolume.energyLocalizer Hσ ((n : ℝ≥0) + 1)
  let Hloc (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    if (t : WithTop ℝ≥0) ≤ τ n ω then nnvolume.finiteEnergyCutoff H t ω else 0
  let Hσloc (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    if (t : WithTop ℝ≥0) ≤ ρ n ω then nnvolume.finiteEnergyCutoff Hσ t ω else 0
  have hτ (n : ℕ) : IsStoppingTime ℱ (τ n) :=
    hH.isLocalizingSequence_energyLocalizer.isStoppingTime n
  have hρ (n : ℕ) : IsStoppingTime ℱ (ρ n) :=
    hHσ.isLocalizingSequence_energyLocalizer.isStoppingTime n
  have hHloc (n : ℕ) : BrownianIntegrable ℱ P (Hloc n) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1)
  have hHσloc (n : ℕ) : BrownianIntegrable ℱ P (Hσloc n) :=
    hHσ.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer ((n : ℝ≥0) + 1)
  obtain ⟨I₀, hI₀ito, -, -, hI₀stop⟩ := hW.exists_isItoIntegral_aux hcont hH
  have hIstop (n : ℕ) : IsItoIntegral ℱ P W (Hloc n) (stoppedProcess I (τ n)) :=
    (hI₀stop n).congr_indist ((hW.isItoIntegral_unique hI₀ito hI).stoppedProcess (τ n))
  obtain ⟨J, hJito, -, -, hJstop⟩ := hW.exists_isItoIntegral_aux hcont hHσ
  let η (n : ℕ) (ω : Ω) : WithTop ℝ≥0 := min (τ n ω) (ρ n ω)
  have hη_top : ∀ᵐ ω ∂P, Tendsto (η · ω) atTop (𝓝 ⊤) := by
    filter_upwards [hH.isLocalizingSequence_energyLocalizer.tendsto_top,
      hHσ.isLocalizingSequence_energyLocalizer.tendsto_top] with ω h1 h2
    simpa only [min_self] using h1.min h2
  have hcompat (n : ℕ) :
      stoppedProcess (stoppedProcess I σ) (η n) ≡ᵐ[P] stoppedProcess J (η n) := by
    have hLHS_eq : stoppedProcess (stoppedProcess I σ) (η n) =
        stoppedProcess (stoppedProcess I (τ n)) (fun ω ↦ min (σ ω) (ρ n ω)) := by
      rw [stoppedProcess_stoppedProcess', stoppedProcess_stoppedProcess']
      congr 1
      ext ω
      dsimp only [η]
      ac_rfl
    have hRHS_eq : stoppedProcess J (η n) = stoppedProcess (stoppedProcess J (ρ n)) (τ n) := by
      rw [stoppedProcess_stoppedProcess']
    have hLHS_ito : IsItoIntegral ℱ P W
        (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ min (σ ω) (ρ n ω) then Hloc n t ω else 0)
        (stoppedProcess (stoppedProcess I σ) (η n)) := by
      rw [hLHS_eq]
      exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont (hHloc n) (hIstop n)
        (hσ.min (hρ n))
    have hRHS_ito : IsItoIntegral ℱ P W
        (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ n ω then Hσloc n t ω else 0)
        (stoppedProcess J (η n)) := by
      rw [hRHS_eq]
      exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont (hHσloc n) (hJstop n)
        (hτ n)
    refine hW.itoIntegral_local_congr hLHS_ito hRHS_ito fun T ↦ ?_
    have hae_le : ∀ᵐ p : ℝ≥0 × Ω ∂(timeMeasure T).prod P, p.1 ≤ T :=
      (Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := P)).ae
        ((ae_mem_Ioc_timeMeasure T).mono fun _ h ↦ h.2)
    have hae_finH : ∀ᵐ p : ℝ≥0 × Ω ∂(timeMeasure T).prod P,
        nnvolume.accumulatedEnergy H T p.2 < ∞ :=
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).ae
        (hH.ae_accumulatedEnergy_lt_top.mono fun _ h ↦ h T)
    have hae_finHσ : ∀ᵐ p : ℝ≥0 × Ω ∂(timeMeasure T).prod P,
        nnvolume.accumulatedEnergy Hσ T p.2 < ∞ :=
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).ae
        (hHσ.ae_accumulatedEnergy_lt_top.mono fun _ h ↦ h T)
    filter_upwards [hae_le, hae_finH, hae_finHσ] with ⟨t, ω⟩ ht hfinH hfinHσ
    have hcutH : nnvolume.finiteEnergyCutoff H t ω = H t ω :=
      nnvolume.finiteEnergyCutoff_eqOn hfinH ht
    have hcutHσ : nnvolume.finiteEnergyCutoff Hσ t ω = Hσ t ω :=
      nnvolume.finiteEnergyCutoff_eqOn hfinHσ ht
    dsimp only [Function.uncurry_apply_pair, Hloc, Hσloc]
    rw [hcutH, hcutHσ]
    dsimp only [Hσ]
    simp only [le_min_iff]
    split_ifs <;> first | rfl | tauto
  have hind : stoppedProcess I σ ≡ᵐ[P] J := by
    refine indist_of_ae_eq_before_lifetimes hη_top fun n ↦ ?_
    filter_upwards [hcompat n] with ω hω t ht
    simpa only [stoppedProcess_eq_of_le ht] using hω t
  exact hJito.congr_indist hind.symm

end TauCeti.Probability.IsFilteredPreBrownianReal
