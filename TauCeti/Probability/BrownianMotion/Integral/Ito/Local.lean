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
  choose U hUito hUpred hUmart _ using fun n ↦
    hW.exists_isItoIntegral_of_brownianIntegrable hcont (hHloc n)
  have hcompat (n m : ℕ) (hnm : n ≤ m) : stoppedProcess (U m) (τ n) ≡ᵐ[P] U n := by
    have hstop :=
      hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont (hHloc m) (hUito m) (hτ n)
    have hEq : (fun (t : ℝ≥0) ω ↦
        if (t : WithTop ℝ≥0) ≤ τ n ω then Hloc m t ω else 0) = Hloc n := by
      ext t ω; dsimp only [Hloc]
      by_cases ht : (t : WithTop ℝ≥0) ≤ τ n ω
      · simp only [ht, ht.trans (hτ_mono hnm ω), ite_true]
      · simp only [ht, ite_false]
    rw [hEq] at hstop
    exact hW.isItoIntegral_unique hstop (hUito n)
  obtain ⟨I, hIprog, hIcont, hIstop⟩ :=
    exists_isStronglyProgressive_patch_stoppedProcess hloc.tendsto_top
      (fun n ↦ (hUpred n).isStronglyProgressive) (fun n ↦ (hUito n).ae_continuous) hcompat
  have hIloc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ I P :=
    hIprog.locally_martingale_of_ae_stopped_eq hloc hUmart fun n t ↦ by
      rw [show (fun s ↦ {ω | (⊥ : WithTop ℝ≥0) < τ n ω}.indicator (I s)) = I from
        funext fun s ↦ funext fun ω ↦
          Set.indicator_of_mem (nnvolume.energyLocalizer_pos H (by positivity) ω) _]
      exact (hIstop n).mono fun ω hω ↦ (hω t).symm
  have hIito : IsItoIntegral ℱ P W H I := by
    refine ⟨hH.isStronglyPredictable, hIcont, fun t ↦ ?_⟩
    have hexK (n : ℕ) : ∃ K : ElementaryIntegrand ℱ,
        eLpNorm (fun p : ℝ≥0 × Ω ↦ K.toProcess p.1 p.2 - Hloc n p.1 p.2) 2
          ((timeMeasure t).prod P) < (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
      obtain ⟨m, s, a, C, -, hs, ha, hb, herr⟩ :=
        ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t (hHloc n).isStronglyPredictable
          (by simpa only [NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def] using
            (hHloc n).memLp t)
          (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _))
      exact ⟨ElementaryIntegrand.ofSimple m s a hs.monotoneOn ha
          (fun j hj ↦ ⟨C, fun ω ↦ by simpa only [Real.norm_eq_abs] using hb j hj ω⟩),
        by simpa only [ElementaryIntegrand.toProcess_ofSimple] using herr⟩
    choose K hK_lt using hexK
    have hK_L2 : Tendsto (fun n ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ (K n).toProcess p.1 p.2 - Hloc n p.1 p.2) 2
          ((timeMeasure t).prod P)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
        (fun _ ↦ zero_le) fun n ↦ (hK_lt n).le
    have hK_I_L2 : Tendsto (fun n ↦ eLpNorm ((K n).integral W t - U n t) 2 P) atTop (𝓝 0) :=
      hK_L2.congr fun n ↦ (hW.eLpNorm_sub_of_isItoIntegral
        ((K n).brownianIntegrable_toProcess (P := P)) (hHloc n)
        ((K n).isItoIntegral hcont) (hUito n) t).symm
    let B (n : ℕ) : Set Ω := {ω | τ n ω ≤ (t : WithTop ℝ≥0)}
    have hB_inter : P (⋂ n, B n) = 0 :=
      measure_mono_null (t := {ω | ¬ Tendsto (τ · ω) atTop (𝓝 ⊤)}) (fun ω hω hlim ↦ by
        obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).exists
        exact not_lt_of_ge (Set.mem_iInter.mp hω n) hn) hloc.tendsto_top
    have hB_lim : Tendsto (fun n ↦ P (B n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, hB_inter] using
        tendsto_measure_iInter_atTop (s := B) (fun n ↦ (ℱ.le t _ (hτ n t)).nullMeasurableSet)
          (fun _ _ hnm ω hω ↦ (hτ_mono hnm ω).trans hω) ⟨0, measure_ne_top P _⟩
    let N : Set Ω := {ω | ¬(nnvolume.accumulatedEnergy H t ω < ∞ ∧
      ∀ n s, stoppedProcess I (τ n) s ω = U n s ω)}
    have hN_zero : P N = 0 := by
      rw [← ae_iff]
      filter_upwards [hH.ae_accumulatedEnergy_lt_top, ae_all_iff.mpr hIstop] with ω hfin hst
      exact ⟨hfin t, hst⟩
    have hgood (n : ℕ) {ω : Ω} (hB : ω ∉ B n) (hN : ω ∉ N) :
        I t ω = U n t ω ∧
          (∫⁻ s, ‖(K n).toProcess s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t) =
            ∫⁻ s, ‖(K n).toProcess s ω - Hloc n s ω‖ₑ ^ 2 ∂timeMeasure t := by
      have ht_lt : (t : WithTop ℝ≥0) < τ n ω := lt_of_not_ge hB
      have hN' := not_not.mp hN
      refine ⟨by simpa only [stoppedProcess_eq_of_le ht_lt.le] using hN'.2 n t,
        lintegral_congr_ae ((ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ ?_)⟩
      have hle : (s : WithTop ℝ≥0) ≤ τ n ω := (WithTop.coe_le_coe.mpr hs.2).trans ht_lt.le
      simp only [Hloc, hle, ite_true, nnvolume.finiteEnergyCutoff_eqOn hN'.1 hs.2]
    have hbound (A C : ℕ → Set Ω) (hC : Tendsto (fun n ↦ P (C n)) atTop (𝓝 0))
        (hsub : ∀ n ω, ω ∈ A n → ω ∉ B n → ω ∉ N → ω ∈ C n) :
        Tendsto (fun n ↦ P (A n)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [add_zero] using hB_lim.add hC) (fun _ ↦ zero_le) fun n ↦ ?_
      calc P (A n) ≤ P (B n ∪ N ∪ C n) := measure_mono fun ω hω ↦ by
            by_cases hB : ω ∈ B n
            · exact .inl (.inl hB)
            · by_cases hN : ω ∈ N
              · exact .inl (.inr hN)
              · exact .inr (hsub n ω hω hB hN)
        _ ≤ P (B n) + P N + P (C n) :=
            (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
        _ = P (B n) + P (C n) := by rw [hN_zero, add_zero]
    refine ⟨K, fun ε hε ↦ hbound _ _ (tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
        (F := fun n s ω ↦ (K n).toProcess s ω - Hloc n s ω)
        (fun n ↦ (((K n).isStronglyPredictable_toProcess.sub
          (hHloc n).isStronglyPredictable).mono ℱ.predictable_le_prod).measurable) hK_L2 hε)
        fun n ω hω hB hN ↦ by simpa only [Set.mem_ofPred_eq, ← (hgood n hB hN).2] using hω,
      fun ε hε ↦ hbound _ _
        ((tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (f := fun n ↦ (K n).integral W t - U n t)
          (g := 0) (by norm_num) (by simpa only [sub_zero] using hK_I_L2)) ε hε)
        fun n ω hω hB hN ↦ by
          simpa only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, eDist_eq_eNorm_sub, sub_zero,
            (hgood n hB hN).1] using hω⟩
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
  have hτ (n : ℕ) := hH.isLocalizingSequence_energyLocalizer.isStoppingTime n
  have hρ (n : ℕ) := hHσ.isLocalizingSequence_energyLocalizer.isStoppingTime n
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
    have hLHS_ito : IsItoIntegral ℱ P W
        (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ min (σ ω) (ρ n ω) then Hloc n t ω else 0)
        (stoppedProcess (stoppedProcess I σ) (η n)) := by
      rw [show stoppedProcess (stoppedProcess I σ) (η n) =
          stoppedProcess (stoppedProcess I (τ n)) (fun ω ↦ min (σ ω) (ρ n ω)) by
        rw [stoppedProcess_stoppedProcess', stoppedProcess_stoppedProcess']; congr 1; ext ω; ac_rfl]
      exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont (hHloc n) (hIstop n)
        (hσ.min (hρ n))
    have hRHS_ito : IsItoIntegral ℱ P W
        (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ n ω then Hσloc n t ω else 0)
        (stoppedProcess J (η n)) := by
      rw [show stoppedProcess J (η n) = stoppedProcess (stoppedProcess J (ρ n)) (τ n) from
        stoppedProcess_stoppedProcess'.symm]
      exact hW.isItoIntegral_stoppedProcess_of_brownianIntegrable hcont (hHσloc n) (hJstop n)
        (hτ n)
    refine hW.itoIntegral_local_congr hLHS_ito hRHS_ito fun T ↦ ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := P)).ae
        ((ae_mem_Ioc_timeMeasure T).mono fun _ h ↦ h.2),
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).ae
        (hH.ae_accumulatedEnergy_lt_top.mono fun _ h ↦ h T),
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).ae
        (hHσ.ae_accumulatedEnergy_lt_top.mono fun _ h ↦ h T)] with ⟨t, ω⟩ ht hfinH hfinHσ
    dsimp only [Function.uncurry_apply_pair, Hloc, Hσloc] at ht hfinH hfinHσ ⊢
    simp only [nnvolume.finiteEnergyCutoff_eqOn hfinH ht,
      nnvolume.finiteEnergyCutoff_eqOn hfinHσ ht, Hσ, le_min_iff]
    split_ifs <;> first | rfl | tauto
  exact hJito.congr_indist (indist_of_ae_eq_before_lifetimes hη_top fun n ↦
    (hcompat n).mono fun ω hω t ht ↦ by simpa only [stoppedProcess_eq_of_le ht] using hω t).symm

end TauCeti.Probability.IsFilteredPreBrownianReal
