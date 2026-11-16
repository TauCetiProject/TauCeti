/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
public import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.StoppingApproximation
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Stopping compatibility of L² Brownian Itô integrals

Stopping the Itô integral process of a `BrownianIntegrable` integrand `H` at any stopping time `τ`
on a raw filtration produces an Itô integral of the cutoff integrand `1_{[0, τ]} · H`
(`isItoIntegral_stoppedProcess_of_brownianIntegrable`), and at every deterministic horizon `T` the
stopped integral agrees almost surely with `hW.l2Integral T` evaluated on `1_{[0, τ]} · H`
(`stoppedProcess_ae_eq_l2Integral`).

The proof first realizes stopping of any `ElementaryIntegrand` at an upward dyadic stopping time
`dyadicCeilTime k ∘ τ` as an exact `ElementaryIntegrand` on a refined dyadic grid, passes to the
`L²` limit via uniform elementary approximation
(`exists_seq_elementaryIntegrand_tendstoUniformlyOn`), and then sends the dyadic mesh `2⁻ᵏ → 0`
via path continuity of the integral and dominated convergence in `L²`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–D.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- Helper: on a single interval `(s, t]` with bounded `ℱ s`-measurable height `ξ`, stopping the
elementary integral at the dyadic stopping time `dyadicCeilTime k ∘ τ` at horizon `T` is realized
exactly by an `ElementaryIntegrand` whose process equals `1_{[0, σ]} · 1_{(s, t]} ξ` on `[0, T]`. -/
private theorem exists_stopped_dyadic_single
    {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    (hC : ∃ C : ℝ, ∀ ω, |ξ ω| ≤ C)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (k : ℕ) (T : ℝ≥0) :
    let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
    ∃ E : ElementaryIntegrand ℱ,
      (∀ u ≤ T, ∀ ω, E.toProcess u ω =
        if (u : WithTop ℝ≥0) ≤ σ ω then (Ioc s t).indicator (fun _ ↦ ξ ω) u else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) (ω : Ω), E.integral X T ω =
        stoppedProcess (fun u ω ↦ ξ ω * (X (min u t) ω - X (min u s) ω)) σ T ω := by
  intro σ
  by_cases hsT : s ≤ T
  · let b : ℝ≥0 := min t T
    have hsb : s ≤ b := le_min hst hsT
    have hbT : b ≤ T := min_le_right t T
    let N : ℕ := ⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1
    let p (j : ℕ) : ℝ≥0 := min b (max s ((j : ℝ≥0) / (2 : ℝ≥0) ^ k))
    have hp_mono : Monotone p := fun _ _ h ↦
      min_le_min_left b (max_le_max_left s (div_le_div_of_nonneg_right (Nat.cast_le.mpr h)
        (by positivity)))
    have hp0 : p 0 = s := by simp [p, min_eq_right hsb]
    have hp_ge (j : ℕ) : s ≤ p j := le_min hsb (le_max_left _ _)
    have hp_le (j : ℕ) : p j ≤ b := min_le_left _ _
    have hp_end : p N = b := by
      have hgt : b < (N : ℝ≥0) / (2 : ℝ≥0) ^ k := by
        rw [lt_div_iff₀ (by positivity)]
        simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (b * (2 : ℝ≥0) ^ k)
      exact min_eq_left (le_max_of_le_right hgt.le)
    -- No dyadic stopping value can fall strictly inside `(p j, p (j + 1))`.
    have hno_split (j : ℕ) (ω : Ω) (hgt : (p j : WithTop ℝ≥0) < σ ω) :
        (p (j + 1) : WithTop ℝ≥0) ≤ σ ω := by
      by_contra hnot
      have hlt : σ ω < (p (j + 1) : WithTop ℝ≥0) := lt_of_not_ge hnot
      cases hτω : τ ω with
      | top => simp only [σ, hτω, dyadicCeilTime_top] at hlt; exact not_top_lt hlt
      | coe v =>
        set r : ℕ := ⌈v * (2 : ℝ≥0) ^ k⌉₊
        have hσeq : σ ω = (↑((r : ℝ≥0) / (2 : ℝ≥0) ^ k) : WithTop ℝ≥0) := by
          simp only [σ, hτω, dyadicCeilTime_coe, r]
        rw [hσeq, WithTop.coe_lt_coe] at hgt hlt
        have hrb : (r : ℝ≥0) / (2 : ℝ≥0) ^ k < b := lt_of_lt_of_le hlt (min_le_left _ _)
        have hsr : s < (r : ℝ≥0) / (2 : ℝ≥0) ^ k := lt_of_le_of_lt (hp_ge j) hgt
        have h1 : (j : ℝ≥0) / (2 : ℝ≥0) ^ k < (r : ℝ≥0) / (2 : ℝ≥0) ^ k :=
          lt_of_le_of_lt (le_max_right _ _) ((min_lt_iff.mp hgt).resolve_left (not_lt_of_gt hrb))
        have h2 : (r : ℝ≥0) / (2 : ℝ≥0) ^ k < ((j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ k :=
          (lt_max_iff.mp (lt_of_lt_of_le hlt (min_le_right _ _))).resolve_left (not_lt_of_gt hsr)
        have hpow : (0 : ℝ≥0) < (2 : ℝ≥0) ^ k := by positivity
        have := Nat.cast_lt.mp ((div_lt_div_iff_of_pos_right hpow).mp h1)
        have := Nat.cast_lt.mp ((div_lt_div_iff_of_pos_right hpow).mp h2)
        omega
    have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime k
    let ζ : ℕ → Ω → ℝ := fun j ω ↦ if (p j : WithTop ℝ≥0) < σ ω then ξ ω else 0
    have hζ_meas (j : ℕ) (_ : j < N) : StronglyMeasurable[ℱ (p j)] (ζ j) :=
      (hξ.mono (ℱ.mono (hp_ge j))).ite
        (by convert (hσ.measurableSet_le (p j)).compl using 1
            ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le])
        stronglyMeasurable_zero
    obtain ⟨C, hC⟩ := hC
    have hζ_bdd (j : ℕ) (_ : j < N) : ∃ C' : ℝ, ∀ ω, |ζ j ω| ≤ C' :=
      ⟨max C 0, fun ω ↦ by
        dsimp only [ζ]; split_ifs
        · exact (hC ω).trans (le_max_left _ _)
        · simp⟩
    refine ⟨ElementaryIntegrand.ofSimple N p ζ (hp_mono.monotoneOn _) hζ_meas hζ_bdd,
      fun u huT ω ↦ ?_, fun X ω ↦ ?_⟩
    · rw [ElementaryIntegrand.toProcess_ofSimple]
      by_cases hu : u ∈ Ioc s b
      · obtain ⟨j₀, hj₀, hju⟩ :=
          exists_lt_mem_Ioc_of_mem_Ioc (τ := p) (n := N) (by simpa only [hp0, hp_end] using hu)
        rw [Finance.simpleHolding_of_mem_Ioc (hp_mono.monotoneOn _) hj₀ hju,
          indicator_of_mem (s := Ioc s t) ⟨hu.1, hu.2.trans (min_le_left t T)⟩]
        have hiff : (p j₀ : WithTop ℝ≥0) < σ ω ↔ (u : WithTop ℝ≥0) ≤ σ ω :=
          ⟨fun h ↦ (WithTop.coe_le_coe.mpr hju.2).trans (hno_split j₀ ω h),
            lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hju.1)⟩
        simp only [ζ, hiff]
      · rw [Finance.simpleHolding_of_notMem_Ioc (hp_mono.monotoneOn _)
            (by simpa only [hp0, hp_end] using hu),
          indicator_of_notMem (fun h : u ∈ Ioc s t ↦ hu ⟨h.1, le_min h.2 huT⟩), ite_self]
    · rw [ElementaryIntegrand.integral_ofSimple, Finance.simpleGains_def]
      have hterm (j : ℕ) :
          ζ j ω * (X (min (p (j + 1)) T) ω - X (min (p j) T) ω) =
            ξ ω * (X (min (p (j + 1) : WithTop ℝ≥0) (σ ω)).untopA ω -
              X (min (p j : WithTop ℝ≥0) (σ ω)).untopA ω) := by
        rw [min_eq_left ((hp_le (j + 1)).trans hbT), min_eq_left ((hp_le j).trans hbT)]
        by_cases hgt : (p j : WithTop ℝ≥0) < σ ω
        · simp only [ζ, hgt, ite_true, min_eq_left hgt.le, min_eq_left (hno_split j ω hgt),
            WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
        · have hle : σ ω ≤ (p j : WithTop ℝ≥0) := le_of_not_gt hgt
          have hle' := hle.trans (WithTop.coe_le_coe.mpr (hp_mono (Nat.le_succ j)))
          simp only [ζ, hgt, ite_false, zero_mul, min_eq_right hle, min_eq_right hle',
            sub_self, mul_zero]
      simp_rw [hterm, ← Finset.mul_sum, Finset.sum_range_sub (fun j ↦
        X (min (p j : WithTop ℝ≥0) (σ ω)).untopA ω) N, hp0, hp_end]
      have hcoe (x : ℝ≥0) :
          ((min (x : WithTop ℝ≥0) (σ ω)).untopA : WithTop ℝ≥0) = min (x : WithTop ℝ≥0) (σ ω) := by
        rw [WithTop.untopA_eq_untop (ne_of_lt (lt_of_le_of_lt (min_le_left _ _)
          (WithTop.coe_lt_top x))), WithTop.coe_untop]
      have hmin_eq (r : ℝ≥0) (hrT : r ≤ T) :
          min (min (T : WithTop ℝ≥0) (σ ω)).untopA r = (min (r : WithTop ℝ≥0) (σ ω)).untopA := by
        apply WithTop.coe_injective
        rw [WithTop.coe_min, hcoe T, hcoe r, min_comm (min (T : WithTop ℝ≥0) (σ ω)), ← min_assoc,
          min_eq_left (WithTop.coe_le_coe.mpr hrT)]
      have hmin_t : min (min (T : WithTop ℝ≥0) (σ ω)).untopA t =
          (min (b : WithTop ℝ≥0) (σ ω)).untopA := by
        rw [← hmin_eq b hbT]; dsimp only [b]
        rw [min_comm t T, ← min_assoc,
          min_eq_left (WithTop.untopA_le (min_le_left (T : WithTop ℝ≥0) (σ ω)))]
      simp only [stoppedProcess, hmin_t, hmin_eq s hsT]
  · -- When `T < s`, both sides vanish identically on `[0, T]`.
    have hTs : T < s := lt_of_not_ge hsT
    refine ⟨ElementaryIntegrand.zero ℱ, fun u huT ω ↦ ?_, fun X ω ↦ ?_⟩
    · simp only [ElementaryIntegrand.toProcess_zero,
        indicator_of_notMem (fun h : u ∈ Ioc s t ↦ not_lt_of_ge (huT.trans hTs.le) h.1), ite_self]
    · have hls : (min (T : WithTop ℝ≥0) (σ ω)).untopA ≤ s :=
        (WithTop.untopA_le (min_le_left _ _)).trans hTs.le
      rw [ElementaryIntegrand.integral_zero, stoppedProcess, min_eq_left (hls.trans hst),
        min_eq_left hls, sub_self, mul_zero]

/-- Stopping any `ElementaryIntegrand` at the dyadic stopping time `dyadicCeilTime k ∘ τ` at
horizon `T` is realized exactly by another `ElementaryIntegrand`. -/
private theorem exists_stopped_dyadic
    (K : ElementaryIntegrand ℱ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (k : ℕ) (T : ℝ≥0) :
    let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
    ∃ E : ElementaryIntegrand ℱ,
      (∀ u ≤ T, ∀ ω, E.toProcess u ω =
        if (u : WithTop ℝ≥0) ≤ σ ω then K.toProcess u ω else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) (ω : Ω), E.integral X T ω =
        stoppedProcess (K.integral X) σ T ω := by
  intro σ
  choose E hEP hEI using fun i : Fin K.n ↦ exists_stopped_dyadic_single (K.mono i.castSucc_le_succ)
    (K.stronglyMeasurable i) (K.bounded i) hτ k T
  suffices ∀ s : Finset (Fin K.n), ∃ M : ElementaryIntegrand ℱ,
      (∀ u ≤ T, ∀ ω, M.toProcess u ω = ∑ i ∈ s, (E i).toProcess u ω) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) (ω : Ω), M.integral X T ω = ∑ i ∈ s, (E i).integral X T ω by
    obtain ⟨M, hMP, hMI⟩ := this Finset.univ
    refine ⟨M, fun u huT ω ↦ ?_, fun X ω ↦ ?_⟩
    · rw [hMP u huT ω, K.toProcess_def]; simp_rw [hEP _ u huT ω]; split_ifs <;> simp
    · rw [hMI X ω]; simp_rw [hEI _ X ω, stoppedProcess, K.integral_def]; rfl
  intro s
  classical
  induction s using Finset.induction with
  | empty => exact ⟨ElementaryIntegrand.zero ℱ, by simp, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨M, hMP, hMI⟩ := ih
    obtain ⟨M', hP', hI'⟩ := (E a).exists_add M
    exact ⟨M', fun u huT ω ↦ by rw [hP', hMP u huT ω, Finset.sum_insert ha],
      fun X ω ↦ by rw [hI', hMI X ω, Finset.sum_insert ha]⟩

/-- For a `BrownianIntegrable` integrand, stopping its Itô integral at any stopping time `τ`
agrees almost surely at every horizon `T` with the L² Brownian integral of the cutoff integrand
`1_{[0, τ]} · H`. -/
theorem stoppedProcess_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) :
    stoppedProcess I τ T =ᵐ[P]
      hW.l2Integral T (((hH.ite_le hτ).memLp_predictableMeasure T).toLp
        (Function.uncurry fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hKlim, hunif⟩ := hW.exists_seq_elementaryIntegrand_tendstoUniformlyOn hcont hH hI
  -- Step 1: prove the identity for every dyadic approximation `σ k := dyadicCeilTime k ∘ τ`.
  have hdyad (k : ℕ) :
      stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T =ᵐ[P]
        hW.l2Integral T (((hH.ite_le (hτ.dyadicCeilTime k)).memLp_predictableMeasure T).toLp
          (Function.uncurry fun t ω ↦
            if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then H t ω else 0)) := by
    let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
    have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime k
    choose K' hK'P hK'I using fun n ↦ exists_stopped_dyadic (K n) hτ k T
    have hlim_ae : TendstoInMeasure P (fun n ↦ (K' n).integral W T) atTop
        (stoppedProcess I σ T) := by
      refine tendstoInMeasure_of_tendsto_ae (fun n ↦
        (((K' n).stronglyAdapted_integral hW.adapted.stronglyAdapted T).mono
          (ℱ.le T)).aestronglyMeasurable) ?_
      filter_upwards [hunif] with ω hω
      simpa only [hK'I, stoppedProcess] using
        (hω T).tendsto_at (Set.mem_Iic.mpr (WithTop.untopA_le (min_le_left _ _)))
    let Hσ : ℝ≥0 → Ω → ℝ := fun t ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0
    have hlim_L2 : Tendsto (fun n ↦ eLpNorm (fun ω ↦ (K' n).integral W T ω -
        hW.l2Integral T (((hH.ite_le hσ).memLp_predictableMeasure T).toLp (Function.uncurry Hσ)) ω)
        2 P) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hKlim T)
        (fun _ ↦ zero_le) fun n ↦ ?_
      rw [hW.eLpNorm_elementaryIntegrand_sub_l2Integral (K' n) (hH.ite_le hσ) T]
      refine eLpNorm_mono_ae
        ((((K' n).isStronglyPredictable_toProcess.sub (hH.ite_le hσ).isStronglyPredictable).mono
          ℱ.predictable_le_prod).aestronglyMeasurable) ?_
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := P)).ae
        ((ae_mem_Ioc_timeMeasure T).mono fun _ h ↦ h.2)] with ⟨u, ω⟩ hu
      dsimp only [Hσ]; rw [hK'P n u hu ω]; split_ifs <;> simp
    exact tendstoInMeasure_ae_unique hlim_ae
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hlim_L2)
  -- Step 2: let `k → ∞` using path continuity of `I` on the left and dominated convergence
  -- on the right.
  let Hk (k : ℕ) : ℝ≥0 → Ω → ℝ :=
    fun t ω ↦ if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then H t ω else 0
  let Hτ : ℝ≥0 → Ω → ℝ := fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0
  have hLHS : TendstoInMeasure P
      (fun k ↦ stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T) atTop
      (stoppedProcess I τ T) :=
    tendstoInMeasure_of_tendsto_ae (fun k ↦ (Lp.aestronglyMeasurable _).congr (hdyad k).symm)
      (hI.ae_continuous.mono fun ω hω ↦
        tendsto_stoppedProcess_dyadicCeilTime I τ T ω hω.continuousAt.continuousWithinAt)
  have hRHS_eLp : Tendsto (fun k ↦ eLpNorm
      (Function.uncurry (Hk k) - Function.uncurry Hτ) 2 ((timeMeasure T).prod P))
      atTop (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (.of_forall fun k ↦ by
        simpa only [NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def] using
          ((hH.ite_le (hτ.dyadicCeilTime k)).memLp T).aestronglyMeasurable)
      (by simpa only [NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def] using hH.memLp T)
      (.of_forall fun k ↦ .of_forall fun p ↦ by
        dsimp only [Hk, Hτ, Function.uncurry]; split_ifs <;> simp)
      (.of_forall fun p ↦ ?_)
    dsimp only [Hk, Hτ, Function.uncurry]
    by_cases hp : (p.1 : WithTop ℝ≥0) ≤ τ p.2
    · exact tendsto_const_nhds.congr fun k ↦ by
        simp only [hp, hp.trans (le_dyadicCeilTime k (τ p.2)), ite_true]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_dyadicCeilTime (τ p.2)).eventually
        (eventually_lt_nhds (lt_of_not_ge hp))] with k hk
      simp only [hp, not_le.mpr hk, ite_false]
  have hRHS : TendstoInMeasure P
      (fun k ↦ stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T) atTop
      (hW.l2Integral T (((hH.ite_le hτ).memLp_predictableMeasure T).toLp (Function.uncurry Hτ))) :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (hRHS_eLp.congr fun k ↦
        (hW.eLpNorm_l2Integral_sub (hH.ite_le (hτ.dyadicCeilTime k)) (hH.ite_le hτ) T).symm)
    ).congr_left fun k ↦ (hdyad k).symm
  exact tendstoInMeasure_ae_unique hLHS hRHS

/-- **Stopping compatibility for L² Brownian Itô integrals.** Stopping an Itô integral of a
`BrownianIntegrable` integrand at any stopping time `τ` produces an Itô integral of the cutoff
integrand `1_{[0, τ]} · H`. No usual filtration conditions are required. -/
theorem isItoIntegral_stoppedProcess_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (stoppedProcess I τ) := by
  obtain ⟨J, hJito, -, -, -⟩ :=
    hW.exists_isItoIntegral_of_brownianIntegrable hcont (hH.ite_le hτ)
  exact hJito.congr_indist (indist_of_ae_eq_of_ae_continuous
    (hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess) hJito.ae_continuous fun T ↦
      (hW.stoppedProcess_ae_eq_l2Integral hcont hH hI hτ T).trans
        (hW.ae_eq_l2Integral_of_isItoIntegral (hH.ite_le hτ) hJito T).symm).symm

end TauCeti.Probability.IsFilteredPreBrownianReal
