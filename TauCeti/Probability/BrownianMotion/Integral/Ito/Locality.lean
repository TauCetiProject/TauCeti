/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Localization
import all TauCeti.Probability.BrownianMotion.Integral.Ito.Localization
import TauCeti.Probability.BrownianMotion.Integral.Locality
import TauCeti.Probability.Process.Indistinguishable

/-!
# Event locality for the Brownian Itô integral

For a filtration-relative Brownian motion `W` with almost surely continuous paths, multiplying the
integrand of a Brownian Itô integral `I` after a deterministic time `s` by an arbitrary
`ℱ s`-measurable random variable `ξ` scales the post-`s` increment `I t - I (min s t)` by `ξ`
(`isItoIntegral_ite_lt_mul`, `itoIntegral_ite_lt_mul_indist`), without any boundedness or moment
assumption on `ξ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D, §3.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W H I J : ℝ≥0 → Ω → ℝ}

private theorem isStoppingTime_ite_norm_le (s : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (m : ℕ) :
    IsStoppingTime ℱ (fun ω ↦ if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s) := by
  intro t
  have hmeas : MeasurableSet[ℱ s] {ω | ‖ξ ω‖ ≤ (m : ℝ)} := by
    let : MeasurableSpace Ω := ℱ s
    exact hξ.measurable.norm measurableSet_Iic
  by_cases hst : s ≤ t
  · have heq : {ω | (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s) ≤ (t : WithTop ℝ≥0)} =
        {ω | ‖ξ ω‖ ≤ (m : ℝ)}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
      by_cases h : ‖ξ ω‖ ≤ (m : ℝ)
      · rw [ite_eq_left h]
        exact iff_of_false (WithTop.not_top_le_coe t) (not_not.mpr h)
      · rw [ite_eq_right h]
        exact iff_of_true (WithTop.coe_le_coe.mpr hst) h
    rw [heq]
    exact ℱ.mono hst _ hmeas.compl
  · have heq : {ω | (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s) ≤ (t : WithTop ℝ≥0)} =
        ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun ω ↦ ?_
      simp only [Set.mem_ofPred_eq]
      by_cases h : ‖ξ ω‖ ≤ (m : ℝ)
      · rw [ite_eq_left h]
        exact not_le.mpr (WithTop.coe_lt_top t)
      · rw [ite_eq_right h]
        exact not_le.mpr (WithTop.coe_lt_coe.mpr (not_le.mp hst))
    rw [heq]
    exact @MeasurableSet.empty Ω (ℱ t)

private theorem isLocalizingSequence_min_ite_norm_le {τ₁ : ℕ → Ω → WithTop ℝ≥0}
    (hloc₁ : IsLocalizingSequence ℱ τ₁ P) (s : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsLocalizingSequence ℱ
      (fun m ω ↦ min (τ₁ m ω) (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s)) P := by
  let τ₂ (m : ℕ) (ω : Ω) : WithTop ℝ≥0 := if ‖ξ ω‖ ≤ (m : ℝ) then ⊤ else s
  have hτ₂_mono (ω : Ω) : Monotone (fun m ↦ τ₂ m ω) := fun m n hmn ↦ by
    by_cases hm : ‖ξ ω‖ ≤ (m : ℝ)
    · have hn : ‖ξ ω‖ ≤ (n : ℝ) := hm.trans (by exact_mod_cast hmn)
      dsimp only [τ₂]
      rw [ite_eq_left hm, ite_eq_left hn]
    · simp only [τ₂, ite_eq_right hm]
      split_ifs
      · exact le_top
      · exact le_rfl
  have hτ₂_top (ω : Ω) : Tendsto (fun m ↦ τ₂ m ω) atTop (𝓝 ⊤) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖ξ ω‖
    exact tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun m hm ↦ by
      have hle : ‖ξ ω‖ ≤ (m : ℝ) := hN.trans (by exact_mod_cast hm)
      dsimp only [τ₂]
      exact (ite_eq_left hle).symm)
  refine ⟨⟨fun m ↦ (hloc₁.isStoppingTime m).min (isStoppingTime_ite_norm_le s hξ m), ?_⟩, ?_⟩
  · filter_upwards [hloc₁.tendsto_top] with ω hω
    refine (WithTop.tendsto_nhds_top_iff _).mpr fun t ↦ ?_
    filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp hω t,
      (WithTop.tendsto_nhds_top_iff _).mp (hτ₂_top ω) t] with m hm₁ hm₂
    exact lt_min hm₁ hm₂
  · filter_upwards [hloc₁.mono] with ω hω m n hmn
    exact min_le_min (hω hmn) (hτ₂_mono ω hmn)

private theorem stoppedProcess_ite_lt_mul_indist {X U : ℝ≥0 → Ω → ℝ} {τ₁ : Ω → WithTop ℝ≥0}
    (hX_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    (hU_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ U t ω))
    (hX_stop : stoppedProcess X τ₁ ≡ᵐ[P] U) (s : ℝ≥0) (ξ : Ω → ℝ) (m : ℕ) :
    stoppedProcess (fun t ω ↦ ξ ω * (X t ω - X (min s t) ω))
      (fun ω ↦ min (τ₁ ω) (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s)) ≡ᵐ[P]
        fun t ω ↦ (if ‖ξ ω‖ ≤ (m : ℝ) then ξ ω else 0) * (U t ω - U (min s t) ω) := by
  have hY_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ ξ ω * (X t ω - X (min s t) ω)) :=
    hX_cont.mono fun _ hc ↦
      continuous_const.mul (hc.sub (hc.comp (continuous_const.min continuous_id)))
  refine TauCeti.indist_of_ae_continuous (hY_cont.mono fun _ hc ↦ hc.stoppedProcess)
    (hU_cont.mono fun _ hc ↦
      continuous_const.mul (hc.sub (hc.comp (continuous_const.min continuous_id)))) fun t ↦ ?_
  filter_upwards [hX_stop.ae_eq_eval t, hX_stop.ae_eq_eval (min s t)] with ω ht hmin
  by_cases hm : ‖ξ ω‖ ≤ (m : ℝ)
  · have hτ_eq : min (τ₁ ω) (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s) = τ₁ ω :=
      min_eq_left (by rw [ite_eq_left hm]; exact le_top)
    have hmin_eq : min s (min (t : WithTop ℝ≥0) (τ₁ ω)).untopA =
        (min ((min s t : ℝ≥0) : WithTop ℝ≥0) (τ₁ ω)).untopA := by
      cases τ₁ ω with
      | top =>
        rw [min_top_right, min_top_right]
        simp only [WithTop.untopA, WithTop.untopD_coe]
      | coe r =>
        rw [← WithTop.coe_min, ← WithTop.coe_min]
        simp only [WithTop.untopA, WithTop.untopD_coe, min_assoc]
    dsimp only [stoppedProcess]
    rw [hτ_eq, ite_eq_left hm, hmin_eq, ← ht, ← hmin]
    rfl
  · have hτ_le : min (τ₁ ω) (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s) ≤
        (s : WithTop ℝ≥0) :=
      (min_le_right _ _).trans_eq (ite_eq_right hm)
    have hu_lt : min (t : WithTop ℝ≥0)
        (min (τ₁ ω) (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s)) ≠ ⊤ :=
      ne_of_lt ((min_le_left _ _).trans_lt (WithTop.coe_lt_top t))
    have hu_le : (min (t : WithTop ℝ≥0)
        (min (τ₁ ω) (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s))).untopA ≤ s := by
      lift min (t : WithTop ℝ≥0)
          (min (τ₁ ω) (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s)) to ℝ≥0
        using hu_lt with u hu
      exact WithTop.coe_le_coe.mp (hu ▸ (min_le_right _ _).trans hτ_le)
    have hmin_eq : min s (min (t : WithTop ℝ≥0)
        (min (τ₁ ω) (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s))).untopA =
        (min (t : WithTop ℝ≥0)
          (min (τ₁ ω) (if ‖ξ ω‖ ≤ (m : ℝ) then (⊤ : WithTop ℝ≥0) else s))).untopA :=
      min_eq_right hu_le
    dsimp only [stoppedProcess]
    rw [hmin_eq, sub_self, mul_zero, ite_eq_right hm, zero_mul]

/-- **Deterministic-time measurable multiplier law for the Brownian Itô integral.** Multiplying
an integrand after a deterministic time `s` by an `ℱ s`-measurable random variable `ξ` scales the
post-`s` increment `I t - I (min s t)` by `ξ`. No boundedness or moment assumption on `ξ` is
required. -/
theorem isItoIntegral_ite_lt_mul
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I)
    (s : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if s < t then ξ ω * H t ω else 0)
      (fun t ω ↦ ξ ω * (I t ω - I (min s t) ω)) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  -- 1. Patch the energy localizer stages `(X, U)` and localize simultaneously by `‖ξ‖ ≤ m`.
  have hH : LocallyBrownianIntegrable ℱ P H := hI.locallyBrownianIntegrable
  obtain ⟨X, U, _, hX_cont, _, hX_ito, _, hUcont, hUae, hX_stop⟩ :=
    hW.exists_patched_energyLocalizer_process hcont hH
  let τ₁ (m : ℕ) := TauCeti.nnvolume.energyLocalizer H ((m : ℝ≥0) + 1)
  let τ₂ (m : ℕ) (ω : Ω) : WithTop ℝ≥0 := if ‖ξ ω‖ ≤ (m : ℝ) then ⊤ else s
  let τ (m : ℕ) (ω : Ω) : WithTop ℝ≥0 := min (τ₁ m ω) (τ₂ m ω)
  have hloc : IsLocalizingSequence ℱ τ P :=
    isLocalizingSequence_min_ite_norm_le hH.isLocalizingSequence_energyLocalizer s hξ
  -- 2. Truncate `ξ` to bounded `ξ_m` and match stopped `Y` with the scaled `L²` stage integrals.
  let ξ_m (m : ℕ) (ω : Ω) : ℝ := if ‖ξ ω‖ ≤ (m : ℝ) then ξ ω else 0
  have hξ_m (m : ℕ) : StronglyMeasurable[ℱ s] (ξ_m m) := by
    let : MeasurableSpace Ω := ℱ s
    exact hξ.ite (hξ.measurable.norm measurableSet_Iic) stronglyMeasurable_const
  have hξ_m_bd (m : ℕ) : MemLp (ξ_m m) ∞ P :=
    memLp_top_of_bound ((hξ_m m).mono (ℱ.le s)).aestronglyMeasurable (m : ℝ)
      (Eventually.of_forall fun ω ↦ by
        by_cases h : ‖ξ ω‖ ≤ (m : ℝ)
        · dsimp only [ξ_m]; rwa [ite_eq_left h]
        · dsimp only [ξ_m]; rw [ite_eq_right h, norm_zero]; exact Nat.cast_nonneg m)
  let Hbase (m : ℕ) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P) ((m : ℝ≥0) + 1)
  let Hstage (m : ℕ) : ℝ≥0 → Ω → ℝ := fun t ω ↦
    if s < t then ξ_m m ω * (if (t : WithTop ℝ≥0) ≤ τ₁ m ω then
      TauCeti.nnvolume.finiteEnergyCutoff H t ω else 0) else 0
  have hHstage (m : ℕ) : BrownianIntegrable ℱ P (Hstage m) :=
    (Hbase m).ite_lt_mul s (hξ_m m) (hξ_m_bd m)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ ξ ω * (X t ω - X (min s t) ω)
  let V (m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ := ξ_m m ω * (U m t ω - U m (min s t) ω)
  have hY_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω) := hX_cont.mono fun _ hc ↦
    continuous_const.mul (hc.sub (hc.comp (continuous_const.min continuous_id)))
  have hUae' (m : ℕ) (t : ℝ≥0) : V m t =ᵐ[P] hW.l2Integral t ((hHstage m).toPredictableLp t) := by
    have hmul := hW.coeFn_l2Integral_ite_lt_mul_eq_mul_sub (Hbase m) s t (hξ_m m) (hξ_m_bd m)
    filter_upwards [hmul, hUae m t, hUae m (min s t)] with ω hω ht hmin
    exact (congrArg (fun x ↦ ξ_m m ω * x) (congrArg₂ Sub.sub ht hmin)).trans hω.symm
  have hstop (m : ℕ) : stoppedProcess Y (τ m) ≡ᵐ[P] V m :=
    stoppedProcess_ite_lt_mul_indist hX_cont (hUcont m) (hX_stop m) s ξ m
  -- 3. Verify `IsItoIntegral` for `Y` via localized stages, then transfer to `I`.
  have hY_ito : IsItoIntegral ℱ P W (fun t ω ↦ if s < t then ξ ω * H t ω else 0) Y := by
    refine hW.isItoIntegral_of_localized_stages
      (hH.ite_lt_mul s hξ).isStronglyPredictable hY_cont hloc hHstage hUae' hstop fun t ↦ ?_
    filter_upwards [hH.ae_accumulatedEnergy_lt_top] with ω hfin m hlt u hu
    by_cases hsu : s < u
    · have hs_lt_t : s < t := hsu.trans_le hu
      have hτ_gt_s : (s : WithTop ℝ≥0) < τ₂ m ω :=
        (WithTop.coe_lt_coe.mpr hs_lt_t).trans (hlt.trans_le (min_le_right _ _))
      have hm : ‖ξ ω‖ ≤ (m : ℝ) := by
        by_contra hnot
        have : τ₂ m ω = (s : WithTop ℝ≥0) := ite_eq_right hnot
        exact absurd (this ▸ hτ_gt_s) (lt_irrefl _)
      have hle₁ : (u : WithTop ℝ≥0) ≤ τ₁ m ω :=
        (WithTop.coe_le_coe.mpr (mem_Iic.mp hu)).trans (hlt.trans_le (min_le_left _ _)).le
      have hcut : TauCeti.nnvolume.finiteEnergyCutoff H u ω = H u ω :=
        TauCeti.nnvolume.finiteEnergyCutoff_eqOn (hfin t) hu
      simp only [Hstage, ite_eq_left hsu, ξ_m, ite_eq_left hm, ite_eq_left hle₁, hcut]
    · simp [Hstage, hsu]
  refine hY_ito.congr ?_
  filter_upwards [isItoIntegral_unique hW hX_ito hI] with ω hω
  intro t
  simp [Y, hω t, hω (min s t)]

/-- Indistinguishability form of `isItoIntegral_ite_lt_mul`. -/
theorem itoIntegral_ite_lt_mul_indist
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hI : IsItoIntegral ℱ P W H I)
    (s : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    (hJ : IsItoIntegral ℱ P W (fun t : ℝ≥0 ↦ fun ω ↦ if s < t then ξ ω * H t ω else 0) J) :
    J ≡ᵐ[P] fun t ω ↦ ξ ω * (I t ω - I (min s t) ω) :=
  isItoIntegral_unique hW hJ (hW.isItoIntegral_ite_lt_mul hcont hI s hξ)

end TauCeti.Probability.IsFilteredPreBrownianReal
