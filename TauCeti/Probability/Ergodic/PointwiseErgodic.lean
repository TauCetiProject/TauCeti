/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

import Mathlib.Dynamics.BirkhoffSum.Maximal
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Dynamics.BirkhoffSum.Limsup
import TauCeti.Dynamics.BirkhoffSum.Maximal
import TauCeti.Dynamics.BirkhoffSum.Norm
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Probability.Ergodic.BirkhoffLp
import TauCeti.Probability.Ergodic.CondExpProjection
import TauCeti.Probability.Ergodic.InvariantSigma

/-!
# Birkhoff's pointwise and `Lᵖ` ergodic theorems

This file establishes Birkhoff's pointwise ergodic theorem and the accompanying `Lᵖ` (`1 ≤ p < ∞`)
ergodic theorem for a measure-preserving endomorphism `T` of a finite measure space `(Ω, μ)` and
an observable `f : Ω → E` taking values in a real Banach space `E`.

The proof for real-valued observables follows the standard maximal-ergodic route (as in Garsia's
presentation of Hopf's maximal ergodic theorem, Billingsley's *Ergodic Theory and Information*, and
Einsiedler–Ward, *Ergodic Theory*, Chapter 2): Mathlib's maximal ergodic theorem
(`mul_measureReal_lt_birkhoffAverageSup_le_integral` and
`mul_measureReal_lt_birkhoffAverageSup_le_norm`) shows that the upper and lower `EReal` limits of
`birkhoffAverage ℝ T g n` are almost everywhere finite and equal. On measurable indicators, this
almost-everywhere limit is identified with the conditional expectation
`μ[f | MeasurableSpace.invariants T]` by comparing convergence in measure against the `L²` mean
ergodic theorem (`TauCeti.Probability.tendsto_eLpNorm_birkhoffAverage_sub_condExp`). Extending from
indicators to an arbitrary real Banach space `E` requires no separability hypothesis: pointwise
convergence holds on simple functions by linearity and transfers to all `Integrable` functions via
`L¹`-density of simple functions and the weak-type maximal inequality; `Lᵖ` convergence for
`1 ≤ p < ∞` follows from `Lᵖ` dominated convergence (`TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto`)
on simple functions together with `Lᵖ`-contractivity of Birkhoff averages and conditional
expectations.

Supporting general-purpose lemmas live in their canonical homes: pointwise norm bounds in
`TauCeti.Dynamics.BirkhoffSum.Norm`, orbit invariance of `limsup`/`liminf` in
`TauCeti.Dynamics.BirkhoffSum.Limsup`, maximal ergodic operator bounds and a.e. finiteness in
`TauCeti.Dynamics.BirkhoffSum.Maximal`, integral invariance and `Lᵖ`/`L¹` contractivity of
Birkhoff averages in `TauCeti.Probability.Ergodic.BirkhoffLp`, and the pre-ergodic conditional
expectation collapse in `TauCeti.Probability.Ergodic.InvariantSigma`.

For ergodic transformations, the invariant σ-algebra is `μ`-trivial, so the conditional expectation
collapses to the space average `⨍ y, f y ∂μ`, yielding the ergodic pointwise, `Lᵖ`, `L¹`, and
visiting-frequency theorems.

## Main results

* `MeasureTheory.MeasurePreserving.ae_tendsto_birkhoffAverage_condExp` — **Birkhoff's pointwise
  ergodic theorem** for Banach-valued integrable observables on a finite measure space.
* `MeasureTheory.MeasurePreserving.tendsto_eLpNorm_birkhoffAverage_sub_condExp` — **`Lᵖ` ergodic
  theorem** (`1 ≤ p < ∞`) for Banach-valued observables on a finite measure space.
* `MeasureTheory.MeasurePreserving.tendsto_integral_norm_birkhoffAverage_sub_condExp` — **`L¹`
  ergodic theorem** in integral-norm form.
* `Ergodic.ae_tendsto_birkhoffAverage_average` — pointwise ergodic theorem for ergodic maps.
* `Ergodic.tendsto_eLpNorm_birkhoffAverage_sub_average` and
  `Ergodic.tendsto_integral_norm_birkhoffAverage_sub_average` — `Lᵖ` and `L¹` ergodic convergence
  for ergodic maps.
* `Ergodic.ae_tendsto_card_filter_iterate_mem_div` — almost-everywhere convergence of orbit
  visiting frequencies to normalized measure.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

section RealBirkhoffHelpers

/-! ## Private helpers for the real-valued pointwise ergodic theorem -/

private lemma mul_measureReal_le_setIntegral_of_lt_limsup {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg : Integrable g μ) {E : Set Ω}
    (hE : MeasurableSet[MeasurableSpace.invariants T] E) {b : ℝ}
    (hb : ∀ x ∈ E,
      (b : EReal) < limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop) :
    b * μ.real E ≤ ∫ x in E, g x ∂μ := by
  let ν : Measure Ω := μ.restrict E
  have hTν : MeasurePreserving T ν ν := by
    simpa only [ν, hE.2] using hT.restrict_preimage hE.1
  have hsub : E ⊆ {x | 0 < birkhoffAverageSup T (g - fun _ ↦ b) x} := by
    intro x hx
    have hfreq : ∃ᶠ n in atTop, (b : EReal) < ((birkhoffAverage ℝ T g n x : ℝ) : EReal) :=
      frequently_lt_of_lt_limsup (by isBoundedDefault) (hb x hx)
    obtain ⟨n, hbn, hn1⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
    have hnpos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have havg_pos : 0 < birkhoffAverage ℝ T (g - fun _ ↦ b) n x := by
      rw [birkhoffAverage_sub_apply, birkhoffAverage_const ℝ T b hnpos, sub_pos]
      exact EReal.coe_lt_coe_iff.mp hbn
    exact (EReal.coe_pos.mpr havg_pos).trans_le
      (le_iSup (fun k ↦ ((birkhoffAverage ℝ T (g - fun _ ↦ b) k x : ℝ) : EReal)) n)
  have hmax : 0 * ν.real {x | 0 < birkhoffAverageSup T (g - fun _ ↦ b) x} ≤
      ∫ x in {x | 0 < birkhoffAverageSup T (g - fun _ ↦ b) x}, (g x - b) ∂ν :=
    mul_measureReal_lt_birkhoffAverageSup_le_integral ν hTν
      (hg.sub (integrable_const b)).integrableOn 0 le_rfl
  have hrestrict : ν.restrict {x | 0 < birkhoffAverageSup T (g - fun _ ↦ b) x} = μ.restrict E :=
    Measure.restrict_eq_self_of_ae_mem (ae_restrict_of_forall_mem hE.1 hsub)
  rw [zero_mul, hrestrict, integral_sub hg.integrableOn integrableOn_const, setIntegral_const,
    smul_eq_mul, sub_nonneg, mul_comm] at hmax
  exact hmax

private lemma measure_liminf_lt_and_lt_limsup_birkhoffAverage_eq_zero {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : Ω → ℝ} (hg_meas : Measurable g) (hg : Integrable g μ)
    {a b : ℝ} (hab : a < b) :
    μ {x | liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop < (a : EReal) ∧
      (b : EReal) < limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop} = 0 := by
  let fInf : Ω → EReal :=
    fun x ↦ liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop
  let fSup : Ω → EReal :=
    fun x ↦ limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop
  set E := {x | fInf x < (a : EReal) ∧ (b : EReal) < fSup x}
  have hfInf_meas : Measurable fInf :=
    Measurable.liminf fun _ ↦
      measurable_coe_real_ereal.comp (measurable_birkhoffAverage hT.measurable hg_meas)
  have hfSup_meas : Measurable fSup :=
    Measurable.limsup fun _ ↦
      measurable_coe_real_ereal.comp (measurable_birkhoffAverage hT.measurable hg_meas)
  have hE : MeasurableSet[MeasurableSpace.invariants T] E := by
    refine ⟨(hfInf_meas measurableSet_Iio).inter (hfSup_meas measurableSet_Ioi), ?_⟩
    ext x
    simp only [E, Set.mem_preimage, Set.mem_ofPred_eq, fInf, fSup,
      TauCeti.liminf_birkhoffAverage_comp, TauCeti.limsup_birkhoffAverage_comp]
  have hlow : b * μ.real E ≤ ∫ x in E, g x ∂μ :=
    mul_measureReal_le_setIntegral_of_lt_limsup hT hg hE fun _ hx ↦ hx.2
  have hhigh_neg : (-a) * μ.real E ≤ ∫ x in E, (-g x) ∂μ := by
    refine mul_measureReal_le_setIntegral_of_lt_limsup hT hg.neg hE fun x hx ↦ ?_
    have h2 := hx.1
    dsimp only [fInf] at h2
    have hfun : (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) =
        -(fun n ↦ ((birkhoffAverage ℝ T (-g) n x : ℝ) : EReal)) := by
      ext n; simp [birkhoffAverage_neg_apply]
    rw [hfun, EReal.liminf_neg, ← EReal.neg_lt_neg_iff, neg_neg] at h2
    simpa [EReal.coe_neg] using h2
  rw [integral_neg] at hhigh_neg
  have hzero : μ.real E = 0 := by nlinarith [measureReal_nonneg (μ := μ) (s := E)]
  exact (measureReal_eq_zero_iff (measure_ne_top μ E)).mp hzero

private lemma ae_liminf_eq_limsup_birkhoffAverage {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ,
      liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop =
        limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop := by
  let fInf : Ω → EReal :=
    fun x ↦ liminf (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop
  let fSup : Ω → EReal :=
    fun x ↦ limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop
  have hall : ∀ᵐ x ∂μ, ∀ a b : ℚ,
      a < b → ¬ (fInf x < ((a : ℝ) : EReal) ∧ ((b : ℝ) : EReal) < fSup x) := by
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro b
    by_cases hab : a < b
    · have hae : ∀ᵐ x ∂μ, ¬ (fInf x < ((a : ℝ) : EReal) ∧ ((b : ℝ) : EReal) < fSup x) := by
        rw [ae_iff]
        simpa only [not_not] using measure_liminf_lt_and_lt_limsup_birkhoffAverage_eq_zero hT
          hg_meas hg (Rat.cast_lt.mpr hab)
      exact hae.mono fun _ hx _ ↦ hx
    · exact ae_of_all _ fun _ h ↦ (hab h).elim
  filter_upwards [hall] with x hx
  refine le_antisymm (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)) ?_
  by_contra! hlt
  obtain ⟨r₁, hr₁, hr₂⟩ := EReal.exists_between_coe_real hlt
  obtain ⟨r₂, hr₂1, hr₂2⟩ := EReal.exists_between_coe_real hr₂
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (EReal.coe_lt_coe_iff.mp hr₂1)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn ha2
  exact hx a b (Rat.cast_lt.mp hb1)
    ⟨hr₁.trans (EReal.coe_lt_coe_iff.mpr ha1), (EReal.coe_lt_coe_iff.mpr hb2).trans hr₂2⟩

private lemma ae_tendsto_birkhoffAverage_real_limit {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T g n x) atTop
      (𝓝 (limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop).toReal) := by
  filter_upwards [ae_liminf_eq_limsup_birkhoffAverage hT hg_meas hg,
    hT.ae_birkhoffAverageSup_norm_lt_top hg] with x heq hfin
  set L : EReal := limsup (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop
  have hbound (n : ℕ) :
      |(birkhoffAverage ℝ T g n x : ℝ)| ≤ birkhoffAverage ℝ T (fun y ↦ ‖g y‖) n x := by
    simpa [Real.norm_eq_abs] using TauCeti.norm_birkhoffAverage_le_birkhoffAverage_norm T g n x
  have htop : L < ⊤ := by
    refine lt_of_le_of_lt ?_ hfin
    exact (limsup_le_limsup (Eventually.of_forall fun n ↦
      EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hbound n)))).trans limsup_le_iSup
  have hbot : ⊥ < L := by
    have hle : -(birkhoffAverageSup T (fun y ↦ ‖g y‖) x) ≤ L := by
      rw [← heq]
      refine le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun n ↦ ?_)
      have h1 : -((birkhoffAverage ℝ T (fun y ↦ ‖g y‖) n x : ℝ) : EReal) ≤
          ((birkhoffAverage ℝ T g n x : ℝ) : EReal) := by
        rw [← EReal.coe_neg, EReal.coe_le_coe_iff]
        linarith [neg_abs_le (birkhoffAverage ℝ T g n x), hbound n]
      exact (EReal.neg_le_neg_iff.mpr
        (le_iSup (fun k ↦ ((birkhoffAverage ℝ T (fun y ↦ ‖g y‖) k x : ℝ) : EReal)) n)).trans h1
    have hneg_bot : (⊥ : EReal) < -(birkhoffAverageSup T (fun y ↦ ‖g y‖) x) := by
      rw [← EReal.neg_top, EReal.neg_lt_neg_iff]
      exact hfin
    exact hneg_bot.trans_le hle
  have htend_ereal : Tendsto (fun n ↦ ((birkhoffAverage ℝ T g n x : ℝ) : EReal)) atTop
      (𝓝 (L.toReal : EReal)) := by
    rw [EReal.coe_toReal htop.ne hbot.ne']
    exact tendsto_of_le_liminf_of_limsup_le heq.ge le_rfl
  exact EReal.tendsto_coe.mp htend_ereal

end RealBirkhoffHelpers

section BanachBirkhoffHelpers

/-! ## Private helpers extending Birkhoff's theorem to Banach-valued observables -/

private lemma ae_tendsto_birkhoffAverage_condExp_simpleFunc {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (s : SimpleFunc Ω E) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T s n x) atTop
      (𝓝 (μ[s | MeasurableSpace.invariants T] x)) := by
  induction s using SimpleFunc.induction with
  | @const c t ht =>
    let φ : Ω → ℝ := t.indicator 1
    let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c
    have hφ_meas : Measurable φ := measurable_one.indicator ht
    have hφ_int : Integrable φ μ := (integrable_const (1 : ℝ)).indicator ht
    have hφ_memLp2 : MemLp φ 2 μ := (memLp_const (1 : ℝ)).indicator ht.nullMeasurableSet
    let lim : Ω → ℝ :=
      fun x ↦ (limsup (fun n ↦ ((birkhoffAverage ℝ T φ n x : ℝ) : EReal)) atTop).toReal
    have hae : ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T φ n x) atTop (𝓝 (lim x)) :=
      ae_tendsto_birkhoffAverage_real_limit hT hφ_meas hφ_int
    have hmeas_in : TendstoInMeasure μ (birkhoffAverage ℝ T φ) atTop lim :=
      tendstoInMeasure_of_tendsto_ae
        (fun _ ↦ (measurable_birkhoffAverage hT.measurable hφ_meas).aestronglyMeasurable) hae
    have hL2_in : TendstoInMeasure μ (birkhoffAverage ℝ T φ) atTop
        (μ[φ | MeasurableSpace.invariants T]) :=
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (TauCeti.Probability.tendsto_eLpNorm_birkhoffAverage_sub_condExp T hT hφ_memLp2 hφ_int)
    have hlim_eq : lim =ᵐ[μ] μ[φ | MeasurableSpace.invariants T] :=
      tendstoInMeasure_ae_unique hmeas_in hL2_in
    have hφ_ae : ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T φ n x) atTop
        (𝓝 (μ[φ | MeasurableSpace.invariants T] x)) := by
      filter_upwards [hae, hlim_eq] with x hx hxeq
      rwa [← hxeq]
    have hfun : (SimpleFunc.piecewise t ht (SimpleFunc.const Ω c) (SimpleFunc.const Ω 0) : Ω → E) =
        L ∘ φ := by
      ext x
      by_cases hx : x ∈ t <;> simp [φ, L, hx]
    rw [hfun]
    filter_upwards [hφ_ae,
      L.comp_condExp_comm hφ_int (m := MeasurableSpace.invariants T)] with x hx hcomm
    have h1 : Tendsto (fun n ↦ L (birkhoffAverage ℝ T φ n x)) atTop
        (𝓝 (L (μ[φ | MeasurableSpace.invariants T] x))) := (L.continuous.tendsto _).comp hx
    have hcomm' : L (μ[φ | MeasurableSpace.invariants T] x) =
        μ[L ∘ φ | MeasurableSpace.invariants T] x := hcomm
    rw [hcomm'] at h1
    exact h1.congr fun n ↦ map_birkhoffAverage ℝ ℝ L T φ n x
  | @add s₁ s₂ _ h₁ h₂ =>
    have hs₁ : Integrable (s₁ : Ω → E) μ := s₁.integrable_of_isFiniteMeasure
    have hs₂ : Integrable (s₂ : Ω → E) μ := s₂.integrable_of_isFiniteMeasure
    filter_upwards [h₁, h₂, condExp_add hs₁ hs₂ (MeasurableSpace.invariants T)] with x hx₁ hx₂ hadd
    have hsum : Tendsto (fun n ↦ birkhoffAverage ℝ T s₁ n x + birkhoffAverage ℝ T s₂ n x) atTop
        (𝓝 (μ[s₁ | MeasurableSpace.invariants T] x + μ[s₂ | MeasurableSpace.invariants T] x)) :=
      hx₁.add hx₂
    rw [← Pi.add_apply, ← hadd] at hsum
    exact hsum.congr fun n ↦ (birkhoffAverage_add_apply ℝ n x).symm

private lemma ae_birkhoffAverage_sub_condExp_decomp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} (T : Ω → Ω) {f g : Ω → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, ∀ n : ℕ,
      birkhoffAverage ℝ T f n x - μ[f | MeasurableSpace.invariants T] x =
        birkhoffAverage ℝ T (f - g) n x +
          (birkhoffAverage ℝ T g n x - μ[g | MeasurableSpace.invariants T] x) -
          μ[f - g | MeasurableSpace.invariants T] x := by
  filter_upwards [condExp_sub hf hg (MeasurableSpace.invariants T)] with x hce_sub n
  rw [birkhoffAverage_sub_apply, hce_sub, Pi.sub_apply]
  abel

private lemma ae_mem_union_of_lt_limsup_norm_birkhoffAverage_sub_condExp {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → E} (hf : Integrable f μ) (s : SimpleFunc Ω E) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x ∂μ,
      (δ : EReal) <
        limsup (fun n ↦
          ((‖birkhoffAverage ℝ T f n x - μ[f | MeasurableSpace.invariants T] x‖ : ℝ) : EReal))
          atTop →
      ((δ / 3 : ℝ) : EReal) < birkhoffAverageSup T (fun y ↦ ‖(f - ⇑s) y‖) x ∨
        δ / 3 ≤ ‖μ[f - ⇑s | MeasurableSpace.invariants T] x‖ := by
  have hs_int : Integrable (s : Ω → E) μ := s.integrable_of_isFiniteMeasure
  filter_upwards [ae_tendsto_birkhoffAverage_condExp_simpleFunc hT s,
    ae_birkhoffAverage_sub_condExp_decomp T hf hs_int] with x hs_lim hdecomp hxD
  have hfreq : ∃ᶠ n in atTop,
      (δ : EReal) <
        ((‖birkhoffAverage ℝ T f n x - μ[f | MeasurableSpace.invariants T] x‖ : ℝ) : EReal) :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hxD
  have hs_small : ∀ᶠ n in atTop,
      ‖birkhoffAverage ℝ T s n x - μ[s | MeasurableSpace.invariants T] x‖ < δ / 3 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hs_lim).eventually (gt_mem_nhds (by linarith))
  obtain ⟨n, hδn, hsn⟩ := (hfreq.and_eventually hs_small).exists
  have hδn' : δ < ‖birkhoffAverage ℝ T f n x - μ[f | MeasurableSpace.invariants T] x‖ :=
    EReal.coe_lt_coe_iff.mp hδn
  have htri : ‖birkhoffAverage ℝ T f n x - μ[f | MeasurableSpace.invariants T] x‖ ≤
      birkhoffAverage ℝ T (fun y ↦ ‖(f - ⇑s) y‖) n x +
        ‖birkhoffAverage ℝ T s n x - μ[s | MeasurableSpace.invariants T] x‖ +
        ‖μ[f - ⇑s | MeasurableSpace.invariants T] x‖ := by
    rw [hdecomp n]
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact (norm_add_le _ _).trans
      (add_le_add (TauCeti.norm_birkhoffAverage_le_birkhoffAverage_norm T (f - ⇑s) n x) le_rfl)
  by_cases hB : δ / 3 ≤ ‖μ[f - ⇑s | MeasurableSpace.invariants T] x‖
  · exact Or.inr hB
  · left
    have hAn : δ / 3 < birkhoffAverage ℝ T (fun y ↦ ‖(f - ⇑s) y‖) n x := by linarith
    exact (EReal.coe_lt_coe_iff.mpr hAn).trans_le
      (le_iSup (fun k ↦ ((birkhoffAverage ℝ T (fun y ↦ ‖(f - ⇑s) y‖) k x : ℝ) : EReal)) n)

private lemma measure_lt_limsup_norm_birkhoffAverage_sub_condExp_eq_zero {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → E} (hf : Integrable f μ) {δ : ℝ} (hδ : 0 < δ) :
    μ {x | (δ : EReal) <
      limsup (fun n ↦
        ((‖birkhoffAverage ℝ T f n x - μ[f | MeasurableSpace.invariants T] x‖ : ℝ) : EReal))
        atTop} = 0 := by
  set D := {x | (δ : EReal) <
    limsup (fun n ↦
      ((‖birkhoffAverage ℝ T f n x - μ[f | MeasurableSpace.invariants T] x‖ : ℝ) : EReal))
      atTop}
  refine (measureReal_eq_zero_iff (measure_ne_top μ D)).mp (le_antisymm ?_ measureReal_nonneg)
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  have hη_pos : 0 < ε * δ / 6 := by positivity
  obtain ⟨s, hs_dist, _⟩ := (memLp_one_iff_integrable.mpr hf).exists_simpleFunc_eLpNorm_sub_lt
    ENNReal.one_ne_top (ENNReal.ofReal_ne_zero_iff.mpr hη_pos)
  have hdiff_int : Integrable (f - ⇑s) μ := hf.sub s.integrable_of_isFiniteMeasure
  have hdiff_norm : ∫ y, ‖(f - ⇑s) y‖ ∂μ < ε * δ / 6 :=
    integral_norm_lt_of_eLpNorm_one_lt_ofReal hs_dist
  set A := {x | ((δ / 3 : ℝ) : EReal) < birkhoffAverageSup T (fun y ↦ ‖(f - ⇑s) y‖) x}
  set B := {x | δ / 3 ≤ ‖μ[f - ⇑s | MeasurableSpace.invariants T] x‖}
  have hδ3 : 0 < δ / 3 := by positivity
  have hμA : μ.real A ≤ (3 / δ) * ∫ y, ‖(f - ⇑s) y‖ ∂μ := by
    have hmax := mul_measureReal_lt_birkhoffAverageSup_le_norm μ hT hdiff_int (δ / 3)
    exact ((le_div_iff₀' hδ3).mpr hmax).trans_eq (by ring)
  have hμB : μ.real B ≤ (3 / δ) * ∫ y, ‖(f - ⇑s) y‖ ∂μ := by
    have hmarkov : (δ / 3) * μ.real B ≤ ∫ y, ‖μ[f - ⇑s | MeasurableSpace.invariants T] y‖ ∂μ :=
      mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
        integrable_condExp.norm (δ / 3)
    exact ((le_div_iff₀' hδ3).mpr (hmarkov.trans (integral_norm_condExp_le (f - ⇑s)))).trans_eq
      (by ring)
  calc
    μ.real D ≤ μ.real (A ∪ B) := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top μ _)
        (measure_mono_ae (ae_mem_union_of_lt_limsup_norm_birkhoffAverage_sub_condExp hT hf s hδ))
    _ ≤ μ.real A + μ.real B := measureReal_union_le A B
    _ ≤ (3 / δ) * (∫ y, ‖(f - ⇑s) y‖ ∂μ) + (3 / δ) * (∫ y, ‖(f - ⇑s) y‖ ∂μ) :=
        add_le_add hμA hμB
    _ = (6 / δ) * ∫ y, ‖(f - ⇑s) y‖ ∂μ := by ring
    _ ≤ (6 / δ) * (ε * δ / 6) := by gcongr
    _ = ε := by field_simp [hδ.ne']

private lemma tendsto_eLpNorm_birkhoffAverage_sub_condExp_simpleFunc {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {p : ℝ≥0∞} (hp : p ≠ ∞) (s : SimpleFunc Ω E) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ T s n - μ[s | MeasurableSpace.invariants T]) p μ)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := s.exists_forall_norm_le
  have hce_bdd : ∀ᵐ x ∂μ, ‖μ[s | MeasurableSpace.invariants T] x‖ₑ ≤ ENNReal.ofReal C :=
    (ae_bdd_norm_condExp_of_ae_bdd_norm (ae_of_all _ hC)).mono fun _ hx ↦ by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (m := μ) (l := atTop) hp
    (Eventually.of_forall fun _ ↦
      aestronglyMeasurable_birkhoffAverage hT.quasiMeasurePreserving s.aestronglyMeasurable)
    (bound := fun _ ↦ (1 : ℝ)) (memLp_const 1) (C := Real.toNNReal C + Real.toNNReal C)
    (Eventually.of_forall fun n ↦ ?_) (ae_tendsto_birkhoffAverage_condExp_simpleFunc hT s)
  filter_upwards [hce_bdd] with x hx
  have havg : ‖birkhoffAverage ℝ T s n x‖ₑ ≤ ENNReal.ofReal C := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (TauCeti.norm_birkhoffAverage_le_of_forall_norm_le hC n x)
  simpa [ENNReal.ofReal] using eNorm_sub_le.trans (add_le_add havg hx)

end BanachBirkhoffHelpers

section PointwiseAndLpErgodic

namespace MeasureTheory.MeasurePreserving

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}

/-- **Birkhoff's pointwise ergodic theorem.** For a measure-preserving endomorphism `T` of a finite
measure space `(Ω, μ)` and an integrable observable `f` valued in a real Banach space, the Birkhoff
time averages `birkhoffAverage ℝ T f n` converge almost everywhere to the conditional expectation
`μ[f | MeasurableSpace.invariants T]`. -/
theorem ae_tendsto_birkhoffAverage_condExp (hT : MeasurePreserving T μ μ)
    {f : Ω → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop
      (𝓝 (μ[f | MeasurableSpace.invariants T] x)) := by
  let err : ℕ → Ω → ℝ :=
    fun n x ↦ ‖birkhoffAverage ℝ T f n x - μ[f | MeasurableSpace.invariants T] x‖
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ,
      limsup (fun n ↦ (err n x : EReal)) atTop ≤
        (((((k + 1 : ℕ) : ℝ)⁻¹ : ℝ)) : EReal) := by
    rw [ae_all_iff]
    intro k
    rw [ae_iff]
    simpa only [not_le] using measure_lt_limsup_norm_birkhoffAverage_sub_condExp_eq_zero hT hf
      (δ := ((k + 1 : ℕ) : ℝ)⁻¹) (by positivity)
  filter_upwards [hall] with x hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hlt : limsup (fun n ↦ (err n x : EReal)) atTop < (ε : EReal) :=
    (hx k).trans_lt (EReal.coe_lt_coe_iff.mpr (by simpa [one_div] using hk))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hlt)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact EReal.coe_lt_coe_iff.mp (hN n hn)

/-- **`Lᵖ` ergodic theorem (`1 ≤ p < ∞`).** For a measure-preserving endomorphism `T` of a finite
measure space `(Ω, μ)` and an `Lᵖ` observable `f` valued in a real Banach space, the Birkhoff time
averages `birkhoffAverage ℝ T f n` converge in `Lᵖ` to `μ[f | MeasurableSpace.invariants T]`. -/
theorem tendsto_eLpNorm_birkhoffAverage_sub_condExp (hT : MeasurePreserving T μ μ)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : Ω → E} (hf : MemLp f p μ) :
    Tendsto
      (fun n ↦ eLpNorm (birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]) p μ)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨s, hs_dist, _⟩ := hf.exists_simpleFunc_eLpNorm_sub_lt hp hε3.ne'
  have hs_lim := tendsto_eLpNorm_birkhoffAverage_sub_condExp_simpleFunc hT hp s
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs_lim.eventually (gt_mem_nhds hε3))
  refine ⟨N, fun n hn ↦ ?_⟩
  calc
    eLpNorm (birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]) p μ
      = eLpNorm (birkhoffAverage ℝ T (f - ⇑s) n +
          (birkhoffAverage ℝ T s n - μ[s | MeasurableSpace.invariants T]) -
          μ[f - ⇑s | MeasurableSpace.invariants T]) p μ :=
        eLpNorm_congr_ae
          ((ae_birkhoffAverage_sub_condExp_decomp T (hf.integrable hp1)
            s.integrable_of_isFiniteMeasure).mono fun _ h ↦ h n)
    _ ≤ eLpNorm (birkhoffAverage ℝ T (f - ⇑s) n) p μ +
          eLpNorm (birkhoffAverage ℝ T s n - μ[s | MeasurableSpace.invariants T]) p μ +
          eLpNorm (μ[f - ⇑s | MeasurableSpace.invariants T]) p μ :=
        (eLpNorm_sub_le hp1).trans (add_le_add (eLpNorm_add_le hp1) le_rfl)
    _ ≤ eLpNorm (f - ⇑s) p μ +
          eLpNorm (birkhoffAverage ℝ T s n - μ[s | MeasurableSpace.invariants T]) p μ +
          eLpNorm (f - ⇑s) p μ := by
          gcongr
          · exact hT.eLpNorm_birkhoffAverage_le hp1 (f - ⇑s) n
          · exact eLpNorm_condExp_le_eLpNorm (f - ⇑s) hp1
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr; exact (hN n hn).le
    _ = ε := by
        rw [← ENNReal.add_div, ← ENNReal.add_div]
        have h3 : ε + ε + ε = ε * 3 := by ring
        rw [h3, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

/-- **`L¹` ergodic theorem.** For a measure-preserving endomorphism `T` of a finite measure space
`(Ω, μ)` and an integrable Banach-valued observable `f`, the mean norm deviation between
`birkhoffAverage ℝ T f n` and `μ[f | MeasurableSpace.invariants T]` converges to `0`. -/
theorem tendsto_integral_norm_birkhoffAverage_sub_condExp (hT : MeasurePreserving T μ μ)
    {f : Ω → E} (hf : Integrable f μ) :
    Tendsto
      (fun n ↦ ∫ x, ‖birkhoffAverage ℝ T f n x - μ[f | MeasurableSpace.invariants T] x‖ ∂μ)
      atTop (𝓝 0) :=
  TauCeti.MeasureTheory.tendsto_integral_norm_of_tendsto_eLpNorm le_rfl
    (hT.tendsto_eLpNorm_birkhoffAverage_sub_condExp le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hf))

end MeasureTheory.MeasurePreserving

end PointwiseAndLpErgodic

section ErgodicSpecializations

namespace Ergodic

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure Ω} {T : Ω → Ω}

/-- **Birkhoff's pointwise ergodic theorem (ergodic case, finite measure).** For an ergodic map `T`
on a finite measure space `(Ω, μ)` and an integrable Banach-valued observable `f`, the Birkhoff
time averages converge almost everywhere to the space average `⨍ y, f y ∂μ`. -/
theorem ae_tendsto_birkhoffAverage_average [IsFiniteMeasure μ] (hT : Ergodic T μ)
    {f : Ω → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x) atTop (𝓝 (⨍ y, f y ∂μ)) := by
  filter_upwards [hT.toMeasurePreserving.ae_tendsto_birkhoffAverage_condExp hf,
    hT.toPreErgodic.condExp_invariants_ae_eq_average f] with x hx hce
  rwa [hce] at hx

/-- **`Lᵖ` ergodic theorem (ergodic case, finite measure, `1 ≤ p < ∞`).** For an ergodic map `T`
on a finite measure space `(Ω, μ)`, the Birkhoff time averages of an `Lᵖ` Banach-valued observable
converge in `Lᵖ` to the constant space average `⨍ y, f y ∂μ`. -/
theorem tendsto_eLpNorm_birkhoffAverage_sub_average [IsFiniteMeasure μ] (hT : Ergodic T μ)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : Ω → E} (hf : MemLp f p μ) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ T f n - fun _ ↦ ⨍ y, f y ∂μ) p μ)
      atTop (𝓝 0) := by
  refine (hT.toMeasurePreserving.tendsto_eLpNorm_birkhoffAverage_sub_condExp hp1 hp hf).congr
    fun n ↦ eLpNorm_congr_ae ?_
  filter_upwards [hT.toPreErgodic.condExp_invariants_ae_eq_average f] with x hx
  simp only [Pi.sub_apply, hx]

/-- **`L¹` ergodic theorem (ergodic case, finite measure).** For an ergodic map `T` on a finite
measure space `(Ω, μ)` and an integrable Banach-valued observable `f`, the mean norm deviation of
`birkhoffAverage ℝ T f n` from the space average `⨍ y, f y ∂μ` converges to `0`. -/
theorem tendsto_integral_norm_birkhoffAverage_sub_average [IsFiniteMeasure μ] (hT : Ergodic T μ)
    {f : Ω → E} (hf : Integrable f μ) :
    Tendsto (fun n ↦ ∫ x, ‖birkhoffAverage ℝ T f n x - ⨍ y, f y ∂μ‖ ∂μ) atTop (𝓝 0) :=
  TauCeti.MeasureTheory.tendsto_integral_norm_of_tendsto_eLpNorm le_rfl
    (hT.tendsto_eLpNorm_birkhoffAverage_sub_average le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hf))

/-- **Ergodic visiting frequencies (finite measure).** For an ergodic map `T` on a finite measure
space `(Ω, μ)` and a null-measurable set `s`, the fraction of the first `n` orbit points landing in
`s` converges almost everywhere to `μ.real s / μ.real Set.univ`. -/
theorem ae_tendsto_card_filter_iterate_mem_div [IsFiniteMeasure μ] (hT : Ergodic T μ)
    {s : Set Ω} [DecidablePred (· ∈ s)] (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ ↦ (((Finset.range n).filter (fun k ↦ T^[k] x ∈ s)).card : ℝ) / (n : ℝ))
      atTop (𝓝 (μ.real s / μ.real Set.univ)) := by
  have hind : Integrable (s.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator₀ hs
  have havg : (⨍ y, s.indicator (fun _ ↦ (1 : ℝ)) y ∂μ) = μ.real s / μ.real Set.univ := by
    rw [average_eq, integral_indicator₀ hs, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one,
      div_eq_inv_mul]
  filter_upwards [hT.ae_tendsto_birkhoffAverage_average hind] with x hx
  rw [havg] at hx
  refine hx.congr fun n ↦ ?_
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, Set.indicator,
    Finset.sum_boole, div_eq_inv_mul]

end Ergodic

end ErgodicSpecializations
