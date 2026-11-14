/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Stopping
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
public import Mathlib.Probability.Process.LocalProperty
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Patching

/-!
# The continuous-time Brownian Itô integral

For a filtration-relative Brownian motion `W` with almost surely continuous paths and a locally
square-integrable predictable integrand `H` (`TauCeti.LocallyBrownianIntegrable ℱ P H`), this file
defines the elementary-approximation specification `TauCeti.Probability.IsItoIntegral` and proves
existence, uniqueness up to indistinguishability, local-martingale regularity, optional stopping,
and local pathwise congruence on the original raw filtration.

`IsItoIntegral ℱ P W H I` asserts that `H` is strongly predictable, `I` has almost surely
continuous paths, and at every horizon `t` there is a sequence of finite-grid elementary holdings
converging to `H` in probability in pathwise square energy on `(0, t]` whose Brownian simple gains
converge to `I t` in probability. Uniqueness up to indistinguishability (`isItoIntegral_unique`)
combines common-grid refinement of signed elementary differences with the energy-to-probability
bound `IsFilteredPreBrownianReal.tendstoInMeasure_sum_mul_sub_of_energy` and path continuity.

Existence (`exists_isItoIntegral`) localizes `H` by closed-level hits of its repaired energy clock
(`TauCeti.nnvolume.energyLocalizer`), constructs continuous martingale stages via
`exists_continuous_l2Integral`, verifies stage compatibility via `stoppedProcess_ae_eq_l2Integral`,
patches the stages without enlarging the filtration, and upgrades the patched local martingale to
an indistinguishable strongly predictable version. Stopping an Itô integral at any raw stopping
time `σ` represents `H` cut off to `⟦0, σ⟧` (`itoIntegral_stoppedProcess`), yielding local
congruence on stochastic intervals (`itoIntegral_local_congr`) and recovering the global `L²`
isometry and martingale properties when `H` is `BrownianIntegrable`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti.LocallyBrownianIntegrable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H K : ℝ≥0 → Ω → ℝ}

/-- The zero process belongs to the pathwise square-energy integrand domain. -/
theorem zero : LocallyBrownianIntegrable ℱ P (0 : ℝ≥0 → Ω → ℝ) :=
  ⟨stronglyMeasurable_const, .of_forall fun _ _ ↦ .zero⟩

/-- Negation preserves finite pathwise square energy. -/
theorem neg (h : LocallyBrownianIntegrable ℱ P H) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ -H t ω) := by
  simpa only [neg_one_mul] using h.const_mul (-1)

/-- Subtraction preserves finite pathwise square energy. -/
theorem sub (hH : LocallyBrownianIntegrable ℱ P H) (hK : LocallyBrownianIntegrable ℱ P K) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ H t ω - K t ω) := by
  simpa only [sub_eq_add_neg] using hH.add hK.neg

/-- Stopping a locally square-integrable predictable integrand at a raw stopping time preserves
`LocallyBrownianIntegrable`. -/
theorem ite_le (hH : LocallyBrownianIntegrable ℱ P H) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) :
    LocallyBrownianIntegrable ℱ P (fun t : ℝ≥0 ↦ fun ω ↦
      if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  refine ⟨hH.isStronglyPredictable.ite_le hτ, hH.ae_memLp.mono fun ω hω T ↦ ?_⟩
  have hS : MeasurableSet {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ τ ω} := by
    cases τ ω with
    | top =>
      rw [show {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ ⊤} = univ by
        ext; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact le_top]
      exact MeasurableSet.univ
    | coe s =>
      rw [show {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)} = Iic s by
        ext; simp only [mem_ofPred_eq, mem_Iic]; exact WithTop.coe_le_coe]
      exact measurableSet_Iic
  have hfun : (fun t : ℝ≥0 ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) =
      {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ τ ω}.indicator (fun t ↦ H t ω) := by
    ext t; simp only [indicator_apply, mem_ofPred_eq]
  rw [hfun]
  exact (hω T).indicator hS.nullMeasurableSet

end TauCeti.LocallyBrownianIntegrable

namespace TauCeti.Probability

section Spec

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ}

/-- Elementary-approximation specification of the continuous-time Brownian Itô integral on a raw
filtration: `H` is strongly predictable, `I` has almost surely continuous sample paths, and at
every observation time `t` there is a sequence of finite-grid elementary holdings converging to `H`
in probability in pathwise square energy on `(0, t]` whose Brownian simple gains converge to `I t`
in probability. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W H I : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is strongly predictable for the declared filtration. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- Almost every path of the integral process is continuous. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)
  /-- At each horizon `t`, finite-grid elementary holdings approximate `H` in pathwise square
  energy in probability while their Brownian gains converge to `I t` in probability. -/
  exists_seq_approx : ∀ t : ℝ≥0, ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
    (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
    (∀ k i, i < n k → StronglyMeasurable[ℱ (τ k i)] (a k i)) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω |
      ε ≤ ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure t}) atTop (𝓝 0)) ∧
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t)

/-- The zero process is an Itô integral of the zero integrand. -/
theorem IsItoIntegral.zero : IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := .of_forall fun _ ↦ continuous_const
  exists_seq_approx t := ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ ↦ 0,
    fun _ _ _ _ _ _ ↦ le_rfl, fun _ _ h ↦ (Nat.not_lt_zero _ h).elim,
    fun ε hε ↦ by
      have hempty : {ω : Ω | ε ≤ ∫⁻ s,
          ‖Finance.simpleHolding (fun _ ↦ 0) 0 (fun _ _ ↦ 0) s ω - (0 : ℝ≥0 → Ω → ℝ) s ω‖ₑ ^ 2
            ∂timeMeasure t} = ∅ := by
        ext ω; simp [Finance.simpleHolding_def, not_le.mpr hε]
      exact tendsto_const_nhds.congr fun _ ↦ by rw [hempty, measure_empty],
    by
      have hfg : (fun _ : ℕ ↦ Finance.simpleGains (fun _ ↦ 0) 0 (fun _ _ ↦ 0) W t) =
          fun _ ↦ (0 : Ω → ℝ) := by
        ext _ _; simp [Finance.simpleGains_def]
      rw [hfg]
      exact fun ε hε ↦ by simp [not_le.mpr hε]⟩

/-- Indistinguishable replacements preserve `IsItoIntegral`. -/
theorem IsItoIntegral.of_indist (hI : IsItoIntegral ℱ P W H I) (hIJ : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P W H J where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hIJ] with ω hc heq
    simpa only [funext heq] using hc
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hen, hg⟩ := hI.exists_seq_approx t
    exact ⟨n, τ, a, hτ, ha, hen, hg.congr_right (hIJ.mono fun _ hω ↦ hω t)⟩

/-- Product-almost-everywhere replacement of a predictable integrand on every finite horizon
preserves `IsItoIntegral`. -/
theorem IsItoIntegral.congr_integrand [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure t).prod P] Function.uncurry K) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hen, hg⟩ := hI.exists_seq_approx t
    have heq_set : MeasurableSet {p : ℝ≥0 × Ω | H p.1 p.2 = K p.1 p.2} :=
      measurableSet_eq_fun (hI.isStronglyPredictable.mono ℱ.predictable_le_prod).measurable
        (hK.mono ℱ.predictable_le_prod).measurable
    have hae_ω : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[timeMeasure t] (fun s ↦ K s ω) :=
      (Measure.ae_ae_comm heq_set).mp (Measure.ae_ae_of_ae_prod (hHK t))
    refine ⟨n, τ, a, hτ, ha, fun ε hε ↦ (hen ε hε).congr' (.of_forall fun k ↦ ?_), hg⟩
    refine measure_congr (hae_ω.mono fun ω hω ↦ ?_)
    have hlin : (∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure t) =
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - K s ω‖ₑ ^ 2 ∂timeMeasure t :=
      lintegral_congr_ae (hω.mono fun s hs ↦ by dsimp only at hs ⊢; rw [hs])
    dsimp only [mem_ofPred_eq]
    rw [hlin]

end Spec

namespace IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W H K I J : ℝ≥0 → Ω → ℝ}

private def clipTau (t : ℝ≥0) (τ : ℕ → ℝ≥0) (i : ℕ) : ℝ≥0 := min (τ i) t

private def clipHeight (t : ℝ≥0) (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (i : ℕ) : Ω → ℝ :=
  if τ i ≤ t then a i else 0

private theorem simpleHolding_clipTau_eq_of_le {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    {s t : ℝ≥0} (hs : s ≤ t) (ω : Ω) :
    Finance.simpleHolding (clipTau t τ) n (clipHeight t τ a) s ω =
      Finance.simpleHolding τ n a s ω := by
  simp only [Finance.simpleHolding_def]
  refine sum_congr rfl fun i _ ↦ ?_
  by_cases h : τ i ≤ t
  · rw [clipTau, clipTau, min_eq_left h, clipHeight, ite_eq_left h]
    have hmem : s ∈ Ioc (τ i) (min (τ (i + 1)) t) ↔ s ∈ Ioc (τ i) (τ (i + 1)) :=
      ⟨fun hs' ↦ ⟨hs'.1, hs'.2.trans (min_le_left _ _)⟩, fun hs' ↦ ⟨hs'.1, le_min hs'.2 hs⟩⟩
    by_cases hs' : s ∈ Ioc (τ i) (τ (i + 1))
    · rw [indicator_of_mem (hmem.mpr hs'), indicator_of_mem hs']
    · rw [indicator_of_notMem (mt hmem.mp hs'), indicator_of_notMem hs']
  · rw [clipHeight, ite_eq_right h,
      indicator_of_notMem fun (hs' : s ∈ Ioc (τ i) (τ (i + 1))) ↦ h (hs'.1.le.trans hs)]
    simp

private theorem clipStrategy_spec {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) (t : ℝ≥0) :
    MonotoneOn (clipTau t τ) (Iic n) ∧
      (∀ i < n, StronglyMeasurable[ℱ (clipTau t τ i)] (clipHeight t τ a i)) ∧
      (∀ ω, (∑ i ∈ range n, clipHeight t τ a i ω *
          (W (clipTau t τ (i + 1)) ω - W (clipTau t τ i) ω)) =
        Finance.simpleGains τ n a W t ω) ∧
      ∀ ω, ENNReal.ofReal (elementaryEnergy (clipTau t τ) (clipHeight t τ a) n ω) =
        ∫⁻ s, ‖Finance.simpleHolding τ n a s ω‖ₑ ^ 2 ∂timeMeasure t := by
  have hm : MonotoneOn (clipTau t τ) (Iic n) :=
    fun i hi j hj hij ↦ min_le_min_right t (hτ hi hj hij)
  refine ⟨hm, fun i hi ↦ ?_, fun ω ↦ ?_, fun ω ↦ ?_⟩
  · by_cases h : τ i ≤ t
    · rw [show clipTau t τ i = τ i from min_eq_left h, show clipHeight t τ a i = a i from
        ite_eq_left h]
      exact ha i hi
    · rw [show clipHeight t τ a i = fun _ ↦ 0 from ite_eq_right h]
      exact stronglyMeasurable_const
  · rw [Finance.simpleGains_def]
    refine sum_congr rfl fun i hi ↦ ?_
    by_cases h : τ i ≤ t
    · simp [clipTau, clipHeight, h]
    · have hti : t ≤ τ i := (not_le.mp h).le
      have ht1 : t ≤ τ (i + 1) :=
        hti.trans (hτ (mem_Iic.mpr (mem_range.mp hi).le) (mem_Iic.mpr (mem_range.mp hi)) i.le_succ)
      simp [clipHeight, h, min_eq_right hti, min_eq_right ht1]
  · have hcongr : (∫⁻ s, ‖Finance.simpleHolding τ n a s ω‖ₑ ^ 2 ∂timeMeasure t) =
        ∫⁻ s, ‖Finance.simpleHolding (clipTau t τ) n (clipHeight t τ a) s ω‖ₑ ^ 2
          ∂timeMeasure t := by
      rw [timeMeasure_def]
      exact setLIntegral_congr_fun measurableSet_Ioc fun s hs ↦ by
        rw [simpleHolding_clipTau_eq_of_le hs.2 ω]
    rw [hcongr, Finance.lintegral_enorm_sq_simpleHolding_timeMeasure hm t ω,
      elementaryEnergy_def, ENNReal.ofReal_sum_of_nonneg fun j hj ↦ mul_nonneg (sq_nonneg _)
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
          (hm (mem_Iic.mpr (mem_range.mp hj).le) (mem_Iic.mpr (mem_range.mp hj)) j.le_succ)))]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [show min (clipTau t τ (j + 1)) t = clipTau t τ j.succ from min_eq_left (min_le_right _ _),
      ENNReal.ofReal_mul (sq_nonneg _), Real.eNorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

private theorem exists_diff_clipped_strategy
    {n₁ n₂ : ℕ} {τ₁ τ₂ : ℕ → ℝ≥0} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Iic n₁)) (ha₁ : ∀ i < n₁, StronglyMeasurable[ℱ (τ₁ i)] (a₁ i))
    (hτ₂ : MonotoneOn τ₂ (Iic n₂)) (ha₂ : ∀ i < n₂, StronglyMeasurable[ℱ (τ₂ i)] (a₂ i))
    (t : ℝ≥0) :
    ∃ (M : ℕ) (g : ℕ → ℝ≥0) (d : ℕ → Ω → ℝ),
      MonotoneOn g (Iic M) ∧
      (∀ j < M, StronglyMeasurable[ℱ (g j)] (d j)) ∧
      (∀ ω, (∑ j ∈ range M, d j ω * (W (g (j + 1)) ω - W (g j) ω)) =
        Finance.simpleGains τ₁ n₁ a₁ W t ω - Finance.simpleGains τ₂ n₂ a₂ W t ω) ∧
      ∀ ω, ENNReal.ofReal (elementaryEnergy g d M ω) =
        ∫⁻ s, ‖Finance.simpleHolding τ₁ n₁ a₁ s ω - Finance.simpleHolding τ₂ n₂ a₂ s ω‖ₑ ^ 2
          ∂timeMeasure t := by
  let l : Fin n₁ ⊕ Fin n₂ → ℝ≥0 := Sum.elim (fun i ↦ τ₁ i) (fun j ↦ τ₂ j)
  let u : Fin n₁ ⊕ Fin n₂ → ℝ≥0 := Sum.elim (fun i ↦ τ₁ (i + 1)) (fun j ↦ τ₂ (j + 1))
  let c : Fin n₁ ⊕ Fin n₂ → Ω → ℝ := Sum.elim (fun i ↦ a₁ i) (fun j ↦ -a₂ j)
  have hc : ∀ x ∈ (Finset.univ : Finset (Fin n₁ ⊕ Fin n₂)), StronglyMeasurable[ℱ (l x)] (c x) := by
    rintro (i | j) _
    · exact ha₁ i i.isLt
    · exact (ha₂ j j.isLt).neg
  obtain ⟨M, σ, b, _, hσ, hb, _, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ Finset.univ l u c hc
  obtain ⟨hm, hd, hsum, hen⟩ := clipStrategy_spec (W := W) hσ.monotoneOn hb t
  refine ⟨M, clipTau t σ, clipHeight t σ b, hm, hd, fun ω ↦ ?_, fun ω ↦ ?_⟩
  · rw [hsum ω, hgain W t ω, Fintype.sum_sum_type]
    have hsum₁ : (∑ i : Fin n₁, if l (.inl i) ≤ u (.inl i) then
          c (.inl i) ω * (W (min (u (.inl i)) t) ω - W (min (l (.inl i)) t) ω) else 0) =
        ∑ i ∈ range n₁, a₁ i ω * (W (min (τ₁ (i + 1)) t) ω - W (min (τ₁ i) t) ω) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun i _ ↦ ?_
      have h1 : l (.inl i) ≤ u (.inl i) :=
        hτ₁ (mem_Iic.mpr i.isLt.le) (mem_Iic.mpr i.isLt) i.val.le_succ
      exact ite_eq_left h1
    have hsum₂ : (∑ j : Fin n₂, if l (.inr j) ≤ u (.inr j) then
          c (.inr j) ω * (W (min (u (.inr j)) t) ω - W (min (l (.inr j)) t) ω) else 0) =
        -(∑ j ∈ range n₂, a₂ j ω * (W (min (τ₂ (j + 1)) t) ω - W (min (τ₂ j) t) ω)) := by
      rw [← sum_neg_distrib, ← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun j _ ↦ ?_
      have h2 : l (.inr j) ≤ u (.inr j) :=
        hτ₂ (mem_Iic.mpr j.isLt.le) (mem_Iic.mpr j.isLt) j.val.le_succ
      rw [ite_eq_left h2]
      dsimp only [l, u, c, Sum.elim_inr, Pi.neg_apply]
      ring
    rw [hsum₁, hsum₂, Finance.simpleGains_def, Finance.simpleGains_def, sub_eq_add_neg]
  · rw [hen ω]
    refine lintegral_congr fun s ↦ ?_
    rw [hhold s ω, Fintype.sum_sum_type]
    dsimp only [l, u, c, Sum.elim_inl, Sum.elim_inr]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ (Ioc (τ₁ i) (τ₁ (i + 1))).indicator (fun _ ↦ a₁ i ω) s),
      Fin.sum_univ_eq_sum_range (fun j ↦ (Ioc (τ₂ j) (τ₂ (j + 1))).indicator (fun _ ↦ (-a₂ j) ω) s)]
    have hneg (j : ℕ) : (Ioc (τ₂ j) (τ₂ (j + 1))).indicator (fun _ ↦ -a₂ j ω) s =
        -(Ioc (τ₂ j) (τ₂ (j + 1))).indicator (fun _ ↦ a₂ j ω) s := by
      by_cases hs : s ∈ Ioc (τ₂ j) (τ₂ (j + 1)) <;> simp [hs]
    simp only [Pi.neg_apply, hneg, sum_neg_distrib, Finance.simpleHolding_def, ← sub_eq_add_neg]

private theorem eNorm_sub_sq_le (x y z : ℝ) :
    ‖x - y‖ₑ ^ 2 ≤ 2 * ‖x - z‖ₑ ^ 2 + 2 * ‖y - z‖ₑ ^ 2 := by
  have hreal : (x - y) ^ 2 ≤ 2 * (x - z) ^ 2 + 2 * (y - z) ^ 2 := by
    nlinarith [sq_nonneg ((x - z) + (y - z))]
  have hsq (r : ℝ) : ‖r‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
    rw [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg r), sq_abs]
  rw [hsq, hsq, hsq, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two,
    ← ENNReal.ofReal_mul zero_le_two, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem tendstoInMeasure_elementaryEnergy_of_approx
    (hH : IsStronglyPredictable ℱ H) (t : ℝ≥0)
    {n₁ n₂ M : ℕ → ℕ} {τ₁ τ₂ g : ℕ → ℕ → ℝ≥0} {a₁ a₂ d : ℕ → ℕ → Ω → ℝ}
    (ha₁ : ∀ k i, i < n₁ k → StronglyMeasurable[ℱ (τ₁ k i)] (a₁ k i))
    (hg : ∀ k, MonotoneOn (g k) (Iic (M k)))
    (hen_eq : ∀ k ω, ENNReal.ofReal (elementaryEnergy (g k) (d k) (M k) ω) =
      ∫⁻ s, ‖Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω -
        Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω‖ₑ ^ 2 ∂timeMeasure t)
    (hE₁ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω |
      ε ≤ ∫⁻ s, ‖Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure t}) atTop (𝓝 0))
    (hE₂ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω |
      ε ≤ ∫⁻ s, ‖Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure t}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ↦ elementaryEnergy (g k) (d k) (M k)) atTop (fun _ ↦ 0) := by
  refine tendstoInMeasure_iff_norm.mpr fun δ hδ ↦ ?_
  have hδ4 : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 4) := ENNReal.ofReal_pos.mpr (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using (hE₁ _ hδ4).add (hE₂ _ hδ4)) (fun _ ↦ bot_le) fun k ↦ ?_
  have hsub : {ω | δ ≤ ‖elementaryEnergy (g k) (d k) (M k) ω - 0‖} ⊆
      {ω | ENNReal.ofReal (δ / 4) ≤ ∫⁻ s,
        ‖Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t} ∪
      {ω | ENNReal.ofReal (δ / 4) ≤ ∫⁻ s,
        ‖Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t} := by
    intro ω hω
    have hnn := elementaryEnergy_nonneg (a := d k) (hg k) ω
    have hle_en : ENNReal.ofReal δ ≤ ENNReal.ofReal (elementaryEnergy (g k) (d k) (M k) ω) := by
      simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn] at hω
      exact ENNReal.ofReal_le_ofReal hω
    have hm₁ : Measurable (fun s : ℝ≥0 ↦
        2 * ‖Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H s ω‖ₑ ^ 2) := by
      have hs : StronglyMeasurable (fun s : ℝ≥0 ↦
          Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H s ω) :=
        (((Finance.isStronglyPredictable_simpleHolding (ha₁ k)).sub hH).mono
          ℱ.predictable_le_prod).comp_measurable (measurable_id.prodMk measurable_const)
      exact (hs.eNorm.pow_const 2).const_mul 2
    have htri : ENNReal.ofReal δ ≤
        2 * (∫⁻ s, ‖Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t) +
        2 * ∫⁻ s, ‖Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t := by
      rw [hen_eq k ω] at hle_en
      refine hle_en.trans ((lintegral_mono fun s ↦ eNorm_sub_sq_le _ _ (H s ω)).trans ?_)
      rw [lintegral_add_left hm₁, lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
        lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
    by_contra hnot
    obtain ⟨h1, h2⟩ := not_or.mp hnot
    simp only [mem_ofPred_eq, not_le] at h1 h2
    have hlt : 2 * (∫⁻ s, ‖Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure t) +
        2 * ∫⁻ s, ‖Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure t < ENNReal.ofReal δ := by
      calc
        _ < 2 * ENNReal.ofReal (δ / 4) + 2 * ENNReal.ofReal (δ / 4) :=
          ENNReal.add_lt_add
            (ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top h1)
            (ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top h2)
        _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
    exact hlt.not_ge htri
  exact (measure_mono hsub).trans (measure_union_le _ _)

private theorem ae_eq_of_tendstoInMeasure_sub_zero
    {G₁ G₂ : ℕ → Ω → ℝ} {f₁ f₂ : Ω → ℝ}
    (h₁ : TendstoInMeasure P G₁ atTop f₁)
    (h₂ : TendstoInMeasure P G₂ atTop f₂)
    (hsub : TendstoInMeasure P (fun k ω ↦ G₁ k ω - G₂ k ω) atTop (fun _ ↦ 0)) :
    f₁ =ᵐ[P] f₂ := by
  obtain ⟨ns₁, hns₁, hae₁⟩ := h₁.exists_seq_tendsto_ae
  obtain ⟨ns₂, hns₂, hae₂⟩ := (h₂.comp hns₁.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ns₃, hns₃, haed⟩ :=
    ((hsub.comp hns₁.tendsto_atTop).comp hns₂.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hae₁, hae₂, haed] with ω hc₁ hc₂ hcd
  have hlim : Tendsto (fun i ↦ G₁ (ns₁ (ns₂ (ns₃ i))) ω - G₂ (ns₁ (ns₂ (ns₃ i))) ω)
      atTop (𝓝 (f₁ ω - f₂ ω)) :=
    ((hc₁.comp hns₂.tendsto_atTop).comp hns₃.tendsto_atTop).sub (hc₂.comp hns₃.tendsto_atTop)
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim hcd)

/-- **Uniqueness of the Brownian Itô integral.** Any two processes satisfying `IsItoIntegral` for
the same predictable integrand `H` are indistinguishable on the original raw filtration. -/
theorem isItoIntegral_unique (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) :
    I ≡ᵐ[P] J := by
  refine Indistinguishable.of_ae_eq hI.ae_continuous hJ.ae_continuous fun t ↦ ?_
  obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hE₁, hG₁⟩ := hI.exists_seq_approx t
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hG₂⟩ := hJ.exists_seq_approx t
  have hdiff (k : ℕ) :=
    exists_diff_clipped_strategy (W := W) (hτ₁ k) (ha₁ k) (hτ₂ k) (ha₂ k) t
  choose M g d hg hd hsum hen using hdiff
  have hen_zero : TendstoInMeasure P (fun k ↦ elementaryEnergy (g k) (d k) (M k))
      atTop (fun _ ↦ 0) :=
    tendstoInMeasure_elementaryEnergy_of_approx hI.isStronglyPredictable t ha₁ hg hen hE₁ hE₂
  have hsum_zero := hW.tendstoInMeasure_sum_mul_sub_of_energy hg hd hen_zero
  have hgain_zero : TendstoInMeasure P
      (fun k ω ↦ Finance.simpleGains (τ₁ k) (n₁ k) (a₁ k) W t ω -
        Finance.simpleGains (τ₂ k) (n₂ k) (a₂ k) W t ω) atTop (fun _ ↦ 0) :=
    hsum_zero.congr_left fun k ↦ .of_forall (hsum k)
  exact ae_eq_of_tendstoInMeasure_sub_zero hG₁ hG₂ hgain_zero

private theorem tendsto_meas_ge_lintegral_eNorm_sq_of_eLpNorm [SFinite P]
    {g : ℕ → ℝ≥0 × Ω → ℝ} (hg : ∀ k, StronglyMeasurable (g k)) (t : ℝ≥0)
    (hlim : Tendsto (fun k ↦ eLpNorm (g k) 2 ((timeMeasure t).prod P)) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) := by
  have hsq : Tendsto (fun k ↦ eLpNorm (g k) 2 ((timeMeasure t).prod P) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow (by decide : 2 ≠ 0)] using
      ((ENNReal.continuous_pow 2).continuousAt.tendsto.comp hlim)
  by_cases htop : ε = ∞
  · subst htop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hsq.eventually (gt_mem_nhds zero_lt_one)] with k hk
    have hm : Measurable (fun p : ℝ≥0 × Ω ↦ ‖g k p‖ₑ ^ 2) := (hg k).eNorm.pow_const 2
    have hlt : ∫⁻ ω, ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t ∂P < ∞ := by
      rw [← lintegral_prod_symm (fun p ↦ ‖g k p‖ₑ ^ 2) hm.aemeasurable,
        TauCeti.lintegral_enorm_pow_eq_eLpNorm_pow (by decide) (hg k).aestronglyMeasurable]
      simpa only [Nat.cast_ofNat] using hk.trans ENNReal.one_lt_top
    have hae := ae_lt_top hm.lintegral_prod_left' hlt.ne
    simpa only [not_lt, top_le_iff] using (ae_iff.mp hae).symm
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [Function.comp_def, mul_zero] using
        ((ENNReal.continuous_const_mul
          (ENNReal.inv_ne_top.mpr hε.ne')).continuousAt.tendsto.comp hsq))
      (fun _ ↦ bot_le) fun k ↦ ?_
    have hm : Measurable (fun p : ℝ≥0 × Ω ↦ ‖g k p‖ₑ ^ 2) := (hg k).eNorm.pow_const 2
    have hmarkov : ε * P {ω | ε ≤ ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t} ≤
        eLpNorm (g k) 2 ((timeMeasure t).prod P) ^ 2 := by
      calc
        ε * P {ω | ε ≤ ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t}
          ≤ ∫⁻ ω, ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t ∂P :=
            mul_meas_ge_le_lintegral hm.lintegral_prod_left' ε
        _ = eLpNorm (g k) 2 ((timeMeasure t).prod P) ^ 2 := by
            rw [← lintegral_prod_symm (fun p ↦ ‖g k p‖ₑ ^ 2) hm.aemeasurable,
              TauCeti.lintegral_enorm_pow_eq_eLpNorm_pow (by decide) (hg k).aestronglyMeasurable]
            simp only [Nat.cast_ofNat]
    calc
      P {ω | ε ≤ ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t}
        = ε⁻¹ * (ε * P {ω | ε ≤ ∫⁻ s, ‖g k (s, ω)‖ₑ ^ 2 ∂timeMeasure t}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hε.ne' htop, one_mul]
      _ ≤ ε⁻¹ * eLpNorm (g k) 2 ((timeMeasure t).prod P) ^ 2 := mul_le_mul_right hmarkov _

/-- Any almost surely continuous modification of `t ↦ hW.l2Integral t (hH.toPredictableLp t)`
satisfies the elementary-approximation specification `IsItoIntegral`. -/
theorem isItoIntegral_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    IsItoIntegral ℱ P W H I where
  isStronglyPredictable := hH.isStronglyPredictable
  ae_continuous := hI_cont
  exists_seq_approx t := by
    let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
    have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
      MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
        (Eventually.of_forall (hb k j hj))
    refine ⟨n, τ, a, fun k ↦ (hτ k).monotoneOn, ha, fun ε hε ↦ ?_, ?_⟩
    · exact tendsto_meas_ge_lintegral_eNorm_sq_of_eLpNorm
        (fun k ↦ ((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
          hH.isStronglyPredictable).mono ℱ.predictable_le_prod) t (herr t) hε
    · refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
      have heq (k : ℕ) : eLpNorm (Finance.simpleGains (τ k) (n k) (a k) W t - I t) 2 P =
          eLpNorm (fun p ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 2
            ((timeMeasure t).prod P) :=
        (eLpNorm_congr_ae (EventuallyEq.rfl.sub (hI t))).trans
          (hW.eLpNorm_simpleGains_sub_l2Integral hH (hτ k).monotoneOn (ha k) (ha₂ k) t)
      simpa only [heq] using herr t

private theorem continuous_stoppedProcess {u : ℝ≥0 → Ω → ℝ} (τ : Ω → WithTop ℝ≥0) {ω : Ω}
    (hu : Continuous (fun t ↦ u t ω)) :
    Continuous (fun t ↦ stoppedProcess u τ t ω) := by
  cases hτ : τ ω with
  | top =>
    have heq (t : ℝ≥0) : stoppedProcess u τ t ω = u t ω :=
      stoppedProcess_eq_of_le (by rw [hτ]; exact le_top)
    simpa only [heq] using hu
  | coe s =>
    have heq (t : ℝ≥0) : stoppedProcess u τ t ω = u (min t s) ω := by
      rcases le_total t s with hts | hst
      · rw [stoppedProcess_eq_of_le (by rw [hτ]; exact WithTop.coe_le_coe.mpr hts), min_eq_left hts]
      · have hm : min (t : WithTop ℝ≥0) (s : WithTop ℝ≥0) = (s : WithTop ℝ≥0) :=
          min_eq_right (WithTop.coe_le_coe.mpr hst)
        dsimp only [stoppedProcess]
        rw [hτ, hm, min_eq_right hst]
        simp only [WithTop.untopA, WithTop.untopD_coe]
    simpa only [Function.comp_def, id_eq, heq] using hu.comp (continuous_id.min continuous_const)

private theorem tendsto_measure_le_of_isLocalizingSequence [IsFiniteMeasure P]
    {τ : ℕ → Ω → WithTop ℝ≥0} (hloc : IsLocalizingSequence ℱ τ P)
    (hmono : ∀ ω, Monotone (τ · ω)) (t : ℝ≥0) :
    Tendsto (fun k ↦ P {ω | τ k ω ≤ (t : WithTop ℝ≥0)}) atTop (𝓝 0) := by
  let A (k : ℕ) : Set Ω := {ω | τ k ω ≤ (t : WithTop ℝ≥0)}
  have hA_anti : Antitone A := fun i j hij ω hω ↦ (hmono ω hij).trans hω
  have hA_meas (k : ℕ) : NullMeasurableSet (A k) P :=
    (ℱ.le t _ ((hloc.isStoppingTime k) t)).nullMeasurableSet
  have hA_inter : P (⋂ k, A k) = 0 := by
    have hset : (⋂ k, A k) = {ω | ¬ ∃ k, (t : WithTop ℝ≥0) < τ k ω} := by
      ext ω; simp only [mem_iInter, A, mem_ofPred_eq, not_exists, not_lt]
    rw [hset, ← ae_iff]
    filter_upwards [hloc.tendsto_top] with ω hω
    exact (hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).exists
  simpa only [Function.comp_def, hA_inter] using
    tendsto_measure_iInter_atTop hA_meas hA_anti ⟨0, measure_ne_top P _⟩

private theorem tendsto_localized_energy_approx [IsFiniteMeasure P]
    {Hstage : ℕ → ℝ≥0 → Ω → ℝ} (hHstage_pred : ∀ k, IsStronglyPredictable ℱ (Hstage k))
    {τ : ℕ → Ω → WithTop ℝ≥0} (hloc : IsLocalizingSequence ℱ τ P)
    (hmono : ∀ ω, Monotone (τ · ω)) (t : ℝ≥0)
    {n : ℕ → ℕ} {grid : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (ha : ∀ k j, j < n k → StronglyMeasurable[ℱ (grid k j)] (a k j))
    (herr_lim : Tendsto (fun k ↦ eLpNorm
      (fun p ↦ Finance.simpleHolding (grid k) (n k) (a k) p.1 p.2 - Hstage k p.1 p.2) 2
        ((timeMeasure t).prod P)) atTop (𝓝 0))
    (hstage_eq : ∀ᵐ ω ∂P, ∀ k, (t : WithTop ℝ≥0) < τ k ω →
      EqOn (fun s ↦ Hstage k s ω) (fun s ↦ H s ω) (Iic t))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s,
      ‖Finance.simpleHolding (grid k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
      atTop (𝓝 0) := by
  have hstage_en := tendsto_meas_ge_lintegral_eNorm_sq_of_eLpNorm
    (fun k ↦ ((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
      (hHstage_pred k)).mono ℱ.predictable_le_prod) t herr_lim hε
  have htail := tendsto_measure_le_of_isLocalizingSequence hloc hmono t
  have hnull : P {ω | ¬ ∀ k, (t : WithTop ℝ≥0) < τ k ω →
      EqOn (fun s ↦ Hstage k s ω) (fun s ↦ H s ω) (Iic t)} = 0 := ae_iff.mp hstage_eq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hstage_en.add htail) (fun _ ↦ bot_le) fun k ↦ ?_
  have hinc : {ω | ε ≤ ∫⁻ s,
        ‖Finance.simpleHolding (grid k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t} ⊆
      {ω | ε ≤ ∫⁻ s,
        ‖Finance.simpleHolding (grid k) (n k) (a k) s ω - Hstage k s ω‖ₑ ^ 2 ∂timeMeasure t} ∪
      {ω | τ k ω ≤ (t : WithTop ℝ≥0)} ∪
      {ω | ¬ ∀ m, (t : WithTop ℝ≥0) < τ m ω →
        EqOn (fun s ↦ Hstage m s ω) (fun s ↦ H s ω) (Iic t)} := by
    intro ω hω
    by_cases hle : τ k ω ≤ (t : WithTop ℝ≥0)
    · exact Or.inl (Or.inr hle)
    · by_cases hgood : ∀ m, (t : WithTop ℝ≥0) < τ m ω →
          EqOn (fun s ↦ Hstage m s ω) (fun s ↦ H s ω) (Iic t)
      · refine Or.inl (Or.inl ?_)
        have heq_int : (∫⁻ s,
              ‖Finance.simpleHolding (grid k) (n k) (a k) s ω - Hstage k s ω‖ₑ ^ 2
                ∂timeMeasure t) =
            ∫⁻ s, ‖Finance.simpleHolding (grid k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
              ∂timeMeasure t := by
          rw [timeMeasure_def]
          exact setLIntegral_congr_fun measurableSet_Ioc fun s hs ↦ by
            have hs_eq : Hstage k s ω = H s ω := hgood k (not_le.mp hle) hs.2
            rw [hs_eq]
        simpa only [mem_ofPred_eq, heq_int] using hω
      · exact Or.inr hgood
  calc
    P _ ≤ P _ := measure_mono hinc
    _ ≤ P _ + P _ := measure_union_le _ _
    _ ≤ (P _ + P _) + 0 := by rw [← hnull]; exact add_le_add (measure_union_le _ _) le_rfl
    _ = _ := add_zero _

private theorem tendstoInMeasure_localized_simpleGains
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {X : ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0} (hloc : IsLocalizingSequence ℱ τ P)
    (hmono : ∀ ω, Monotone (τ · ω))
    {Hstage : ℕ → ℝ≥0 → Ω → ℝ} (hHstage : ∀ k, BrownianIntegrable ℱ P (Hstage k))
    {U : ℕ → ℝ≥0 → Ω → ℝ}
    (hUae : ∀ k t, U k t =ᵐ[P] hW.l2Integral t ((hHstage k).toPredictableLp t))
    (hstop : ∀ k, stoppedProcess X (τ k) ≡ᵐ[P] U k) (t : ℝ≥0)
    {n : ℕ → ℕ} {grid : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hgrid : ∀ k, MonotoneOn (grid k) (Iic (n k)))
    (ha : ∀ k j, j < n k → StronglyMeasurable[ℱ (grid k j)] (a k j))
    (ha₂ : ∀ k j, j < n k → MemLp (a k j) 2 P)
    (herr_lim : Tendsto (fun k ↦ eLpNorm
      (fun p ↦ Finance.simpleHolding (grid k) (n k) (a k) p.1 p.2 - Hstage k p.1 p.2) 2
        ((timeMeasure t).prod P)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (grid k) (n k) (a k) W t) atTop (X t) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have htail := tendsto_measure_le_of_isLocalizingSequence hloc hmono t
  have hG_stage : TendstoInMeasure P
      (fun k ω ↦ Finance.simpleGains (grid k) (n k) (a k) W t ω - U k t ω)
      atTop (0 : Ω → ℝ) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    have heq (k : ℕ) :
        eLpNorm ((fun ω ↦ Finance.simpleGains (grid k) (n k) (a k) W t ω - U k t ω) - 0) 2 P =
        eLpNorm (fun p ↦ Finance.simpleHolding (grid k) (n k) (a k) p.1 p.2 -
          Hstage k p.1 p.2) 2 ((timeMeasure t).prod P) := by
      rw [sub_zero]
      exact (eLpNorm_congr_ae (EventuallyEq.rfl.sub (hUae k t))).trans
        (hW.eLpNorm_simpleGains_sub_l2Integral (hHstage k) (hgrid k) (ha k) (ha₂ k) t)
    simpa only [heq] using herr_lim
  refine tendstoInMeasure_iff_norm.mpr fun ε hε ↦ ?_
  have hG_ε := (tendstoInMeasure_iff_norm.mp hG_stage) ε hε
  simp only [Pi.zero_apply, sub_zero] at hG_ε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hG_ε.add htail) (fun _ ↦ bot_le) fun k ↦ ?_
  have hnull_k : P {ω | stoppedProcess X (τ k) t ω ≠ U k t ω} = 0 :=
    ae_iff.mp ((hstop k).mono fun _ hω ↦ hω t)
  have hinc : {ω | ε ≤ ‖Finance.simpleGains (grid k) (n k) (a k) W t ω - X t ω‖} ⊆
      {ω | ε ≤ ‖Finance.simpleGains (grid k) (n k) (a k) W t ω - U k t ω‖} ∪
      {ω | τ k ω ≤ (t : WithTop ℝ≥0)} ∪
      {ω | stoppedProcess X (τ k) t ω ≠ U k t ω} := by
    intro ω hω
    by_cases hle : τ k ω ≤ (t : WithTop ℝ≥0)
    · exact Or.inl (Or.inr hle)
    · by_cases heq_u : stoppedProcess X (τ k) t ω = U k t ω
      · refine Or.inl (Or.inl ?_)
        have hXt : X t ω = U k t ω :=
          (stoppedProcess_eq_of_le (u := X) (not_le.mp hle).le).symm.trans heq_u
        simpa only [mem_ofPred_eq, hXt] using hω
      · exact Or.inr heq_u
  calc
    P _ ≤ P _ := measure_mono hinc
    _ ≤ P _ + P _ := measure_union_le _ _
    _ ≤ (P _ + P _) + 0 := by rw [← hnull_k]; exact add_le_add (measure_union_le _ _) le_rfl
    _ = _ := add_zero _

private theorem isItoIntegral_of_localized_stages
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : IsStronglyPredictable ℱ H)
    {X : ℝ≥0 → Ω → ℝ} (hX_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    {τ : ℕ → Ω → WithTop ℝ≥0} (hloc : IsLocalizingSequence ℱ τ P)
    (hmono : ∀ ω, Monotone (τ · ω))
    {Hstage : ℕ → ℝ≥0 → Ω → ℝ} (hHstage : ∀ k, BrownianIntegrable ℱ P (Hstage k))
    {U : ℕ → ℝ≥0 → Ω → ℝ}
    (hUae : ∀ k t, U k t =ᵐ[P] hW.l2Integral t ((hHstage k).toPredictableLp t))
    (hstop : ∀ k, stoppedProcess X (τ k) ≡ᵐ[P] U k)
    (hstage_eq : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ∀ k, (t : WithTop ℝ≥0) < τ k ω →
      EqOn (fun s ↦ Hstage k s ω) (fun s ↦ H s ω) (Iic t)) :
    IsItoIntegral ℱ P W H X where
  isStronglyPredictable := hH
  ae_continuous := hX_cont
  exists_seq_approx t := by
    let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    have hex (k : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t
      (hHstage k).isStronglyPredictable ((hHstage k).memLp_timeMeasure t)
      (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (k + 1)))
    choose n grid a C _ hgrid ha hb herr using hex
    have hinv : Tendsto (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have herr_lim : Tendsto (fun k ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (grid k) (n k) (a k) p.1 p.2 - Hstage k p.1 p.2) 2
          ((timeMeasure t).prod P)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
        (fun _ ↦ bot_le) fun k ↦ (herr k).le
    have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
      MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
        (Eventually.of_forall (hb k j hj))
    exact ⟨n, grid, a, fun k ↦ (hgrid k).monotoneOn, ha,
      fun _ hε ↦ tendsto_localized_energy_approx (fun k ↦ (hHstage k).isStronglyPredictable)
        hloc hmono t ha herr_lim (hstage_eq t) hε,
      hW.tendstoInMeasure_localized_simpleGains hloc hmono hHstage hUae hstop t
        (fun k ↦ (hgrid k).monotoneOn) ha ha₂ herr_lim⟩

private theorem exists_patched_energyLocalizer_process
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    letI := (hW.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
    ∃ (X : ℝ≥0 → Ω → ℝ) (U : ℕ → ℝ≥0 → Ω → ℝ),
      IsStronglyProgressive ℱ X ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) ∧
      Locally (fun Z ↦ Martingale Z ℱ P) ℱ X P ∧
      IsItoIntegral ℱ P W H X ∧
      (∀ m, IsStronglyPredictable ℱ (U m)) ∧
      (∀ m, ∀ᵐ ω ∂P, Continuous (fun t ↦ U m t ω)) ∧
      (∀ m t, U m t =ᵐ[P] hW.l2Integral t
        ((hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer
          (P := P) ((m : ℝ≥0) + 1)).toPredictableLp t)) ∧
      ∀ m : ℕ, stoppedProcess X (TauCeti.nnvolume.energyLocalizer H ((m : ℝ≥0) + 1)) ≡ᵐ[P] U m := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let τ (m : ℕ) := TauCeti.nnvolume.energyLocalizer H ((m : ℝ≥0) + 1)
  have hloc := hH.isLocalizingSequence_energyLocalizer
  let hHstage (m : ℕ) :=
    hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P) ((m : ℝ≥0) + 1)
  choose U hUp hUm hUcont hUae using fun m ↦ hW.exists_continuous_l2Integral hcont (hHstage m)
  have hcompat (n m : ℕ) (hnm : n ≤ m) : stoppedProcess (U m) (τ n) ≡ᵐ[P] U n := by
    refine Indistinguishable.of_ae_eq
      ((hUcont m).mono fun _ hc ↦ continuous_stoppedProcess (τ n) hc) (hUcont n) fun t ↦ ?_
    have hstop_ae := hW.stoppedProcess_ae_eq_l2Integral (hHstage m) (hUp m).stronglyAdapted
      ((hUcont m).mono fun _ hc _ ↦ hc.continuousWithinAt) (hUae m) (hloc.isStoppingTime n) t
    have hlp_eq : ((hHstage m).ite_le (hloc.isStoppingTime n)).toPredictableLp t =
        (hHstage n).toPredictableLp t := by
      refine BrownianIntegrable.toPredictableLp_congr _ _ (.of_forall fun ⟨s, ω⟩ ↦ ?_)
      have hτ_le : τ n ω ≤ τ m ω := TauCeti.nnvolume.monotone_energyLocalizer H ω
        (add_le_add (Nat.cast_le.mpr hnm) le_rfl)
      dsimp only [Function.uncurry_apply_pair, τ] at *
      by_cases hs : (s : WithTop ℝ≥0) ≤ TauCeti.nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω
      · rw [ite_eq_left hs, ite_eq_left (hs.trans hτ_le), ite_eq_left hs]
      · rw [ite_eq_right hs, ite_eq_right hs]
    exact hstop_ae.trans (hlp_eq ▸ (hUae n t).symm)
  obtain ⟨X, hX_prog, hX_cont, hX_stop⟩ :=
    TauCeti.exists_isStronglyProgressive_patch_stoppedProcess hloc.tendsto_top
      (fun m ↦ (hUp m).isStronglyProgressive) hUcont hcompat
  have hX_loc : Locally (fun Z ↦ Martingale Z ℱ P) ℱ X P := by
    refine hX_prog.locally_martingale_of_ae_stopped_eq hloc hUm fun n t ↦ ?_
    rw [show (fun s ↦ {ω | (⊥ : WithTop ℝ≥0) < τ n ω}.indicator (X s)) = X by
      ext s ω; exact indicator_of_mem (show 0 < τ n ω from TauCeti.nnvolume.energyLocalizer_pos H
        (C := (n : ℝ≥0) + 1) (by positivity) ω) _]
    exact (hX_stop n).symm.mono fun _ hω ↦ hω t
  have hX_ito : IsItoIntegral ℱ P W H X :=
    hW.isItoIntegral_of_localized_stages hH.isStronglyPredictable hX_cont hloc
      (fun ω _ _ hij ↦ TauCeti.nnvolume.monotone_energyLocalizer H ω
        (add_le_add (Nat.cast_le.mpr hij) le_rfl))
      hHstage hUae hX_stop fun t ↦ hH.ae_accumulatedEnergy_lt_top.mono fun ω hfin k hlt s hs ↦ by
        have hst : s ≤ t := hs
        have hle : (s : WithTop ℝ≥0) ≤ τ k ω := (WithTop.coe_le_coe.mpr hst).trans hlt.le
        dsimp only [τ] at hle
        simpa only [ite_eq_left hle] using TauCeti.nnvolume.finiteEnergyCutoff_eqOn (hfin t) hs
  exact ⟨X, U, hX_prog, hX_cont, hX_loc, hX_ito, hUp, hUcont, hUae, hX_stop⟩

/-- **Existence of the continuous-time Brownian Itô integral.** For a filtration-relative Brownian
motion `W` with almost surely continuous paths and a `LocallyBrownianIntegrable` integrand `H`,
there exists a strongly predictable native local martingale `I` on the original raw filtration
satisfying `IsItoIntegral ℱ P W H I`. -/
theorem exists_isItoIntegral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ I ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ I P ∧
      IsItoIntegral ℱ P W H I := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨X, _, _, hX_cont, hX_loc, hX_ito, _⟩ :=
    hW.exists_patched_energyLocalizer_process hcont hH
  obtain ⟨I, hI_pred, hIX, hI_loc⟩ :=
    hX_loc.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hX_cont.mono fun _ hc _ ↦ hc.continuousWithinAt)
  exact ⟨I, hI_pred, hI_loc, hX_ito.of_indist hIX.symm⟩

/-- **Local-martingale property of the Brownian Itô integral.** Any strongly progressive process
satisfying `IsItoIntegral` for a `LocallyBrownianIntegrable` integrand is a native local
martingale on the original raw filtration. -/
theorem itoIntegral_localMartingale
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI_prog : IsStronglyProgressive ℱ I) (hI : IsItoIntegral ℱ P W H I) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ I P := by
  obtain ⟨J, _, hJ_loc, hJ_ito⟩ := hW.exists_isItoIntegral hcont hH
  exact hI_prog.locally_martingale_of_indist hJ_loc (hW.isItoIntegral_unique hJ_ito hI)

/-- **Optional stopping of the Brownian Itô integral.** Stopping an Itô integral of a
`LocallyBrownianIntegrable` integrand `H` at any raw stopping time `σ` yields an Itô integral of
`H` cut off to `⟦0, σ⟧`. -/
theorem itoIntegral_stoppedProcess
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (stoppedProcess I σ) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨X, U, _, hX_cont, _, hX_ito, hUp, hUcont, hUae, hX_stop⟩ :=
    hW.exists_patched_energyLocalizer_process hcont hH
  let τ (k : ℕ) := TauCeti.nnvolume.energyLocalizer H ((k : ℝ≥0) + 1)
  let hHstage (k : ℕ) :=
    (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer (P := P)
      ((k : ℝ≥0) + 1)).ite_le hσ
  have hUσ_ae (k : ℕ) (t : ℝ≥0) :
      stoppedProcess (U k) σ t =ᵐ[P] hW.l2Integral t ((hHstage k).toPredictableLp t) :=
    hW.stoppedProcess_ae_eq_l2Integral _ (hUp k).stronglyAdapted
      ((hUcont k).mono fun _ hc _ ↦ hc.continuousWithinAt) (hUae k) hσ t
  have hXσ_stop (k : ℕ) :
      stoppedProcess (stoppedProcess X σ) (τ k) ≡ᵐ[P] stoppedProcess (U k) σ := by
    rw [stoppedProcess_stoppedProcess, inf_comm, ← stoppedProcess_stoppedProcess]
    exact (hX_stop k).mono fun ω hω t ↦ by dsimp only [stoppedProcess]; exact hω _
  have hXσ_ito : IsItoIntegral ℱ P W
      (fun t : ℝ≥0 ↦ fun ω ↦ if (t : WithTop ℝ≥0) ≤ σ ω then H t ω else 0)
      (stoppedProcess X σ) := by
    refine hW.isItoIntegral_of_localized_stages (hH.isStronglyPredictable.ite_le hσ)
      (hX_cont.mono fun _ hc ↦ continuous_stoppedProcess σ hc)
      hH.isLocalizingSequence_energyLocalizer
      (fun ω _ _ hij ↦ TauCeti.nnvolume.monotone_energyLocalizer H ω
        (add_le_add (Nat.cast_le.mpr hij) le_rfl))
      hHstage hUσ_ae hXσ_stop fun t ↦ ?_
    filter_upwards [hH.ae_accumulatedEnergy_lt_top] with ω hfin k hlt s hs
    have hst : s ≤ t := hs
    have hle : (s : WithTop ℝ≥0) ≤ τ k ω := (WithTop.coe_le_coe.mpr hst).trans hlt.le
    have hcut : TauCeti.nnvolume.finiteEnergyCutoff H s ω = H s ω :=
      TauCeti.nnvolume.finiteEnergyCutoff_eqOn (hfin t) hs
    dsimp only [τ] at hle
    dsimp only
    rw [ite_eq_left hle, hcut]
  have hIX : stoppedProcess X σ ≡ᵐ[P] stoppedProcess I σ :=
    (hW.isItoIntegral_unique hX_ito hI).mono fun ω hω t ↦ by dsimp only [stoppedProcess]; exact hω _
  exact hXσ_ito.of_indist hIX

/-- **Local congruence of the Brownian Itô integral.** If two `LocallyBrownianIntegrable`
integrands agree product-almost-everywhere on `⟦0, σ⟧` over every finite horizon for a raw stopping
time `σ`, their Itô integrals agree up to indistinguishability when stopped at `σ`. -/
theorem itoIntegral_local_congr
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) (hK : LocallyBrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ)
    (hHK : ∀ t : ℝ≥0,
      Function.uncurry (fun s : ℝ≥0 ↦ fun ω ↦ if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0) =ᵐ[
        (timeMeasure t).prod P]
      Function.uncurry (fun s : ℝ≥0 ↦ fun ω ↦ if (s : WithTop ℝ≥0) ≤ σ ω then K s ω else 0)) :
    stoppedProcess I σ ≡ᵐ[P] stoppedProcess J σ := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hIσ := (hW.itoIntegral_stoppedProcess hcont hH hI hσ).congr_integrand
    (hK.isStronglyPredictable.ite_le hσ) hHK
  exact hW.isItoIntegral_unique hIσ (hW.itoIntegral_stoppedProcess hcont hK hJ hσ)

/-- Every Itô integral of a `LocallyBrownianIntegrable` integrand vanishes almost surely at `0`. -/
theorem itoIntegral_ae_eval_zero
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    I 0 =ᵐ[P] 0 := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have h0 : IsStoppingTime ℱ (fun _ : Ω ↦ (0 : WithTop ℝ≥0)) := isStoppingTime_const ℱ 0
  have hHK (t : ℝ≥0) :
      Function.uncurry (fun s : ℝ≥0 ↦ fun ω ↦
        if (s : WithTop ℝ≥0) ≤ (0 : WithTop ℝ≥0) then H s ω else 0) =ᵐ[
        (timeMeasure t).prod P] Function.uncurry (0 : ℝ≥0 → Ω → ℝ) := by
    rw [timeMeasure_def]
    have hmem : ∀ᵐ p ∂((Measure.comap ((↑) : ℝ≥0 → ℝ) volume).restrict (Ioc 0 t)).prod P,
        0 < p.1 :=
      (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)).mpr
        ((ae_restrict_mem measurableSet_Ioc).mono fun _ hs ↦ .of_forall fun _ ↦ hs.1)
    exact hmem.mono fun ⟨s, ω⟩ hs ↦ ite_eq_right (not_le.mpr (WithTop.coe_lt_coe.mpr hs))
  have hind := hW.isItoIntegral_unique
    ((hW.itoIntegral_stoppedProcess hcont hH hI h0).congr_integrand
      (IsItoIntegral.zero (ℱ := ℱ) (P := P) (W := W)).isStronglyPredictable hHK)
    IsItoIntegral.zero
  exact hind.mono fun ω hω ↦ by simpa [stoppedProcess] using hω 0

/-- When `H` has finite expected square energy on every finite horizon (`BrownianIntegrable`), any
process `I` satisfying `IsItoIntegral ℱ P W H I` agrees almost everywhere at each time `t` with
`hW.l2Integral t (hH.toPredictableLp t)`. -/
theorem itoIntegral_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t) := by
  obtain ⟨J, _, _, hJ_cont, hJ_ae⟩ := hW.exists_continuous_l2Integral hcont hH
  have hIJ := hW.isItoIntegral_unique hI (hW.isItoIntegral_of_ae_eq_l2Integral hH hJ_cont hJ_ae)
  exact EventuallyEq.trans (hIJ.mono fun _ hω ↦ hω t) (hJ_ae t)

/-- **Cross-isometry of the Brownian Itô integral** on `BrownianIntegrable` integrands. -/
theorem itoIntegral_mul_isometry
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (T : ℝ≥0) :
    ∫ ω, I T ω * J T ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure T).prod P :=
  hW.integral_mul_of_ae_eq_l2Integral hH hK
    (hW.itoIntegral_ae_eq_l2Integral hcont hH hI)
    (hW.itoIntegral_ae_eq_l2Integral hcont hK hJ) T

/-- **Itô isometry** for any process satisfying `IsItoIntegral` of a `BrownianIntegrable`
integrand. -/
theorem itoIntegral_isometry
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure T).prod P := by
  simpa only [sq] using hW.itoIntegral_mul_isometry hcont hH hH hI hI T

/-- Any strongly adapted Itô integral of a `BrownianIntegrable` integrand is a true martingale on
the original raw filtration, with square-compensation martingale `I_t² - ∫_{(0, t]} H_s² ds`. -/
theorem itoIntegral_martingale
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H)
    (hI_adapt : StronglyAdapted ℱ I) (hI : IsItoIntegral ℱ P W H I) :
    Martingale I ℱ P ∧
      Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P :=
  ⟨hW.martingale_of_ae_eq_l2Integral hH hI_adapt (hW.itoIntegral_ae_eq_l2Integral hcont hH hI),
    hW.martingale_sq_sub_integral_of_ae_eq_l2Integral hH hI_adapt
      (hW.itoIntegral_ae_eq_l2Integral hcont hH hI)⟩

end IsFilteredPreBrownianReal

end TauCeti.Probability
