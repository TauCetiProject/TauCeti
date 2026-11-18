/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Basic.ENNReal.Real
public import TauCeti.Probability.Martingale.MaximalInequality.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IsLUB

/-!
# Closed-level event-refined maximal inequality and running-supremum finiteness

For a nonnegative submartingale, Doob's maximal inequality retains the crossing event in the
terminal expectation. This refinement, unlike the weak bound by the whole terminal expectation,
can be integrated over the threshold to obtain strong maximal estimates for stochastic-integral
approximation.

We extend the strict-crossing refinement from `MaximalInequality.Basic` to the closed event
that the running supremum is at least the threshold, for both nonnegative and general signed real
submartingales, and record almost sure finiteness of the running supremum for right-continuous
submartingales and Banach-valued martingales. No usual-filtration assumption is needed.
Uncountable crossing events are interpreted using outer measure and restricted integrals;
right continuity identifies them almost everywhere with countable measurable crossing events.
The finite-set input in `MaximalInequality.Basic` uses Mathlib's `maximal_ineq` without dropping
its terminal event indicator.

## Main declarations

* `MeasureTheory.Submartingale.mul_measure_le_iSup_le_setIntegral`,
  `MeasureTheory.Submartingale.mul_measure_le_iSup_le_setIntegral_posPart`,
  `MeasureTheory.Submartingale.mul_measure_le_iSup_le_integral_posPart`: closed-level Doob
  inequalities for nonnegative and general real submartingales.
* `MeasureTheory.Submartingale.ae_iSup_ofReal_lt_top`,
  `MeasureTheory.Martingale.ae_iSup_eNorm_lt_top`: almost sure finiteness of the running supremum
  before `T` for right-continuous submartingales and Banach-valued martingales.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 1.3.8.
-/

public section
noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  {ℱ : Filtration ι m0} {f : ι → Ω → ℝ} [IsFiniteMeasure μ]

/-- **Closed-level event-refined Doob inequality.** The running supremum is taken in `ℝ≥0∞`,
so no pathwise boundedness assumption or convention for an unattained real supremum is needed.
The terminal expectation retains exactly the event that this supremum is at least `ε`. -/
theorem mul_measure_le_iSup_le_setIntegral
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (ε : ℝ≥0) :
    ε * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        f T ω ∂μ) := by
  by_cases hε : ε = 0
  · simp [hε]
  obtain ⟨δ, hδmono, hδmem, hδlim⟩ := exists_seq_strictMono_tendsto' (pos_iff_ne_zero.2 hε)
  let Y : Ω → ℝ≥0∞ := fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)
  let A : ℕ → Set Ω := fun n ↦ {ω | (δ n : ℝ≥0∞) < Y ω}
  have hY : AEMeasurable Y μ := hf.aemeasurable_iSup_ofReal hcont
  have hA (n : ℕ) : NullMeasurableSet (A n) μ := nullMeasurableSet_lt aemeasurable_const hY
  have hanti : Antitone A := by
    intro i j hij ω h
    have hij' : (δ i : ℝ≥0∞) ≤ δ j := by exact_mod_cast hδmono.monotone hij
    exact hij'.trans_lt h
  have hδlim' : Tendsto (fun n ↦ (δ n : ℝ≥0∞)) atTop (𝓝 (ε : ℝ≥0∞)) :=
    ENNReal.continuous_coe.tendsto ε |>.comp hδlim
  have hInter : (⋂ n, A n) = {ω | (ε : ℝ≥0∞) ≤ Y ω} := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, A]
    exact ⟨fun h ↦ le_of_tendsto' hδlim' (fun n ↦ (h n).le),
      fun h n ↦ lt_of_lt_of_le (by exact_mod_cast (hδmem n).2) h⟩
  -- Decreasing crossing events converge in measure and under the terminal expectation.
  have hmeasure := tendsto_measure_iInter_atTop hA hanti ⟨0, measure_ne_top _ _⟩
  have hint := tendsto_integral_of_dominated_convergence (fun ω ↦ ‖f T ω‖)
    (fun n ↦ (hf.integrable T).aestronglyMeasurable.indicator₀ (hA n)) (hf.integrable T).norm
    (fun n ↦ Eventually.of_forall (fun ω ↦ norm_indicator_le_norm_self (f T) ω))
    (Eventually.of_forall (fun ω ↦ (hanti.tendsto_indicator _ _ _).trans (pure_le_nhds _)))
  simp_rw [integral_indicator₀ (hA _)] at hint
  rw [integral_indicator₀ (NullMeasurableSet.iInter hA)] at hint
  have hbound (n : ℕ) : δ n * μ (A n) ≤ ENNReal.ofReal (∫ ω in A n, f T ω ∂μ) := by
    have hset : A n = {ω | ∃ t ≤ T, (δ n : ℝ) < f t ω} := by
      ext ω
      simp [A, Y, lt_iSup_iff, ENNReal.coe_lt_ofReal]
    rw [hset]
    exact hf.mul_measure_exists_le_lt_le_setIntegral hnonneg hcont (δ n)
  have h := le_of_tendsto_of_tendsto'
    (ENNReal.Tendsto.mul hδlim' (Or.inr (measure_ne_top _ _)) hmeasure
      (Or.inr ENNReal.coe_ne_top)) (ENNReal.tendsto_ofReal hint) hbound
  simpa only [hInter] using h

/-- **Closed-level event-refined positive-part Doob inequality.** Because `ENNReal.ofReal` vanishes
on `(-∞, 0]`, `⨆ t ≤ T, ENNReal.ofReal (f t ω)` coincides pointwise with
`⨆ t ≤ T, ENNReal.ofReal ((f⁺) t ω)`. -/
theorem mul_measure_le_iSup_le_setIntegral_posPart
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) (ε : ℝ≥0) :
    ε * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        (f⁺) T ω ∂μ) := by
  have hsup (ω : Ω) : (⨆ t ≤ T, ENNReal.ofReal ((f⁺) t ω)) = ⨆ t ≤ T, ENNReal.ofReal (f t ω) := by
    simp_rw [Pi.posPart_apply, ENNReal.ofReal_posPart]
  have hcont_pos : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ (f⁺) u ω) (Ioi t) t :=
    hcont.mono fun _ hω t ht ↦ by
      simpa only [Pi.posPart_apply, posPart_def] using (hω t ht).sup continuousWithinAt_const
  simpa only [hsup] using
    hf.pos.mul_measure_le_iSup_le_setIntegral (fun _ _ ↦ posPart_nonneg _) hcont_pos ε

/-- **Closed-level positive-part Doob maximal inequality** (`ε P(sup_{t ≤ T} f_t ≥ ε) ≤ E[(f_T)⁺]`).
Holds for every real submartingale `f` with right-continuous paths before `T` and `ε : ℝ≥0`. -/
theorem mul_measure_le_iSup_le_integral_posPart
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) (ε : ℝ≥0) :
    ε * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω, (f⁺) T ω ∂μ) :=
  (hf.mul_measure_le_iSup_le_setIntegral_posPart hcont ε).trans
    (ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hf.pos.integrable T)
      (Eventually.of_forall fun _ ↦ posPart_nonneg _)))

/-- **Almost sure finiteness of the running supremum of a submartingale.** Any real submartingale
with almost surely right-continuous paths before `T` on a finite measure space has almost everywhere
finite running supremum `⨆ t ≤ T, ENNReal.ofReal (f t ω) < ∞` (no higher `Lᵖ` moment is needed). -/
theorem ae_iSup_ofReal_lt_top
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) :
    ∀ᵐ ω ∂μ, (⨆ t ≤ T, ENNReal.ofReal (f t ω)) < ∞ := by
  obtain ⟨S, hSc, hST, hae⟩ := exists_countable_subset_Iic_iSup_ofReal_ae_eq hcont
  filter_upwards [hae, hf.ae_biSup_ofReal_lt_top hSc fun _ hs ↦ hST hs] with ω hω hlt
  rwa [hω]

end MeasureTheory.Submartingale

namespace MeasureTheory.Martingale

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [IsFiniteMeasure μ] {ℱ : Filtration ι mΩ} {M : ι → Ω → E}

/-- **Almost sure finiteness of the running norm supremum of a right-continuous martingale.** No
`MemLp` assumption beyond martingale integrability is needed. -/
theorem ae_iSup_eNorm_lt_top (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t) :
    ∀ᵐ ω ∂μ, (⨆ t ≤ T, ‖M t ω‖ₑ) < ∞ := by
  simp_rw [← ofReal_norm]
  exact hM.submartingale_norm.ae_iSup_ofReal_lt_top (hcont.mono fun _ hω t ht ↦ (hω t ht).norm)

end MeasureTheory.Martingale
