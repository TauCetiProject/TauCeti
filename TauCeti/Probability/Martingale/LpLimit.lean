/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Fixed-time Lᵖ completion of martingales

A sequence of martingales which is Cauchy in Lᵖ at every date, for `1 ≤ p ≤ ∞` on a
finite measure space, has a martingale limit with Lᵖ convergence at every date.
The limit is literally strongly adapted to the original filtration: choosing an
arbitrary representative of an ambient Lᵖ limit would not ensure this on a raw
filtration. Instead, closedness of the subspace of measurable Lᵖ classes supplies
a representative measurable at each date.

This is the fixed-time completion step used when extending elementary stochastic
integrals. It does not assert path continuity, progressive measurability, or
simultaneous-time convergence. Those require additional uniform approximation.

The L¹ stability theorem also works for arbitrary measures whose filtration trims
are sigma-finite, and does not need an integrable dominator.

The construction uses Mathlib's Lᵖ completeness and
`MeasureTheory.isClosed_aestronglyMeasurable` for measurable classes.
-/

public section

noncomputable section

open Filter
open scoped Topology ENNReal

namespace MeasureTheory

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {ℱ : Filtration ι mΩ} {X : ℕ → ι → Ω → E} {Y : ι → Ω → E}

/-- A strongly adapted fixed-time L¹ limit of martingales is a martingale.
No domination, path regularity, or completeness of the filtration is required. -/
theorem martingale_of_tendsto_eLpNorm_one [SigmaFiniteFiltration μ ℱ]
    (hX : ∀ n, Martingale (X n) ℱ μ) (hY : StronglyAdapted ℱ Y)
    (hlim : ∀ t, Tendsto (fun n => eLpNorm (X n t - Y t) 1 μ) atTop (𝓝 0)) :
    Martingale Y ℱ μ := by
  have hint : ∀ t, Integrable (Y t) μ := fun t =>
    memLp_one_iff_integrable.mp (Lp.memLp_of_cauchy_tendsto le_rfl
      (fun n => memLp_one_iff_integrable.mpr ((hX n).integrable t)) (Y t) (hlim t))
  refine ⟨hY, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (hY s).aestronglyMeasurable).symm
  exact tendsto_nhds_unique_of_eventuallyEq
    (tendsto_setIntegral_of_L1' (Y s) (Eventually.of_forall fun n => (hX n).integrable s)
      (hlim s) A)
    (tendsto_setIntegral_of_L1' (Y t) (Eventually.of_forall fun n => (hX n).integrable t)
      (hlim t) A)
    (Eventually.of_forall fun n => (hX n).setIntegral_eq hst hA)

/-- Fixed-time Lᵖ-Cauchy martingales on a finite measure space admit a strongly adapted
martingale limit in Lᵖ, including `p = ∞`. The conclusion concerns convergence separately
at each date; it makes no assertion about paths or a common exceptional set. -/
theorem exists_martingale_of_cauchySeq_Lp [IsFiniteMeasure μ] {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    (hX : ∀ n, Martingale (X n) ℱ μ)
    (hmem : ∀ n t, MemLp (X n t) p μ)
    (hcau : ∀ t, CauchySeq (fun n => (hmem n t).toLp (X n t))) :
    ∃ Y : ι → Ω → E, Martingale Y ℱ μ ∧ ∀ t, MemLp (Y t) p μ ∧
      Tendsto (fun n => eLpNorm (X n t - Y t) p μ) atTop (𝓝 0) := by
  choose g hg using fun t => cauchySeq_tendsto_of_complete (hcau t)
  have hmeas : ∀ t, AEStronglyMeasurable[ℱ t] (g t) μ := by
    intro t
    exact (isClosed_aestronglyMeasurable (F := E) (p := p) (ℱ.le t)).mem_of_tendsto
      (hg t) (Eventually.of_forall fun n =>
        ((hX n).stronglyAdapted t).aestronglyMeasurable.congr (hmem n t).coeFn_toLp.symm)
  let Y : ι → Ω → E := fun t => (hmeas t).mk (g t)
  have hY : StronglyAdapted ℱ Y := fun t => (hmeas t).stronglyMeasurable_mk
  have hYm : ∀ t, MemLp (Y t) p μ := fun t =>
    (Lp.memLp (g t)).ae_eq (hmeas t).ae_eq_mk
  have hlim : ∀ t, Tendsto (fun n => eLpNorm (X n t - Y t) p μ) atTop (𝓝 0) := by
    intro t
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hmem n t) _ (hYm t)).mp
    have heq : (hYm t).toLp (Y t) = g t := by
      apply Lp.ext
      exact (hYm t).coeFn_toLp.trans (hmeas t).ae_eq_mk.symm
    rw [heq]
    exact hg t
  exact ⟨Y, martingale_of_tendsto_eLpNorm_one hX hY (fun t =>
    TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm hp.out (hlim t)),
    fun t => ⟨hYm t, hlim t⟩⟩

end MeasureTheory
