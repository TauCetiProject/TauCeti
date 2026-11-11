/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Measurability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Local finiteness from the intensity of a random measure

The intensity of a random measure `N` on a measure space with measure `P` is the mixture
`P.bind N`. If this intensity is finite on compact sets, then almost every realization is
locally finite. The exceptional event is independent of the compact set: a compact exhaustion
reduces the assertion to countably many evaluations. No probability normalization or topology
on the sample space is needed.

`Measure.isFiniteMeasureOnCompacts_bind_iff` tests local finiteness of the intensity using
expected masses on any compact exhaustion. The converse to the almost-sure assertion is not
claimed: almost-sure local finiteness need not give finite expected masses.

The measurable local-finiteness event is supplied by
`MeasureTheory.measurableSet_isLocallyFiniteMeasure`. Together with
`AEMeasurable.exists_ae_eq_range_subset`, it allows one to choose a measurable version all of
whose values are locally finite, without changing the law. These results are useful for
passing from a measure-valued construction to locally finite configurations.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 2 (intensity measures and local finiteness).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [T2Space X] {N : Ω → Measure X}

/-- The intensity is finite on compact sets exactly when the expected masses of the sets
of a compact exhaustion are finite. The choice of exhaustion is arbitrary. -/
theorem isFiniteMeasureOnCompacts_bind_iff (P : Measure Ω) (hN : AEMeasurable N P)
    (K : CompactExhaustion X) :
    IsFiniteMeasureOnCompacts (P.bind N) ↔
      ∀ n, ∫⁻ ω, N ω (K n) ∂P < ∞ := by
  rw [K.isFiniteMeasureOnCompacts_iff]
  simp_rw [Measure.bind_apply (K.isCompact _).measurableSet hN]

/-- Finite expected mass on every set of a compact exhaustion implies local finiteness
almost surely, simultaneously at every location. -/
theorem ae_isLocallyFiniteMeasure_of_lintegral_lt_top (P : Measure Ω)
    (hN : AEMeasurable N P) (K : CompactExhaustion X)
    (hK : ∀ n, ∫⁻ ω, N ω (K n) ∂P < ∞) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (N ω) := by
  have hfinite (n : ℕ) : ∀ᵐ ω ∂P, N ω (K n) < ∞ :=
    ae_lt_top' ((Measure.measurable_coe (K.isCompact n).measurableSet).comp_aemeasurable hN)
      (hK n).ne
  filter_upwards [ae_all_iff.2 hfinite] with ω hω
  exact (K.isLocallyFiniteMeasure_iff (N ω)).2 hω

/-- A random measure with locally finite intensity is almost surely locally finite.
No finite-total-mass or probability hypothesis on the sample measure is needed. -/
theorem ae_isLocallyFiniteMeasure_of_bind (P : Measure Ω) (hN : AEMeasurable N P)
    [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    [IsFiniteMeasureOnCompacts (P.bind N)] :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (N ω) := by
  let K := CompactExhaustion.choice X
  exact P.ae_isLocallyFiniteMeasure_of_lintegral_lt_top hN K
    ((P.isFiniteMeasureOnCompacts_bind_iff hN K).1 inferInstance)

end MeasureTheory.Measure
