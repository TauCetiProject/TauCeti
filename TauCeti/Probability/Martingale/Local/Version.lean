/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Local.Congruence
public import TauCeti.Probability.Process.LocalProperty
public import TauCeti.Probability.Process.Predictable.Basic

/-!
# Predictable versions of local martingales

A native local martingale with almost-surely left-continuous paths has a predictable,
indistinguishable version which is again a native local martingale on the original
filtration. In particular, this applies to almost-surely continuous local martingales.
It supplies representatives suitable for stopped evaluation and stochastic integration
without completing or enlarging the filtration.

Native locality alone does not imply adaptation of the original process: its stopped
stages can hide arbitrary changes on exceptional sample points. We first use
`ProbabilityTheory.Locally.exists_stronglyAdapted_ae_eq` to recover an adapted
representative from those stages. The predictable-version theorem for adapted
left-continuous processes then applies, and progressive congruence preserves locality.
All comparisons hold simultaneously in time outside one common null set, rather than
only almost surely at each deterministic time.

No moment assumption on the initial value, finiteness assumption on the measure,
completeness, or right continuity of the filtration is required. The selected version
need not have left-continuous paths on the exceptional null set.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.Locally

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}

/-- An almost-surely left-continuous native local martingale has a predictable
indistinguishable version which remains a native local martingale for the same measure
and filtration. Literal adaptation of the original process is not assumed. -/
theorem exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P)
    (hc : ∀ᵐ ω ∂P, IsLeftContinuous (fun t ↦ X t ω)) :
    ∃ Y : ℝ≥0 → Ω → E, IsStronglyPredictable ℱ Y ∧ Y ≡ᵐ[P] X ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ Y P := by
  obtain ⟨Z, hZ, hZX⟩ := hX.exists_stronglyAdapted_ae_eq fun _ h ↦ h.stronglyAdapted
  have hcZ : ∀ᵐ ω ∂P, IsLeftContinuous (fun t ↦ Z t ω) := by
    filter_upwards [hc, hZX] with ω hω heq
    simpa only [funext heq] using hω
  obtain ⟨Y, hY, hYZ⟩ :=
    hZ.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous hcZ
  have hYX : Y ≡ᵐ[P] X := hYZ.trans hZX
  exact ⟨Y, hY, hYX, hY.isStronglyProgressive.locally_martingale_of_indist hX hYX.symm⟩

end ProbabilityTheory.Locally
