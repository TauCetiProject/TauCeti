/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar measures determined by one integral

On a second countable locally compact group, a left-invariant measure that is finite on compacts
is a multiple `c • ν` of any Haar measure `ν` (`MeasureTheory.Measure.isMulLeftInvariant_eq_smul`).
Hence it equals `ν` as soon as both give the same nonzero integral to a single function
(`MeasureTheory.Measure.eq_haar_of_integral_eq`). This is how a Haar measure is pinned down by a
normalisation such as `∫ |f| ^ 2 = 1`. Both multiplicative and additive versions are provided.

## Main results

* `MeasureTheory.Measure.eq_haar_of_integral_eq`: a left-invariant measure, finite on compacts,
  that gives a function the same nonzero integral as a Haar measure is that Haar measure. The
  additive version is `MeasureTheory.Measure.eq_addHaar_of_integral_eq`.

## Provenance

Generalised from `New.addHaar_eq_of_integral_eq_one` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/General/Measure/HaarNormalisation.lean`, which states it for two additive Haar measures
and a real function with integral `1`.
-/

public section

open scoped NNReal

namespace MeasureTheory.Measure

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A left-invariant measure that is finite on compacts and gives a function `f` the same
nonzero integral as a Haar measure `ν` is equal to `ν`. -/
@[to_additive /-- A left-invariant measure that is finite on compacts and gives a function `f`
the same nonzero integral as an additive Haar measure `ν` is equal to `ν`. -/]
theorem eq_haar_of_integral_eq {μ ν : Measure G} [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] [ν.IsHaarMeasure] {f : G → E} (h : ∫ x, f x ∂μ = ∫ x, f x ∂ν)
    (hf : ∫ x, f x ∂ν ≠ 0) : μ = ν := by
  obtain ⟨c, rfl⟩ : ∃ c : ℝ≥0, μ = c • ν := ⟨_, μ.isMulLeftInvariant_eq_smul ν⟩
  obtain rfl : c = 1 := by
    rw [integral_smul_nnreal_measure, NNReal.smul_def] at h
    have h_zero : ((c : ℝ) - 1) • ∫ x, f x ∂ν = 0 := by rw [sub_smul, one_smul, h, sub_self]
    simpa [sub_eq_zero] using (smul_eq_zero.1 h_zero).resolve_right hf
  exact one_smul _ ν

end MeasureTheory.Measure
