/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic

/-!
# A projection-valued measure splits norms along a partition

`∑ ‖proj (B k) ξ‖² = ‖ξ‖²` when the `B k` are a countable measurable partition
of `ℝ`.

`Basic.lean` carries the diagonal measures as data and proves the quadratic
identity `‖proj B ξ‖² = diag ξ B` in real form.  Everything here is that
identity restated in `ℝ≥0∞`, where it says the *measure* directly, so countable
additivity of `diag ξ` — an honest Borel measure — transfers to the projections
with no summability bookkeeping.

This is the hypothesis that
`TauCeti.HilbertSchmidt.tsum_energy_isometryFamily_comp` and its two-sided
companion take: a family that splits vector norms splits the Hilbert–Schmidt
energy.  Spectral projections over a partition of the line are the instance the
block argument for the Sylvester spectral gap uses.

## Sources

*Follows nothing in particular*: one identity of `ProjValMeasure/Basic.lean` restated in
`ℝ≥0∞` so that countable additivity transfers with no summability bookkeeping.

## Provenance

*New.*
-/

public section

open scoped ENNReal NNReal InnerProductSpace
open MeasureTheory

namespace TauCeti

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProjValMeasure

/-- The quadratic identity in `ℝ≥0∞`: the squared enorm of a projection *is* the
diagonal measure of the set.  The real-valued form needs a `toReal`, which is
what makes additivity awkward; this form does not. -/
@[simp]
theorem enorm_sq_proj_apply (P : ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B)
    (ξ : H) : ‖P.proj B hB ξ‖ₑ ^ 2 = (P.diag ξ) B := by
  have := P.diag_finite ξ
  have hfin : (P.diag ξ) B ≠ ⊤ := measure_ne_top _ _
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
    ← ENNReal.ofReal_pow (norm_nonneg _), P.norm_sq_proj_apply B hB ξ,
    ENNReal.ofReal_toReal hfin]

/-- Total mass, in `ℝ≥0∞`. -/
theorem diag_univ (P : ProjValMeasure H) (ξ : H) :
    (P.diag ξ) Set.univ = ‖ξ‖ₑ ^ 2 := by
  have h := P.enorm_sq_proj_apply Set.univ MeasurableSet.univ ξ
  rw [P.proj_univ] at h
  simpa using h.symm

/-- **A projection-valued measure splits norms along a partition.**  Countable
additivity of the diagonal measure, read through the quadratic identity. -/
theorem tsum_enorm_sq_proj (P : ProjValMeasure H) {ι : Type*} [Countable ι]
    (B : ι → Set ℝ) (hB : ∀ k, MeasurableSet (B k))
    (hdisj : Pairwise (Function.onFun Disjoint B)) (hcov : (⋃ k, B k) = Set.univ)
    (ξ : H) :
    ∑' k, ‖P.proj (B k) (hB k) ξ‖ₑ ^ 2 = ‖ξ‖ₑ ^ 2 := by
  have hmeas : ∑' k, (P.diag ξ) (B k) = (P.diag ξ) Set.univ := by
    rw [← hcov, measure_iUnion hdisj hB]
  rw [tsum_congr fun k => P.enorm_sq_proj_apply (B k) (hB k) ξ, hmeas, P.diag_univ ξ]

end ProjValMeasure
end TauCeti
