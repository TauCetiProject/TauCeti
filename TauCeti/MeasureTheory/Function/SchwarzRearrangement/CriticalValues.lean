/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.SchwarzRearrangement.Lipschitz
public import TauCeti.Analysis.Calculus.Sard.Radial
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Critical values of Schwarz rearrangements

The real-valued Schwarz rearrangement of the positive part of a Lipschitz function has a
Lebesgue-null set of critical values. Thus almost every level contains neither zero-gradient
points nor nondifferentiability points. This is the radial critical-value input to the
reciprocal-gradient coarea formula for the distribution function of a rearrangement.

The representative is the canonical `schwarzRearrangement` followed by `ENNReal.toReal`.
For integrable inputs the extended rearrangement is finite almost everywhere, by
`MeasureTheory.Integrable.ae_schwarzRearrangement_ofReal_ne_top`. The critical-value assertion
itself needs no integrability hypothesis and retains the same totalization conventions as
`TauCeti.lipschitzWith_toReal_schwarzRearrangement`.

## References

* Bianchi–Gardner–Gronchi–Kiderlen, *The Pólya–Szegő inequality for smoothing rearrangements*,
  arXiv:2206.09833, proof of Theorem 5.8.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {K : ℝ≥0} {h : E → ℝ}

/-- The totalized critical values of the real Schwarz rearrangement of the positive part of a
Lipschitz function form a Lebesgue-null set. In particular, images of nondifferentiability points
are included in this exceptional set. -/
theorem volume_image_setOf_fderiv_toReal_schwarzRearrangement_eq_zero
    (hh : LipschitzWith K h) :
    volume ((fun x ↦ (TauCeti.schwarzRearrangement volume
      (fun y ↦ ENNReal.ofReal (h y)) x).toReal) ''
      {x | fderiv ℝ (fun z ↦ (TauCeti.schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x = 0}) = 0 := by
  have hLip := TauCeti.lipschitzWith_toReal_schwarzRearrangement volume hh
  apply hLip.volume_image_setOf_fderiv_eq_zero_of_norm_eq
  intro x y hxy
  exact congrArg ENNReal.toReal (TauCeti.schwarzRearrangement_eq_of_norm_eq volume _ hxy)

end LipschitzWith
