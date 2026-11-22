/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Equidistribution.Weyl
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.SpecificLimits.VanDerCorput

/-!
# Van der Corput's difference theorem on `UnitAddTorus d`

If every positive-lag difference sequence `n ↦ x (n + h) - x n` (`h > 0`) in `UnitAddTorus d` is
asymptotically equidistributed for Haar probability, then `x` is asymptotically equidistributed
for Haar probability (`TauCeti.vanDerCorput_difference`).

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1 (Corollary 1.1.7).
-/

public section

open MeasureTheory

namespace TauCeti

/-- **Van der Corput's difference theorem on `UnitAddTorus d`**: if every positive-lag difference
sequence `n ↦ x (n + h) - x n` (`h > 0`) is equidistributed for Haar probability, then `x` is
equidistributed for Haar probability. -/
theorem vanDerCorput_difference {d : Type*} [Fintype d] {x : ℕ → UnitAddTorus d}
    (hx : ∀ h : ℕ, 0 < h → AsympEquidistributed (fun n ↦ x (n + h) - x n)
      (volume : Measure (UnitAddTorus d)).toProbabilityMeasure) :
    AsympEquidistributed x (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
  rw [weyl_criterion]; intro k hk
  refine tendsto_cesaro_zero_of_forall_correlation ⟨1, fun n ↦ by simp⟩ fun h hh ↦ ?_
  simpa only [← UnitAddTorus.mFourier_apply_sub] using (weyl_criterion.mp (hx h hh)) k hk

end TauCeti
