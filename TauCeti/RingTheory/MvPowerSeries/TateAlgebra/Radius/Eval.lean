/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Radius.Basic

/-!
# Evaluation and radius restriction

Evaluation commutes with restriction to smaller polyradii at arguments bounded by the smaller
polyradii.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

/-- Evaluating after restriction to smaller radii gives the original evaluation. -/
theorem restrictedEval₂_restrictedRadiusHom {k : ℕ} {R S : Type*}
    [NormedCommRing R] [IsUltrametricDist R] [NormedCommRing S] [IsUltrametricDist S]
    [CompleteSpace S] {r s : Fin k → ℝ} (hr : ∀ i, 0 ≤ r i) (hrs : r ≤ s)
    (φ : R →+* S) (a : Fin k → S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (ha : ∀ i, ‖a i‖ ≤ r i)
    (f : IsRestricted.subring (R := R) s) :
    restrictedEval₂ φ a hφ ha (restrictedRadiusHom hr hrs f) =
      restrictedEval₂ φ a hφ (fun i ↦ (ha i).trans (hrs i)) f := by
  rw [restrictedEval₂_apply, restrictedEval₂_apply, coe_restrictedRadiusHom]

end TauCeti.MvPowerSeries
