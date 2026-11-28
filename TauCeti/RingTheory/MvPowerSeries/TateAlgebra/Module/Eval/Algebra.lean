/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Eval

/-!
# Comparing algebra-valued and module-valued evaluation

Evaluation of a restricted series at the image of a scalar-field point agrees with
module-valued evaluation of its coefficient family.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {K R : Type*} [NormedField K] [NormedCommRing R] [NormedAlgebra K R]
  [IsUltrametricDist R] [CompleteSpace R] {k : ℕ} {r : Fin k → ℝ}

/-- Evaluation at a point over the scalar field is module-valued evaluation of the coefficient
family. -/
theorem restrictedEval₂_algebraMap_arg_eq_familyEval
    (f : MvPowerSeries.IsRestricted.subring (R := R) r) (z : Fin k → K)
    (hz : ∀ i, ‖algebraMap K R (z i)‖ ≤ r i) :
    MvPowerSeries.restrictedEval₂ (RingHom.id R) (fun i ↦ algebraMap K R (z i))
      (fun _ ↦ le_rfl) hz f =
      familyEval z (fun d ↦ MvPowerSeries.coeff d (f : MvPowerSeries (Fin k) R)) := by
  rw [familyEval_def, ← (MvPowerSeries.hasSum_restrictedEval₂ _ _ _ hz f).tsum_eq]
  congr 1
  funext d
  rw [TauCeti.Huber.weightedEvalTerm_def, RingHom.id_apply, Algebra.smul_def, mul_comm]
  simp [Finsupp.prod_fintype d (z · ^ ·) (fun _ ↦ pow_zero _)]


end TauCeti.MvPowerSeries
