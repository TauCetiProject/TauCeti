/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Data.ENNReal.Inv

/-!
# Lowering the exponent of `Lᵖ` functions on a finite measure space

On a finite measure space `ν`, `L^q(ν) ⊆ Lᵖ(ν)` for `p ≤ q` (Mathlib's
`MeasureTheory.Lp.antitone`), with `‖f‖_p ≤ ν(univ) ^ (1/p - 1/q) ‖f‖_q`
(`MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ`). This file bundles the inclusion as a
continuous linear map, which does not change the underlying almost everywhere equivalence class.

## Main definitions

* `TauCeti.Lp.ofExponentLEL`: the continuous inclusion `L^q(ν) → Lᵖ(ν)` for `p ≤ q`.

## Main results

* `TauCeti.Lp.coeFn_ofExponentLEL`: the inclusion does not change the underlying function.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 2.14.
-/

public section

noncomputable section

namespace TauCeti.Lp

open MeasureTheory
open scoped ENNReal

variable {α F : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The continuous inclusion `L^q(ν) → Lᵖ(ν)` for a finite measure `ν` and `p ≤ q`, with norm at
most `ν(univ) ^ (1/p - 1/q)`; it does not change the underlying almost everywhere equivalence
class. -/
def ofExponentLEL (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (hpq : p ≤ q) :
    Lp F q ν →L[ℝ] Lp F p ν :=
  LinearMap.mkContinuous
    { toFun f := ⟨f, MeasureTheory.Lp.antitone hpq f.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (ν Set.univ ^ (1 / p.toReal - 1 / q.toReal)).toReal fun f => by
      have hc : ν Set.univ ^ (1 / p.toReal - 1 / q.toReal) ≠ ∞ :=
        ENNReal.rpow_ne_top_of_nonneg (ENNReal.one_div_toReal_sub_one_div_toReal_nonneg
          (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hpq) (measure_ne_top ν _)
      rw [LinearMap.coe_mk, AddHom.coe_mk, MeasureTheory.Lp.norm_def,
        MeasureTheory.Lp.coeFn_mk (MeasureTheory.Lp.antitone hpq f.2), MeasureTheory.Lp.norm_def,
        mul_comm, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top (MeasureTheory.Lp.eLpNorm_ne_top f) hc)
        (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq (MeasureTheory.Lp.aestronglyMeasurable f))

/-- Lowering the exponent keeps the underlying almost everywhere equivalence class. -/
theorem ofExponentLEL_apply (hpq : p ≤ q) (f : Lp F q ν) :
    ofExponentLEL F hpq f = ⟨f, MeasureTheory.Lp.antitone hpq f.2⟩ :=
  (rfl)

/-- Lowering the exponent does not change the underlying function. -/
@[simp]
theorem coeFn_ofExponentLEL (hpq : p ≤ q) (f : Lp F q ν) : ⇑(ofExponentLEL F hpq f) = ⇑f :=
  (rfl)

end TauCeti.Lp
