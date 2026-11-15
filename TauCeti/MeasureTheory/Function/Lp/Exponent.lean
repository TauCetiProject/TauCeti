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

* `MeasureTheory.Lp.ofExponentLEL`: the continuous `𝕜`-linear inclusion `L^q(ν) → Lᵖ(ν)` for
  `p ≤ q`, for any bounded scalar action of a normed ring `𝕜`.

## Main results

* `MeasureTheory.Lp.coeFn_ofExponentLEL`, `MeasureTheory.Lp.ofExponentLEL_toLp`: the inclusion
  does not change the underlying function.
* `MeasureTheory.Lp.ofExponentLEL_injective`: the inclusion is injective.
* `MeasureTheory.Lp.opNorm_ofExponentLEL_le`, `MeasureTheory.Lp.norm_ofExponentLEL_apply_le`: the
  bound `ν(univ) ^ (1/p - 1/q)` on the operator norm.
* `MeasureTheory.Lp.ofExponentLEL_self`, `MeasureTheory.Lp.ofExponentLEL_ofExponentLEL`: the
  identity at `p = q` and transitivity.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 2.14.
-/

public section

noncomputable section

namespace MeasureTheory.Lp

open scoped ENNReal

variable {α 𝕜 F : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
  [NormedAddCommGroup F] {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

omit [Fact (1 ≤ q)] in
/-- The norm bound of the inclusion `L^q(ν) → Lᵖ(ν)`, on the underlying class. -/
private theorem norm_mk_le (hpq : p ≤ q) (f : Lp F q ν) :
    ‖(⟨f, Lp.antitone hpq f.2⟩ : Lp F p ν)‖ ≤
      (ν Set.univ ^ (1 / p.toReal - 1 / q.toReal)).toReal * ‖f‖ := by
  have hc : ν Set.univ ^ (1 / p.toReal - 1 / q.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (ENNReal.one_div_toReal_sub_one_div_toReal_nonneg
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hpq) (measure_ne_top ν _)
  rw [Lp.norm_def, Lp.coeFn_mk (Lp.antitone hpq f.2), Lp.norm_def, mul_comm,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hc)
    (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq (Lp.aestronglyMeasurable f))

section NormedRing

variable [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F]

variable (𝕜 F) in
/-- The continuous inclusion `L^q(ν) → Lᵖ(ν)` for a finite measure `ν` and `p ≤ q`, with norm at
most `ν(univ) ^ (1/p - 1/q)`; it does not change the underlying almost everywhere equivalence
class. -/
def ofExponentLEL (hpq : p ≤ q) : Lp F q ν →L[𝕜] Lp F p ν :=
  LinearMap.mkContinuous
    { toFun f := ⟨f, Lp.antitone hpq f.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (ν Set.univ ^ (1 / p.toReal - 1 / q.toReal)).toReal (norm_mk_le hpq)

/-- Lowering the exponent keeps the underlying almost everywhere equivalence class. -/
theorem ofExponentLEL_apply (hpq : p ≤ q) (f : Lp F q ν) :
    ofExponentLEL 𝕜 F hpq f = ⟨f, Lp.antitone hpq f.2⟩ :=
  (rfl)

/-- Lowering the exponent does not change the underlying function. -/
@[simp]
theorem coeFn_ofExponentLEL (hpq : p ≤ q) (f : Lp F q ν) : ⇑(ofExponentLEL 𝕜 F hpq f) = ⇑f :=
  (rfl)

/-- Lowering the exponent of the class of a function `f` gives the class of `f`. -/
@[simp]
theorem ofExponentLEL_toLp (hpq : p ≤ q) {f : α → F} (hf : MemLp f q ν) :
    ofExponentLEL 𝕜 F hpq (hf.toLp f) = (hf.mono_exponent hpq).toLp f :=
  (rfl)

/-- Lowering the exponent is injective. -/
theorem ofExponentLEL_injective (hpq : p ≤ q) :
    Function.Injective (ofExponentLEL (ν := ν) 𝕜 F hpq) := fun f g h =>
  Lp.ext (by rw [← coeFn_ofExponentLEL (𝕜 := 𝕜) hpq f, h, coeFn_ofExponentLEL])

/-- Lowering the exponent multiplies the norm by at most `ν(univ) ^ (1/p - 1/q)`. -/
theorem norm_ofExponentLEL_apply_le (hpq : p ≤ q) (f : Lp F q ν) :
    ‖ofExponentLEL 𝕜 F hpq f‖ ≤ (ν Set.univ ^ (1 / p.toReal - 1 / q.toReal)).toReal * ‖f‖ :=
  norm_mk_le hpq f

/-- Lowering the exponent from `p` to itself is the identity. -/
@[simp]
theorem ofExponentLEL_self (f : Lp F p ν) : ofExponentLEL 𝕜 F le_rfl f = f :=
  (rfl)

/-- Exponent inclusions compose transitively. -/
@[simp]
theorem ofExponentLEL_ofExponentLEL (hpq : p ≤ q) (hqr : q ≤ r) (f : Lp F r ν) :
    ofExponentLEL 𝕜 F hpq (ofExponentLEL 𝕜 F hqr f) = ofExponentLEL 𝕜 F (hpq.trans hqr) f :=
  (rfl)

end NormedRing

/-- The operator norm of the inclusion `L^q(ν) → Lᵖ(ν)` is at most `ν(univ) ^ (1/p - 1/q)`. -/
theorem opNorm_ofExponentLEL_le [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] (hpq : p ≤ q) :
    ‖ofExponentLEL (ν := ν) 𝕜 F hpq‖ ≤ (ν Set.univ ^ (1 / p.toReal - 1 / q.toReal)).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

end MeasureTheory.Lp
