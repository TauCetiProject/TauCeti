/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import TauCeti.MeasureTheory.Function.Lp.Multiplication.Eigenspace

/-!
# Coordinate multiplication on `L²([0, 1])`

Defines the essentially bounded coordinate symbol `TauCeti.unitInterval.coordLp` (`t ↦ (t : ℂ)`)
on the unit interval with Lebesgue measure and proves that multiplication by `coordLp` on
`Lp E 2 (volume : Measure unitInterval)` has no eigenvalues.

## Main declarations

* `TauCeti.unitInterval.coordLp`: the coordinate symbol `t ↦ (t : ℂ)` in `Lp ℂ ∞ volume`.
* `TauCeti.unitInterval.coeFn_coordLp`: `coordLp` agrees with `t ↦ (t : ℂ)` almost everywhere.
* `TauCeti.unitInterval.star_coordLp`: `coordLp` is self-adjoint.
* `TauCeti.unitInterval.not_hasEigenvalue_multiplicationOperator_coordLp`: multiplication by
  `coordLp` on `Lp E 2 volume` has no eigenvalues.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal unitInterval

namespace TauCeti.unitInterval

/-- The bounded coordinate symbol `t ↦ (t : ℂ)` in `Lp ℂ ∞ (volume : Measure unitInterval)`. -/
def coordLp : Lp ℂ ∞ (volume : Measure I) :=
  ContinuousMap.toLp ∞ (volume : Measure I) ℂ
    ⟨fun t : I ↦ ((t : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtypeVal⟩

/-- Almost everywhere on `unitInterval`, `coordLp` evaluates to `t ↦ (t : ℂ)`. -/
theorem coeFn_coordLp :
    ⇑coordLp =ᵐ[volume] fun t : I ↦ ((t : ℝ) : ℂ) := by
  rw [coordLp]
  filter_upwards [ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (volume : Measure I)
    ⟨fun t : I ↦ ((t : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtypeVal⟩] with t ht
  rw [ht, ContinuousMap.coe_mk]

/-- The real-valued coordinate symbol `coordLp` is self-adjoint. -/
@[simp]
theorem star_coordLp : star coordLp = coordLp :=
  Lp.star_eq_self_of_ae_eq_ofReal coeFn_coordLp

/-- Multiplication by the coordinate function `t ↦ (t : ℂ)` on `Lp E 2 (volume : Measure I)` has
no eigenvalues. -/
theorem not_hasEigenvalue_multiplicationOperator_coordLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) :
    ¬ Module.End.HasEigenvalue
      (Lp.multiplicationOperator (E := E) (p := 2) coordLp).toLinearMap c := by
  have hnull : ∀ᵐ t : I ∂volume, ((t : ℝ) : ℂ) ≠ c := by
    rw [ae_iff]
    exact Set.Subsingleton.measure_zero
      (fun _ hx _ hy ↦ Subtype.ext (Complex.ofReal_injective
        ((not_not.mp hx).trans (not_not.mp hy).symm))) volume
  refine Lp.not_hasEigenvalue_multiplicationOperator coordLp ?_
  filter_upwards [coeFn_coordLp, hnull] with t ht hne
  rwa [ht]

end TauCeti.unitInterval

end
