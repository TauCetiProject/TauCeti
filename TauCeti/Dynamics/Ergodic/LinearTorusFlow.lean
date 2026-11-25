/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Dynamics.Flow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Linear flows on the unit torus

For a velocity `v : ι → ℝ`, the linear flow on the unit torus `UnitAddTorus ι = (ℝ / ℤ)^ι` moves
a point `x` at time `t` to `x + t • v`, that is `i ↦ x i + [t * v i]`
(`TauCeti.linearTorusFlow v`, a continuous flow in the sense of Mathlib's `Flow`). Each time-`t`
map is a translation of the compact group `UnitAddTorus ι`, so it preserves the volume (the Haar
probability) (`TauCeti.measurePreserving_linearTorusFlow`), and the flow is jointly measurable
in time and space (`TauCeti.measurable_uncurry_linearTorusFlow`).

The flow is a `Flow` rather than an instance of `AddAction ℝ (UnitAddTorus ι)`: the torus already
carries Mathlib's translation action of `ℝ` on each circle factor, which is the linear flow of
velocity `fun _ ↦ 1` (`TauCeti.linearTorusFlow_one_apply`), and a second instance depending on
`v` would conflict with it.

## Main definitions

* `TauCeti.linearTorusFlow v`: the linear flow `(t, x) ↦ x + t • v` on `UnitAddTorus ι`.

## Main results

* `TauCeti.measurePreserving_linearTorusFlow`: each time-`t` map preserves the volume.
* `TauCeti.measurable_uncurry_linearTorusFlow`: the flow is jointly measurable.
-/

public section

open MeasureTheory

namespace TauCeti

variable {ι : Type*}

/-- The linear flow on the unit torus with velocity `v : ι → ℝ`: at time `t` it moves `x` to
`x + t • v`, that is `i ↦ x i + [t * v i]`. -/
noncomputable def linearTorusFlow (v : ι → ℝ) : Flow ℝ (UnitAddTorus ι) where
  toFun t x := x + fun i ↦ ((t * v i : ℝ) : UnitAddCircle)
  cont' := by fun_prop
  map_add' t₁ t₂ x := by
    ext i
    simp only [Pi.add_apply, add_mul, AddCircle.coe_add]
    abel
  map_zero' x := by
    ext i
    simp

@[simp]
theorem linearTorusFlow_apply (v : ι → ℝ) (t : ℝ) (x : UnitAddTorus ι) (i : ι) :
    linearTorusFlow v t x i = x i + ((t * v i : ℝ) : UnitAddCircle) :=
  (rfl)

/-- The time-`t` map of the linear flow is translation by `i ↦ [t * v i]`. -/
theorem linearTorusFlow_eq_add (v : ι → ℝ) (t : ℝ) (x : UnitAddTorus ι) :
    linearTorusFlow v t x = x + fun i ↦ ((t * v i : ℝ) : UnitAddCircle) :=
  (rfl)

/-- The linear flow of velocity `fun _ ↦ 1` is Mathlib's translation action of `ℝ` on each
circle factor. -/
theorem linearTorusFlow_one_apply (t : ℝ) (x : UnitAddTorus ι) :
    linearTorusFlow 1 t x = t +ᵥ x := by
  ext i
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (x i)
  simp [← ha, add_comm]

/-- The linear flow on the unit torus is jointly measurable in time and space. -/
theorem measurable_uncurry_linearTorusFlow (v : ι → ℝ) :
    Measurable fun p : ℝ × UnitAddTorus ι ↦ linearTorusFlow v p.1 p.2 :=
  measurable_pi_iff.2 fun i ↦ by
    simp only [linearTorusFlow_apply]
    fun_prop

variable [Fintype ι]

/-- **Linear flows preserve volume.** Each time-`t` map of a linear flow on the unit torus is a
translation, so it preserves the volume. -/
theorem measurePreserving_linearTorusFlow (v : ι → ℝ) (t : ℝ) :
    MeasurePreserving (linearTorusFlow v t) volume volume := by
  simpa only [funext (linearTorusFlow_eq_add v t)] using
    measurePreserving_add_right volume (fun i ↦ ((t * v i : ℝ) : UnitAddCircle))

end TauCeti
