/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.AddCircleAdd
public import Mathlib.NumberTheory.Real.Irrational
import TauCeti.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Ergodicity of the time-`t` maps of the circle flow

The real line acts on the circle `AddCircle p = ℝ / pℤ`, `p > 0`, by Mathlib's quotient action
`t +ᵥ x = ↑t + x`; this is the linear flow of speed `1`. Its time-`t` map is ergodic for the Haar
measure exactly when `t / p` is irrational (`AddCircle.ergodic_vadd_iff`), by Mathlib's
characterization of ergodic rotations (`AddCircle.ergodic_add_left`) and the irrationality
criterion for infinite order (`AddCircle.addOrderOf_coe_eq_zero_iff`). In particular the time-`p`
map is the identity, which is not ergodic (`AddCircle.not_ergodic_vadd_self`), while on the unit
circle every time-`t` map with `t` irrational is ergodic.

## Main results

* `AddCircle.ergodic_vadd_iff`: the time-`t` map of the circle flow is ergodic exactly when `t / p`
  is irrational.
* `AddCircle.not_ergodic_vadd_self`: the time-`p` map is not ergodic.
-/

public section

open MeasureTheory

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

/-- **Ergodic time-`t` maps of the circle flow.** The time-`t` map `x ↦ t +ᵥ x` of the translation
action of `ℝ` on `AddCircle p` is ergodic for the Haar measure exactly when `t / p` is
irrational. -/
theorem ergodic_vadd_iff {t : ℝ} :
    Ergodic (fun x : AddCircle p ↦ t +ᵥ x) ↔ Irrational (t / p) := by
  have h : (fun x : AddCircle p ↦ t +ᵥ x) = ((t : AddCircle p) + ·) := by
    funext x
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp
  rw [h, ergodic_add_left, addOrderOf_coe_eq_zero_iff]

/-- **Check.** The time-`p` map of the circle flow is the identity, which is not ergodic. -/
theorem not_ergodic_vadd_self : ¬Ergodic (fun x : AddCircle p ↦ p +ᵥ x) := by
  rw [ergodic_vadd_iff, div_self (Fact.out : 0 < p).ne']
  exact not_irrational_one

end AddCircle
