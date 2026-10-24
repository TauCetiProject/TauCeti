/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
public import TauCeti.Topology.Circle.AddCircle

/-!
# Loops as maps out of the circle

A loop `γ : Path x x` closes up, so it factors through the quotient `[0, 1] → S¹`,
`t ↦ exp (2πit)`, which identifies the two endpoints. The factorization is the map
`Path.toCircle γ : C(Circle, X)`: it sends `exp (2πit)` to `γ t`, and the point `1` to `x`.

Maps out of a wedge of circles are assembled from maps out of the circles, so this is how loops
in a space give maps out of a wedge of circles.

In the other direction, the `(p, q)` curve `t ↦ (exp (2πipt), exp (2πiqt))` is the standard loop
on the torus `S¹ × S¹` winding `p` times around the first circle and `q` times around the second.

## Main definitions

* `Path.toCircle`: a loop, read as a map from the unit circle.
* `TauCeti.torusCurve p q`: the `(p, q)` curve on `S¹ × S¹`, a loop at `(1, 1)`.

## Main results

* `Path.toCircle_exp`: the point `exp (2πit)` goes to `γ t`.
* `Path.toCircle_one`: the point `1` goes to the base point.
-/

public section

noncomputable section

open unitInterval

namespace Path

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- A loop `γ` at `x`, read as a map from the unit circle: `exp (2πit)` goes to `γ t`. It is
`γ` extended to `ℝ` and descended to `AddCircle 1`, which is identified with the circle by
`AddCircle.homeomorphCircle`. -/
def toCircle (γ : Path x x) : C(Circle, X) :=
  ⟨AddCircle.liftIco 1 0 γ.extend ∘ (AddCircle.homeomorphCircle one_ne_zero).symm,
    (AddCircle.liftIco_zero_continuous (by simp) γ.continuous_extend.continuousOn).comp
      (AddCircle.homeomorphCircle one_ne_zero).symm.continuous⟩

/-- The point `exp (2πit)` of the circle goes to `γ t`. -/
theorem toCircle_exp (γ : Path x x) (t : I) :
    γ.toCircle (Circle.exp (2 * Real.pi * t)) = γ t := by
  have h : (AddCircle.homeomorphCircle one_ne_zero).symm (Circle.exp (2 * Real.pi * t)) =
      ((t : ℝ) : AddCircle (1 : ℝ)) := by
    rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_apply_mk, div_one]
  rw [toCircle, ContinuousMap.coe_mk, Function.comp_apply, h]
  rcases eq_or_lt_of_le t.2.2 with ht | ht
  · have ht' : t = 1 := Subtype.ext ht
    rw [ht, AddCircle.coe_period, ← AddCircle.coe_zero (p := (1 : ℝ)),
      AddCircle.liftIco_zero_coe_apply ⟨le_rfl, zero_lt_one⟩, γ.extend_zero, ht', γ.target]
  · rw [AddCircle.liftIco_zero_coe_apply ⟨t.2.1, ht⟩, γ.extend_extends']

/-- The point `1` of the circle goes to the base point of the loop. -/
@[simp]
theorem toCircle_one (γ : Path x x) : γ.toCircle 1 = x := by
  simpa using γ.toCircle_exp 0

end Path

namespace TauCeti

/-- The `(p, q)` curve `t ↦ (exp (2πipt), exp (2πiqt))` on the torus `S¹ × S¹`, a loop at
`(1, 1)` winding `p` times around the first circle and `q` times around the second. -/
def torusCurve (p q : ℤ) : Path ((1 : Circle), (1 : Circle)) (1, 1) where
  toFun t := (Circle.exp (2 * Real.pi * (p * t)), Circle.exp (2 * Real.pi * (q * t)))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    simp only [Set.Icc.coe_one, mul_one]
    exact Prod.ext (Circle.exp_two_pi_mul_int p) (Circle.exp_two_pi_mul_int q)

@[simp]
theorem torusCurve_apply (p q : ℤ) (t : unitInterval) :
    torusCurve p q t = (Circle.exp (2 * Real.pi * (p * t)), Circle.exp (2 * Real.pi * (q * t))) :=
  (rfl)

end TauCeti
