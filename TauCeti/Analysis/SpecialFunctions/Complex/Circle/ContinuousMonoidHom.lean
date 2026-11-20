/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuous homomorphisms out of the circle through `Circle.exp`

Mathlib's exponential `Circle.exp t = e^{it}` is a surjective continuous homomorphism from the
real line onto the circle with kernel `2πℤ`. So a continuous homomorphism `f : ℝ → G` with
`f (2π) = 1` descends to a continuous homomorphism `ψ : Circle → G` with
`ψ (Circle.exp t) = f t`. This file packages that descent.

## Main declarations

* `ContinuousMonoidHom.circleLift`: the continuous homomorphism `Circle →ₜ* G` induced by a
  continuous homomorphism `Multiplicative ℝ →ₜ* G` that is trivial at `2π`.
* `ContinuousMonoidHom.circleLift_circleExp`: its value at `Circle.exp t` is `f t`.
-/

public section

noncomputable section

open Real

namespace ContinuousMonoidHom

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- A continuous homomorphism `f` from the real line that is trivial at `2π` is `2π`-periodic. -/
theorem periodic_two_pi_of_apply_eq_one (f : Multiplicative ℝ →ₜ* G)
    (hf : f (.ofAdd (2 * π)) = 1) :
    Function.Periodic (fun t : ℝ ↦ f (.ofAdd t)) (2 * π) := fun t ↦ by
  beta_reduce
  rw [ofAdd_add, map_mul, hf, mul_one]

/-- **Descent through `Circle.exp`.** A continuous homomorphism `f : ℝ → G` with `f (2π) = 1`
induces the continuous homomorphism `Circle.exp t ↦ f t` from the circle
(`ContinuousMonoidHom.circleLift_circleExp`). -/
def circleLift (f : Multiplicative ℝ →ₜ* G) (hf : f (.ofAdd (2 * π)) = 1) : Circle →ₜ* G where
  toFun z := (periodic_two_pi_of_apply_eq_one f hf).lift (AddCircle.homeomorphCircle'.symm z)
  map_one' := by
    rw [← Circle.exp_zero, ← AddCircle.homeomorphCircle'_apply_mk,
      AddCircle.homeomorphCircle'.symm_apply_apply, Function.Periodic.lift_coe, ofAdd_zero,
      map_one]
  map_mul' z w := by
    obtain ⟨s, rfl⟩ := Circle.exp_surjective z
    obtain ⟨t, rfl⟩ := Circle.exp_surjective w
    rw [← Circle.exp_add, ← AddCircle.homeomorphCircle'_apply_mk,
      ← AddCircle.homeomorphCircle'_apply_mk, ← AddCircle.homeomorphCircle'_apply_mk]
    simp only [Homeomorph.symm_apply_apply, Function.Periodic.lift_coe]
    rw [ofAdd_add, map_mul]
  continuous_toFun := by
    have hlift : Continuous (periodic_two_pi_of_apply_eq_one f hf).lift :=
      continuous_coinduced_dom.2 (f.continuous.comp continuous_ofAdd)
    exact hlift.comp AddCircle.homeomorphCircle'.symm.continuous

/-- The descent of `f` through `Circle.exp` sends `Circle.exp t` to `f t`. -/
@[simp]
theorem circleLift_circleExp (f : Multiplicative ℝ →ₜ* G) (hf : f (.ofAdd (2 * π)) = 1)
    (t : ℝ) : circleLift f hf (Circle.exp t) = f (.ofAdd t) := by
  change (periodic_two_pi_of_apply_eq_one f hf).lift (AddCircle.homeomorphCircle'.symm _) = _
  rw [← AddCircle.homeomorphCircle'_apply_mk, AddCircle.homeomorphCircle'.symm_apply_apply,
    Function.Periodic.lift_coe]

end ContinuousMonoidHom
