/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Descent
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Continuous homomorphisms out of the circle through `Circle.exp`

Mathlib's exponential `Circle.exp t = e^{it}` is a surjective continuous homomorphism from the
real line onto the circle with kernel `2πℤ`, and a quotient map. So a continuous homomorphism
`f : ℝ → G` with `f (2π) = 1` descends to a continuous homomorphism `ψ : Circle → G` with
`ψ (Circle.exp t) = f t`. This file packages that descent as an instance of
`ContinuousMonoidHom.liftOfIsQuotientMap` for `Circle.expContinuousMonoidHom`.

## Main declarations

* `Circle.isQuotientMap_expContinuousMonoidHom`: `Circle.exp`, packaged as a continuous
  homomorphism, is a quotient map.
* `ContinuousMonoidHom.ext_circleExp`: continuous homomorphisms out of the circle agreeing on
  every `Circle.exp t` are equal.
* `ContinuousMonoidHom.circleLift`: the continuous homomorphism `Circle →ₜ* G` induced by a
  continuous homomorphism `Multiplicative ℝ →ₜ* G` that is trivial at `2π`.
* `ContinuousMonoidHom.circleLift_circleExp`: its value at `Circle.exp t` is `f t`.
* `ContinuousMonoidHom.circleLift_unique`: it is the only such continuous homomorphism.
-/

public section

noncomputable section

open Real

namespace Circle

/-- `Circle.expContinuousMonoidHom` is a quotient map from the real line onto the circle. -/
theorem isQuotientMap_expContinuousMonoidHom :
    Topology.IsQuotientMap expContinuousMonoidHom := by
  rw [show ⇑expContinuousMonoidHom = exp ∘ Multiplicative.toAdd from
    funext expContinuousMonoidHom_apply]
  exact isAddQuotientCoveringMap_exp.toIsQuotientMap.comp
    (isOpenMap_toAdd.isQuotientMap continuous_toAdd Multiplicative.toAdd.surjective)

end Circle

namespace ContinuousMonoidHom

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- Continuous homomorphisms out of the circle are determined by their values on `Circle.exp t`. -/
theorem ext_circleExp {ψ φ : Circle →ₜ* G} (h : ∀ t : ℝ, ψ (Circle.exp t) = φ (Circle.exp t)) :
    ψ = φ :=
  ext fun z ↦ by
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    exact h t

/-- **Descent through `Circle.exp`.** A continuous homomorphism `f : ℝ → G` with `f (2π) = 1`
induces the continuous homomorphism `Circle.exp t ↦ f t` from the circle
(`ContinuousMonoidHom.circleLift_circleExp`). -/
def circleLift (f : Multiplicative ℝ →ₜ* G) (hf : f (.ofAdd (2 * π)) = 1) : Circle →ₜ* G :=
  liftOfIsQuotientMap Circle.expContinuousMonoidHom Circle.isQuotientMap_expContinuousMonoidHom f
    fun t ht ↦ by
      rw [MonoidHom.mem_ker, MonoidHom.coe_ofClass, Circle.expContinuousMonoidHom_apply] at ht
      rw [MonoidHom.mem_ker, MonoidHom.coe_ofClass]
      obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 ht
      have hper : Function.Periodic (fun s : ℝ ↦ f (.ofAdd s)) (2 * π) := fun s ↦ by
        beta_reduce
        rw [ofAdd_add, map_mul, hf, mul_one]
      rw [← ofAdd_toAdd t, hn, hper.int_mul_eq, ofAdd_zero, map_one]

/-- The descent of `f` through `Circle.exp` sends `Circle.exp t` to `f t`. -/
@[simp]
theorem circleLift_circleExp (f : Multiplicative ℝ →ₜ* G) (hf : f (.ofAdd (2 * π)) = 1)
    (t : ℝ) : circleLift f hf (Circle.exp t) = f (.ofAdd t) := by
  rw [← toAdd_ofAdd t, ← Circle.expContinuousMonoidHom_apply, circleLift,
    liftOfIsQuotientMap_comp_apply, toAdd_ofAdd]

/-- **Uniqueness of the descent through `Circle.exp`.** A continuous homomorphism `ψ` out of the
circle with `ψ (Circle.exp t) = f t` for every `t` is `circleLift f hf`. -/
theorem circleLift_unique (f : Multiplicative ℝ →ₜ* G) (hf : f (.ofAdd (2 * π)) = 1)
    {ψ : Circle →ₜ* G} (h : ∀ t : ℝ, ψ (Circle.exp t) = f (.ofAdd t)) :
    ψ = circleLift f hf :=
  ext_circleExp fun t ↦ by rw [h, circleLift_circleExp]

end ContinuousMonoidHom
