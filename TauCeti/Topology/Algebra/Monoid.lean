/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.CompactOpen

/-!
# Continuous maps on a topological magma

Continuous-map constructions that use the multiplication of a topological magma, next to
Mathlib's `ContinuousMap.mulLeft` and `ContinuousMap.mulRight`.

## Main definitions

* `ContinuousMap.compSwapShearMulRight`: the family `x ↦ (y ↦ Ψ y (y * x))` attached to a
  two-variable continuous map `Ψ`, that is, `Ψ` precomposed with the coordinate swap followed by
  the shear `(a, b) ↦ (a, a * b)` of `Homeomorph.shearMulRight`, with
  `ContinuousMap.compSwapShearMulRight_apply_apply` its pointwise formula.
-/

public section

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [Mul X] [ContinuousMul X] [LocallyCompactSpace X]
  {Z : Type*} [TopologicalSpace Z]

/-- The family `x ↦ (y ↦ Ψ y (y * x))` attached to a two-variable continuous map `Ψ`: the
uncurried `Ψ` precomposed with the coordinate swap `(x, y) ↦ (y, x)` followed by the shear
`(a, b) ↦ (a, a * b)` of `Homeomorph.shearMulRight`, curried again. Local compactness makes
evaluation continuous, which is what makes the family jointly continuous. -/
noncomputable def compSwapShearMulRight (Ψ : C(X, C(X, Z))) : C(X, C(X, Z)) :=
  curry ⟨fun p : X × X => Ψ p.2 (p.2 * p.1),
    continuous_eval.comp ((Ψ.continuous.comp continuous_snd).prodMk
      (continuous_snd.mul continuous_fst))⟩

@[simp]
theorem compSwapShearMulRight_apply_apply (Ψ : C(X, C(X, Z))) (x y : X) :
    compSwapShearMulRight Ψ x y = Ψ y (y * x) := (rfl)

end ContinuousMap
