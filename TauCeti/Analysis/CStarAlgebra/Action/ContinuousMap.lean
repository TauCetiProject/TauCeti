/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Complex.Circle

/-!
# Translation actions on algebras of continuous functions

A continuous action of a topological group `G` on a compact space `X` induces a point-norm
continuous action `ofMulAction G X` of `G` on the commutative C⋆-algebra `C(X, ℂ)` by
translation, `(g • f)(x) = f (g⁻¹ • x)`. Each automorphism is composition with the
homeomorphism `x ↦ g⁻¹ • x`, and continuity of the orbit of `f` is continuity of the curried
map `(g, x) ↦ f (g⁻¹ • x)`, since the norm topology on `C(X, ℂ)` is the compact-open topology.

The *rotation action* `rotation` of the real line on `C(S¹, ℂ)` is the translation action of
the circle group pulled back along `t ↦ exp (i t)`, `Circle.expContinuousMonoidHom`, so that
`rotation t f z = f (exp (-i t) z)`. It is the basic example of a C⋆-dynamical system on a
commutative algebra. The coordinate function `Circle.coordinate`, `u(z) = z`, is a unitary of
`C(S¹, ℂ)` and an eigenvector of the rotation action, `α_t(u) = exp (-i t) u`,
`rotation_coordinate`.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for translation actions on
`C₀(X)`.
-/

public section

noncomputable section

namespace TauCeti.CStarAction

variable (G X : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [CompactSpace X] [MulAction G X] [ContinuousSMul G X]

/-- The translation action `(g • f)(x) = f (g⁻¹ • x)` on `C(X, ℂ)` induced by a continuous
action of a topological group on a compact space. -/
def ofMulAction : CStarAction G C(X, ℂ) where
  toMonoidHom :=
    { toFun g := (Homeomorph.smul g⁻¹).compStarAlgEquiv' ℂ ℂ
      map_one' := by
        ext
        simp
      map_mul' g h := by
        ext
        simp [mul_smul] }
  continuous_orbit f :=
    (ContinuousMap.curry (f.comp ⟨fun p : G × X => p.1⁻¹ • p.2, by fun_prop⟩)).continuous

variable {G X}

@[simp]
theorem ofMulAction_apply_apply (g : G) (f : C(X, ℂ)) (x : X) :
    ofMulAction G X g f x = f (g⁻¹ • x) :=
  (rfl)

end TauCeti.CStarAction

namespace Circle

/-- The map `t ↦ exp (i t)` from the real line to the circle, as a continuous homomorphism
from `Multiplicative ℝ`. -/
def expContinuousMonoidHom : ContinuousMonoidHom (Multiplicative ℝ) Circle where
  toFun t := Circle.exp t.toAdd
  map_one' := Circle.exp_zero
  map_mul' _ _ := Circle.exp_add _ _
  continuous_toFun := Circle.exp.continuous.comp continuous_toAdd

@[simp]
theorem expContinuousMonoidHom_apply (t : Multiplicative ℝ) :
    expContinuousMonoidHom t = Circle.exp t.toAdd :=
  (rfl)

/-- The coordinate function `z ↦ z` on the circle. -/
def coordinate : C(Circle, ℂ) :=
  ⟨(↑), by fun_prop⟩

@[simp]
theorem coordinate_apply (z : Circle) : coordinate z = z :=
  (rfl)

theorem star_coordinate_mul : star coordinate * coordinate = 1 := by
  ext z
  simp [Complex.conj_mul']

theorem coordinate_mul_star : coordinate * star coordinate = 1 := by
  rw [mul_comm, star_coordinate_mul]

end Circle

namespace TauCeti.CStarAction

open Complex

/-- The rotation action of the real line on `C(S¹, ℂ)`: the real number `t` acts by
`f ↦ (z ↦ f (exp (i t)⁻¹ z))`. -/
def rotation : CStarAction (Multiplicative ℝ) C(Circle, ℂ) :=
  (ofMulAction Circle Circle).comp Circle.expContinuousMonoidHom

@[simp]
theorem rotation_apply_apply (t : Multiplicative ℝ) (f : C(Circle, ℂ)) (z : Circle) :
    rotation t f z = f ((Circle.exp t.toAdd)⁻¹ * z) := by
  simp [rotation]

/-- The coordinate function is an eigenvector of the rotation action. -/
theorem rotation_coordinate (t : ℝ) :
    rotation (Multiplicative.ofAdd t) Circle.coordinate = exp (-I * t) • Circle.coordinate := by
  ext z
  simp [Circle.coe_exp, ← Complex.exp_neg, mul_comm]

end TauCeti.CStarAction
