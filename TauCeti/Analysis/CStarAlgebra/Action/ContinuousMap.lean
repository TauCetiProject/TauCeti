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
the circle group pulled back along `t ↦ exp (i t)`, so that
`rotation t f z = f (exp (-i t) z)`. It is the basic example of a C⋆-dynamical system on a
commutative algebra.

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

/-- The rotation action of the real line on `C(S¹, ℂ)`: the real number `t` acts by
`f ↦ (z ↦ f (exp (i t)⁻¹ z))`. -/
def rotation : CStarAction (Multiplicative ℝ) C(Circle, ℂ) :=
  (ofMulAction Circle Circle).comp
    { toFun t := Circle.exp t.toAdd
      map_one' := Circle.exp_zero
      map_mul' _ _ := Circle.exp_add _ _
      continuous_toFun := Circle.exp.continuous.comp continuous_toAdd }

@[simp]
theorem rotation_apply_apply (t : Multiplicative ℝ) (f : C(Circle, ℂ)) (z : Circle) :
    rotation t f z = f ((Circle.exp t.toAdd)⁻¹ * z) := by
  simp [rotation]
  -- evaluating the anonymous continuous homomorphism `t ↦ exp (i t)` is definitional
  rfl

end TauCeti.CStarAction
