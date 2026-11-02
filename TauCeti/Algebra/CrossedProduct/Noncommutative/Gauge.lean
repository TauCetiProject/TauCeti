/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Basic
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Gauge changes of noncommutative crossed products

Suppose two normalized crossed systems have coefficient automorphisms and factors related
by a normalized family of units `b`. Their crossed products are isomorphic by the map
`d[g] ↦ d b(g)[g]` from the new system to the original system. This map fixes coefficients;
its inverse sends `d[g]` to `d b(g)⁻¹[g]`.

The factors and coefficient algebra may be noncommutative. This comparison makes the
crossed product attached to a group-extension section independent of that section up to
algebra isomorphism, while retaining the actual change of basis.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace TauCeti.CrossedSystem.Algebra

universe u v w

variable {k : Type u} {D : Type v} {G : Type w}
  [CommSemiring k] [Semiring D] [_root_.Algebra k D] [Monoid G]
  (c c' : CrossedSystem k D G) (b : G → Dˣ)
  (hb : b 1 = 1)
  (hact : ∀ g d, c'.action g d = (b g : D) * c.action g d * ↑(b g)⁻¹)
  (hfactor : ∀ g h, (c'.factor g h : D) =
    (b g : D) * c.action g (b h) * c.factor g h * ↑(b (g * h))⁻¹)

/-- A normalized gauge relating two crossed systems induces an algebra isomorphism,
from the new system to the old one, sending `[g]` to `b(g)[g]`. -/
noncomputable def gaugeEquiv : Algebra c' ≃ₐ[k] Algebra c := by
  let e := (basis c').equiv ((basis c).unitsSMul b) (Equiv.refl G)
  have he (g : G) (d : D) : e (d • basis c' g) = (d * b g) • basis c g := by
    simp only [map_smul, e, Module.Basis.equiv_apply, Equiv.refl_apply,
      Module.Basis.unitsSMul_apply, Units.smul_def, smul_smul]
  refine AlgEquiv.ofLinearEquiv (e.restrictScalars k) ?_ ?_
  · rw [one_def, LinearEquiv.restrictScalars_apply, ← one_smul D (basis c' 1), he, hb]
    simp
  · intro a a'
    induction a using induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [map_add, add_mul, ha, ha']
    | smul_basis g d =>
      induction a' using induction_on with
      | zero => simp
      | add a a' ha ha' => simp only [map_add, mul_add, ha, ha']
      | smul_basis h f =>
        -- The coefficient-linear map multiplies each coordinate on the right by `b(g)`.
        simp only [LinearEquiv.restrictScalars_apply, smul_basis_mul_smul_basis, he]
        rw [hact, hfactor]
        simp [map_mul, mul_assoc]

/-- The gauge isomorphism multiplies each basis element by its gauge unit. -/
@[simp]
theorem gaugeEquiv_basis (g : G) :
    gaugeEquiv c c' b hb hact hfactor (basis c' g) = (b g : D) • basis c g := by
  simp [gaugeEquiv, Module.Basis.unitsSMul_apply, Units.smul_def]

/-- The gauge isomorphism fixes the coefficient algebra. -/
@[simp]
theorem gaugeEquiv_inc (d : D) :
    gaugeEquiv c c' b hb hact hfactor (inc c' d) = inc c d := by
  simp only [inc_apply, gaugeEquiv, AlgEquiv.ofLinearEquiv_apply,
    LinearEquiv.restrictScalars_apply, map_smul, Module.Basis.equiv_apply,
    Equiv.refl_apply, Module.Basis.unitsSMul_apply, hb, one_smul]

/-- The inverse gauge isomorphism fixes the coefficient algebra. -/
@[simp]
theorem gaugeEquiv_symm_inc (d : D) :
    (gaugeEquiv c c' b hb hact hfactor).symm (inc c d) = inc c' d := by
  apply (gaugeEquiv c c' b hb hact hfactor).injective
  simp

/-- The inverse gauge isomorphism multiplies each basis element by the inverse gauge unit. -/
@[simp]
theorem gaugeEquiv_symm_basis (g : G) :
    (gaugeEquiv c c' b hb hact hfactor).symm (basis c g) =
      (↑(b g)⁻¹ : D) • basis c' g := by
  apply (gaugeEquiv c c' b hb hact hfactor).injective
  rw [smul_def, map_mul, gaugeEquiv_inc, gaugeEquiv_basis, ← smul_def, smul_smul]
  simp

end TauCeti.CrossedSystem.Algebra
