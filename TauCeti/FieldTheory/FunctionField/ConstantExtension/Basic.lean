/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.GeometricDegree
public import TauCeti.FieldTheory.FunctionField.Basic

/-!
# Finite extensions of the constant field

When a finite extension of constants is adjoined to an algebraic function field,
the compositum is again an algebraic function field over the enlarged constant field.  This
gives the function-field structure needed to discuss its places, divisors, and genus.

Separability and exactness of the original constant field are not needed here.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- A compositum with finite constants is finite over the original field. The ambient field
`F'` is assumed to be precisely the compositum of `F` and `k'`. -/
theorem finiteDimensional_of_constantCompositum_eq_top [FiniteDimensional k k']
    (h : constantCompositum F k' F' = ⊤) : FiniteDimensional F F' := by
  let : Algebra.EssFiniteType k k' := inferInstance
  obtain ⟨S, hS⟩ := IntermediateField.fg_top k k'
  have htop : IntermediateField.adjoin F ((algebraMap k' F') '' (S : Set k')) = ⊤ := by
    rw [← constantCompositum_eq_adjoin_of_adjoin_eq_top (F := F) (k' := k')
      (F' := F') S hS]
    exact h
  have hfinite : Finite ((algebraMap k' F') '' (S : Set k')) :=
    S.finite_toSet.image _
  let : Finite ((algebraMap k' F') '' (S : Set k')) := hfinite
  have hi : ∀ x ∈ (algebraMap k' F') '' (S : Set k'), IsIntegral F x := by
    rintro x ⟨c, _, rfl⟩
    exact (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  have := IntermediateField.finiteDimensional_adjoin hi
  rw [htop] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- Adjoining a finite extension of constants to a function field produces a
function field over the enlarged constant field.  The statement uses an ambient compositum
equation so that it applies to any compatible field realization. -/
theorem IsFunctionField.of_constantCompositum_eq_top [FiniteDimensional k k']
    (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) : IsFunctionField k' F' := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (F := F) (k' := k')
    (F' := F') h
  let : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  exact (hF.finite_extension (E := F')).of_isAlgebraic

end TauCeti
