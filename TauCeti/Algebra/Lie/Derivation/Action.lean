/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic

/-!
# Lie actions by associative derivations

The Leibniz rule for a Lie action on an associative ring is independent of its scalar ring.
Together with a Lie module structure it describes a linear action by derivations, including
on noncommutative coefficient algebras. Inner commutator actions are examples.

Adapted from `Mei/Algebra/Lie/Derivation/Action.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace TauCeti

/-- A Lie action on a non-associative ring acts by derivations of its multiplication. -/
class IsDerivationAction (L A : Type*) [LieRing L] [NonUnitalNonAssocRing A]
    [LieRingModule L A] : Prop where
  /-- The Leibniz rule. -/
  lie_mul : ∀ (x : L) (a b : A), ⁅x, a * b⁆ = a * ⁅x, b⁆ + ⁅x, a⁆ * b

/-- Restricting a derivation action to a Lie subalgebra preserves the Leibniz rule. -/
instance _root_.LieSubalgebra.instIsDerivationAction {R L A : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [NonUnitalNonAssocRing A] [LieRingModule L A]
    [IsDerivationAction L A] (K : LieSubalgebra R L) : IsDerivationAction K A where
  lie_mul x a b := IsDerivationAction.lie_mul (x : L) a b

/-- A derivation of a non-associative ring acts by derivations. -/
instance _root_.LieSubalgebra.instIsDerivationActionDerivation {R A : Type*} [CommRing R]
    [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] :
    IsDerivationAction (derivationLieAlgebra R A) A where
  lie_mul D a b := by
    change (D : Module.End R A) (a * b) = _
    simp [add_comm]

/-- Mathlib's derivations of a commutative algebra act by derivations. -/
instance _root_.Derivation.instIsDerivationAction {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] : IsDerivationAction (Derivation R A A) A where
  lie_mul D a b := by
    simp [smul_eq_mul, mul_comm b (D a)]

namespace IsDerivationAction

variable {R L A : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [LieRingModule L A] [LieModule R L A] [IsDerivationAction L A]

attribute [local instance] LieRing.ofAssociativeRing

/-- A Lie action by derivations is a homomorphism into the derivation Lie algebra. -/
def toDerivationLieAlgebra : L →ₗ⁅R⁆ derivationLieAlgebra R A where
  toLinearMap := {
    toFun x := ⟨LieModule.toEnd R L A x,
      mem_derivationLieAlgebra.2 fun a b => by
        simpa [add_comm] using IsDerivationAction.lie_mul x a b⟩
    map_add' x y := Subtype.ext ((LieModule.toEnd R L A).map_add x y)
    map_smul' r x := Subtype.ext ((LieModule.toEnd R L A).map_smul r x) }
  map_lie' := by
    intro x y
    apply Subtype.ext
    change LieModule.toEnd R L A ⁅x, y⁆ = _
    exact (LieModule.toEnd R L A).map_lie x y

/-- The derivation homomorphism evaluates as the original Lie action. -/
@[simp]
theorem coe_toDerivationLieAlgebra (x : L) :
    (toDerivationLieAlgebra (R := R) (A := A) x : Module.End R A) =
      LieModule.toEnd R L A x := (rfl)

end IsDerivationAction

section Unital

variable (R : Type*) [CommRing R]
  {L A : Type*} [LieRing L] [NonAssocRing A] [LieRingModule L A] [IsDerivationAction L A]

attribute [local instance] LieRing.ofAssociativeRing

/-- A derivation action on a unital non-associative ring kills its unit. -/
theorem IsDerivationAction.lie_one [LieAlgebra R L]
    [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [LieModule R L A]
    (x : L) : ⁅x, (1 : A)⁆ = 0 := by
  rw [← LieModule.toEnd_apply_apply R,
    ← IsDerivationAction.coe_toDerivationLieAlgebra (R := R)]
  exact derivationLieAlgebra.apply_one_eq_zero _

/-- A derivation action kills scalars in a unital associative algebra. -/
@[simp]
theorem IsDerivationAction.lie_algebraMap [LieAlgebra R L]
    {A : Type*} [Ring A] [Algebra R A]
    [LieRingModule L A] [LieModule R L A] [IsDerivationAction L A] (x : L) (r : R) :
    ⁅x, algebraMap R A r⁆ = 0 := by
  rw [← LieModule.toEnd_apply_apply R,
    ← IsDerivationAction.coe_toDerivationLieAlgebra (R := R)]
  exact derivationLieAlgebra.map_algebraMap _ _

end Unital

attribute [local instance] LieRing.ofAssociativeRing

/-- The action of a derivation algebra on a unital non-associative ring kills its unit. -/
theorem LieSubalgebra.lie_one {R A : Type*} [CommRing R]
    [NonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    (D : derivationLieAlgebra R A) : ⁅D, (1 : A)⁆ = 0 :=
  derivationLieAlgebra.apply_one_eq_zero D

/-- The action of a derivation algebra kills scalars in a unital associative algebra. -/
theorem LieSubalgebra.lie_algebraMap {R A : Type*} [CommRing R]
    [Ring A] [Algebra R A] (D : derivationLieAlgebra R A) (r : R) :
    ⁅D, algebraMap R A r⁆ = 0 :=
  derivationLieAlgebra.map_algebraMap D r

/-- The commutator action of an associative ring on itself is by derivations. -/
instance (A : Type*) [Ring A] : IsDerivationAction A A where
  lie_mul x a b := by simp [Ring.lie_def, mul_sub, sub_mul, mul_assoc]

end TauCeti
