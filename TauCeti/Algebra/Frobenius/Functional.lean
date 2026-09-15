/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Frobenius functionals and the right dual

A linear functional `lambda : A →ₗ[k] k` is called Frobenius here when the multiplication pairing
`(a, b) ↦ lambda (a * b)` is nondegenerate on both sides. This file bundles that condition as
`TauCeti.FrobeniusFunctional` and, for finite-dimensional algebras, proves its standard
characterization by a right-module equivalence from the regular module to its linear dual.

The handedness is explicit. `TauCeti.RightDual k A` is the linear dual `Module.Dual k A` equipped
with the right `A`-action

`(phi * a) b = phi (a * b)`.

For a Frobenius functional `lambda`, the corresponding map sends `a` to the functional
`b ↦ lambda (a * b)`. It is right-linear for precisely this action. Conversely, a right-module
equivalence `e : A ≃ RightDual k A` recovers its functional by evaluating `e 1`; right-linearity
shows these constructions are inverse. The equivalence requires finite-dimensionality only in the
forward direction, where two-sided nondegeneracy upgrades to a perfect pairing.

`TauCeti.SymmetricFrobeniusFunctional` records the additional trace identity
`lambda (a * b) = lambda (b * a)` and identifies it with symmetry of the multiplication pairing.
It is deliberately stronger than an arbitrary Frobenius functional.

## Main definitions

* `TauCeti.RightDual`: the linear dual carrying the right action above.
* `TauCeti.FrobeniusFunctional`: a functional with two-sided nondegenerate multiplication pairing.
* `TauCeti.FrobeniusFunctional.equivRightDualEquiv`: the equivalence between Frobenius
  functionals and right-module equivalences with the right dual.
* `TauCeti.SymmetricFrobeniusFunctional`: a Frobenius functional satisfying the trace identity.

## References

See Curtis--Reiner, *Methods of Representation Theory*, Volume I, Section 9, and Lam,
*Lectures on Modules and Rings*, Section 16.
-/

public section

namespace TauCeti

open Module

universe u v

/-- The linear dual of an algebra, with the right action `(phi * a) b = phi (a * b)`. -/
abbrev RightDual (k : Type u) (A : Type v) [CommSemiring k] [Semiring A] [Algebra k A] :=
  Module.Dual k A

namespace RightDual

variable (k : Type u) (A : Type v) [CommSemiring k] [Semiring A] [Algebra k A]

instance : SMul Aᵐᵒᵖ (RightDual k A) :=
  ⟨fun a phi => phi.comp (LinearMap.mulLeft k a.unop)⟩

@[simp]
theorem smul_apply (a : Aᵐᵒᵖ) (b : A) (phi : RightDual k A) :
    (a • phi) b = phi (a.unop * b) := rfl

@[simp]
theorem op_smul_apply (a b : A) (phi : RightDual k A) :
    (MulOpposite.op a • phi) b = phi (a * b) := by simp

instance : Module Aᵐᵒᵖ (RightDual k A) where
  one_smul phi := by
    ext b
    simp
  mul_smul a b phi := by
    ext c
    simp [mul_assoc]
  smul_zero a := by
    ext b
    simp
  smul_add a phi psi := by
    ext b
    simp
  zero_smul phi := by
    ext b
    simp
  add_smul a b phi := by
    ext c
    simp only [smul_apply, LinearMap.add_apply, MulOpposite.unop_add, add_mul, map_add]

end RightDual

section

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A]

/-- A linear functional whose multiplication pairing is nondegenerate on both sides. -/
@[ext]
structure FrobeniusFunctional where
  /-- The underlying linear functional. -/
  functional : A →ₗ[k] k
  /-- An element killed by the functional against every right multiplier is zero. -/
  left_nondegenerate : ∀ a : A, (∀ b : A, functional (a * b) = 0) → a = 0
  /-- An element killed by the functional against every left multiplier is zero. -/
  right_nondegenerate : ∀ b : A, (∀ a : A, functional (a * b) = 0) → b = 0

namespace FrobeniusFunctional

variable {k A}

/-- The multiplication pairing associated to a Frobenius functional. -/
def pairing (lambda : FrobeniusFunctional k A) : LinearMap.BilinForm k A :=
  (LinearMap.mul k A).compr₂ lambda.functional

@[simp]
theorem pairing_apply (lambda : FrobeniusFunctional k A) (a b : A) :
    lambda.pairing a b = lambda.functional (a * b) := (rfl)

/-- Multiplication makes the pairing associated to any functional associative. -/
theorem pairing_mul_assoc (lambda : FrobeniusFunctional k A) (a b c : A) :
    lambda.pairing (a * b) c = lambda.pairing a (b * c) := by
  simp only [pairing_apply, mul_assoc]

/-- Left nondegeneracy says exactly that the multiplication pairing is injective in its first
argument. -/
theorem pairing_injective (lambda : FrobeniusFunctional k A) :
    Function.Injective lambda.pairing :=
  LinearMap.ker_eq_bot.mp <|
    LinearMap.separatingLeft_iff_ker_eq_bot.mp lambda.left_nondegenerate

/-- Right nondegeneracy says exactly that the flipped multiplication pairing is injective. -/
theorem pairing_flip_injective (lambda : FrobeniusFunctional k A) :
    Function.Injective lambda.pairing.flip :=
  LinearMap.ker_eq_bot.mp <|
    LinearMap.separatingLeft_iff_ker_eq_bot.mp lambda.right_nondegenerate

/-- The multiplication pairing is nondegenerate on both sides. -/
theorem pairing_nondegenerate (lambda : FrobeniusFunctional k A) :
    lambda.pairing.Nondegenerate :=
  ⟨lambda.left_nondegenerate, lambda.right_nondegenerate⟩

/-- The multiplication pairing of a finite-dimensional Frobenius algebra is perfect. -/
instance pairing_isPerfPair [FiniteDimensional k A] (lambda : FrobeniusFunctional k A) :
    lambda.pairing.IsPerfPair :=
  LinearMap.IsPerfPair.of_injective lambda.pairing_injective lambda.pairing_flip_injective

/-- The canonical right-linear map from an algebra to its right dual. -/
def toRightDualLinearMap (lambda : FrobeniusFunctional k A) : A →ₗ[Aᵐᵒᵖ] RightDual k A where
  toFun a := lambda.pairing a
  map_add' a b := by
    ext c
    simp
  map_smul' a b := by
    ext c
    simp [mul_assoc]

@[simp]
theorem toRightDualLinearMap_apply_apply (lambda : FrobeniusFunctional k A) (a b : A) :
    lambda.toRightDualLinearMap a b = lambda.functional (a * b) := (rfl)

/-- A Frobenius functional identifies the regular right module with its right dual. -/
noncomputable def toRightDualEquiv [FiniteDimensional k A] (lambda : FrobeniusFunctional k A) :
    A ≃ₗ[Aᵐᵒᵖ] RightDual k A :=
  LinearEquiv.ofBijective lambda.toRightDualLinearMap
    (lambda.pairing_isPerfPair.bijective_left)

@[simp]
theorem toRightDualEquiv_apply_apply [FiniteDimensional k A]
    (lambda : FrobeniusFunctional k A) (a b : A) :
    lambda.toRightDualEquiv a b = lambda.functional (a * b) := by
  have h : lambda.toRightDualEquiv a = lambda.toRightDualLinearMap a := by
    unfold toRightDualEquiv
    apply LinearEquiv.ofBijective_apply
  rw [h, toRightDualLinearMap_apply_apply]

/-- A right-module equivalence is determined by its value at one. -/
theorem rightDualEquiv_apply_apply (e : A ≃ₗ[Aᵐᵒᵖ] RightDual k A) (a b : A) :
    e a b = e 1 (a * b) := by
  rw [← RightDual.op_smul_apply k A, ← e.map_smul]
  simp

/-- A right-module equivalence with the right dual determines a Frobenius functional. -/
def ofRightDualEquiv (e : A ≃ₗ[Aᵐᵒᵖ] RightDual k A) : FrobeniusFunctional k A where
  functional := e 1
  left_nondegenerate a ha := by
    apply e.injective
    rw [map_zero]
    ext b
    rw [rightDualEquiv_apply_apply]
    exact ha b
  right_nondegenerate b hb := by
    rw [← Module.forall_dual_apply_eq_zero_iff k b]
    intro phi
    obtain ⟨a, rfl⟩ := e.surjective phi
    rw [rightDualEquiv_apply_apply]
    exact hb a

@[simp]
theorem ofRightDualEquiv_functional_apply (e : A ≃ₗ[Aᵐᵒᵖ] RightDual k A) (a : A) :
    (ofRightDualEquiv e).functional a = e 1 a := (rfl)

@[simp]
theorem ofRightDualEquiv_toRightDualEquiv [FiniteDimensional k A]
    (lambda : FrobeniusFunctional k A) :
    ofRightDualEquiv lambda.toRightDualEquiv = lambda := by
  ext a
  simp

@[simp]
theorem toRightDualEquiv_ofRightDualEquiv [FiniteDimensional k A]
    (e : A ≃ₗ[Aᵐᵒᵖ] RightDual k A) :
    (ofRightDualEquiv e).toRightDualEquiv = e := by
  ext a b
  rw [toRightDualEquiv_apply_apply, ofRightDualEquiv_functional_apply]
  exact (rightDualEquiv_apply_apply e a b).symm

/-- Frobenius functionals are equivalent to right-module identifications with the right dual. -/
noncomputable def equivRightDualEquiv [FiniteDimensional k A] :
    FrobeniusFunctional k A ≃ (A ≃ₗ[Aᵐᵒᵖ] RightDual k A) where
  toFun := toRightDualEquiv
  invFun := ofRightDualEquiv
  left_inv := ofRightDualEquiv_toRightDualEquiv
  right_inv := toRightDualEquiv_ofRightDualEquiv

end FrobeniusFunctional

end

section

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A]

/-- A Frobenius functional whose multiplication pairing is symmetric. -/
@[ext]
structure SymmetricFrobeniusFunctional extends FrobeniusFunctional k A where
  /-- The functional is a trace: it is unchanged by swapping a product's factors. -/
  trace_mul_comm : ∀ a b : A, functional (a * b) = functional (b * a)

namespace SymmetricFrobeniusFunctional

variable {k A}

/-- The multiplication pairing of a symmetric Frobenius functional is symmetric. -/
theorem pairing_isSymm (lambda : SymmetricFrobeniusFunctional k A) :
    lambda.toFrobeniusFunctional.pairing.IsSymm := ⟨lambda.trace_mul_comm⟩

end SymmetricFrobeniusFunctional

end


end TauCeti
