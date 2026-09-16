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

`(phi * a) b = phi (a * b)`,

recorded as a left action of `Aᵐᵒᵖ`.

The multiplication pairing `TauCeti.mulPairing` and the canonical map
`TauCeti.toRightDualLinearMap` to the right dual are attached to an arbitrary functional: being
Frobenius is not needed to form them, only to make them nondegenerate, respectively bijective. The
right dual, the pairing, both functional structures and the reverse construction
`TauCeti.FrobeniusFunctional.ofRightDualEquiv` need only a commutative semiring base and a semiring
algebra, the last one additionally a projective module so that the dual separates points; a field,
a ring and finite-dimensionality enter exactly at the perfect-pairing argument. For a Frobenius
functional `lambda` the canonical map sends `a` to the functional `b ↦ lambda (a * b)`, and it is
right-linear for precisely the action above. Conversely a right-module equivalence
`e : A ≃ RightDual k A` recovers its functional by evaluating `e 1`; right-linearity shows these
constructions are inverse. The equivalence requires finite-dimensionality only in the forward
direction, where two-sided nondegeneracy upgrades to a perfect pairing.

`TauCeti.SymmetricFrobeniusFunctional` records the additional trace identity
`lambda (a * b) = lambda (b * a)` and identifies it with symmetry of the multiplication pairing.
It is deliberately stronger than an arbitrary Frobenius functional.

## Main definitions

* `TauCeti.RightDual`: the linear dual carrying the right action above.
* `TauCeti.mulPairing`: the pairing `(a, b) ↦ lambda (a * b)` of a linear functional.
* `TauCeti.FrobeniusFunctional`: a functional with two-sided nondegenerate multiplication pairing.
* `TauCeti.FrobeniusFunctional.equivRightDualEquiv`: the equivalence between Frobenius
  functionals and right-module equivalences with the right dual.
* `TauCeti.SymmetricFrobeniusFunctional`: a Frobenius functional satisfying the trace identity.

## Implementation notes

`RightDual k A` is a type synonym for `Module.Dual k A`, not an abbreviation for it: the action
above is one convention among several, so attaching it to `Module.Dual k A` itself would impose it
on every `k`-linear dual and would override the codomain-scaling action that Mathlib installs
there. The synonym inherits the additive and `k`-linear structure and the evaluation API of the
dual through `inferInstanceAs`, and `TauCeti.RightDual.ofDual` and `TauCeti.RightDual.toDual`
translate between the two readings; only the `Aᵐᵒᵖ`-action is new. Those three declarations are
`@[expose]`d because the synonym and its transport maps are definitionally the identity and the
elaborator needs that to elaborate the instances below; every other definition here is opaque
outside the module and is used through its characteristic lemmas.

The same reasoning, for the dual of a right module over a base algebra, is recorded in
`TauCeti/LinearAlgebra/Dual/RightAction.lean`. That file's `TauCeti.dualRightAction` dualizes a
right `A`-module to a left `A`-module, whereas the action here dualizes the *left* regular module
of `A` and therefore acts by `Aᵐᵒᵖ`; obtaining it from `dualRightAction` would need `A` as a right
`Aᵐᵒᵖ`-module, that is a `Module Aᵐᵒᵖᵐᵒᵖ A` instance, which does not exist.

## References

See Curtis--Reiner, *Methods of Representation Theory*, Volume I, Section 9, and Lam,
*Lectures on Modules and Rings*, Section 16.
-/

public section

namespace TauCeti

open Module

universe u v

section Semiring

variable (k : Type u) (A : Type v) [CommSemiring k] [Semiring A] [Algebra k A]

/-- The linear dual of an algebra, with the right action `(phi * a) b = phi (a * b)`, recorded as a
left action of `Aᵐᵒᵖ`. -/
@[expose]
def RightDual : Type max v u := Module.Dual k A

namespace RightDual

instance : AddCommMonoid (RightDual k A) := inferInstanceAs (AddCommMonoid (Module.Dual k A))

instance : Module k (RightDual k A) := inferInstanceAs (Module k (Module.Dual k A))

instance : FunLike (RightDual k A) A k := inferInstanceAs (FunLike (Module.Dual k A) A k)

instance : LinearMapClass (RightDual k A) k A k :=
  inferInstanceAs (LinearMapClass (Module.Dual k A) k A k)

variable {k A}

/-- Read a linear functional as an element of the right dual. -/
@[expose]
def ofDual : Module.Dual k A ≃ₗ[k] RightDual k A := LinearEquiv.refl k _

/-- Forget the right action, reading an element of the right dual as a linear functional. -/
@[expose]
def toDual : RightDual k A ≃ₗ[k] Module.Dual k A := LinearEquiv.refl k _

@[simp]
theorem ofDual_apply (phi : Module.Dual k A) (a : A) : ofDual phi a = phi a := rfl

@[simp]
theorem toDual_apply (phi : RightDual k A) (a : A) : toDual phi a = phi a := rfl

@[ext]
theorem ext {phi psi : RightDual k A} (h : ∀ a, phi a = psi a) : phi = psi :=
  DFunLike.ext _ _ h

@[simp]
theorem zero_apply (a : A) : (0 : RightDual k A) a = 0 := rfl

@[simp]
theorem add_apply (phi psi : RightDual k A) (a : A) : (phi + psi) a = phi a + psi a := rfl

/-- An element of a projective module killed by every functional in the right dual is zero. -/
theorem forall_apply_eq_zero_iff [Module.Projective k A] (b : A) :
    (∀ phi : RightDual k A, phi b = 0) ↔ b = 0 :=
  ⟨fun h => (Module.forall_dual_apply_eq_zero_iff k b).mp fun phi => h (ofDual phi),
    fun hb phi => by simp [hb]⟩

instance : SMul Aᵐᵒᵖ (RightDual k A) :=
  ⟨fun a phi => ofDual ((toDual phi).comp (LinearMap.mulLeft k a.unop))⟩

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
    simp only [smul_apply, add_apply, MulOpposite.unop_add, add_mul, map_add]

end RightDual

variable {k A}

/-- The multiplication pairing `(a, b) ↦ lambda (a * b)` of a linear functional. -/
def mulPairing (lambda : A →ₗ[k] k) : LinearMap.BilinForm k A :=
  (LinearMap.mul k A).compr₂ lambda

@[simp]
theorem mulPairing_apply (lambda : A →ₗ[k] k) (a b : A) :
    mulPairing lambda a b = lambda (a * b) := (rfl)

/-- Multiplication makes the pairing associated to any functional associative. -/
theorem mulPairing_mul_assoc (lambda : A →ₗ[k] k) (a b c : A) :
    mulPairing lambda (a * b) c = mulPairing lambda a (b * c) := by
  simp only [mulPairing_apply, mul_assoc]

/-- The canonical right-linear map from an algebra to its right dual attached to a functional. -/
def toRightDualLinearMap (lambda : A →ₗ[k] k) : A →ₗ[Aᵐᵒᵖ] RightDual k A where
  toFun a := RightDual.ofDual (mulPairing lambda a)
  map_add' a b := by
    ext c
    simp
  map_smul' a b := by
    ext c
    simp [mul_assoc]

@[simp]
theorem toRightDualLinearMap_apply_apply (lambda : A →ₗ[k] k) (a b : A) :
    toRightDualLinearMap lambda a b = lambda (a * b) := (rfl)

/-- A right-module map from an algebra to its right dual is determined by its value at one. -/
theorem rightDualMap_apply_apply {F : Type*} [FunLike F A (RightDual k A)]
    [LinearMapClass F Aᵐᵒᵖ A (RightDual k A)] (f : F) (a b : A) :
    f a b = f 1 (a * b) := by
  rw [← RightDual.op_smul_apply, ← map_smul]
  simp

variable (k A)

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

/-- The multiplication pairing is nondegenerate on both sides. -/
theorem nondegenerate_mulPairing (lambda : FrobeniusFunctional k A) :
    (mulPairing lambda.functional).Nondegenerate :=
  ⟨lambda.left_nondegenerate, lambda.right_nondegenerate⟩

/-- A right-module equivalence with the right dual determines a Frobenius functional. Nothing
beyond separation of points by the dual, that is projectivity, is needed: this direction uses
neither a field nor finite-dimensionality. -/
def ofRightDualEquiv [Module.Projective k A] (e : A ≃ₗ[Aᵐᵒᵖ] RightDual k A) :
    FrobeniusFunctional k A where
  functional := RightDual.toDual (e 1)
  left_nondegenerate a ha := by
    apply e.injective
    rw [map_zero]
    ext b
    rw [rightDualMap_apply_apply]
    exact ha b
  right_nondegenerate b hb := by
    rw [← RightDual.forall_apply_eq_zero_iff (k := k) b]
    intro phi
    obtain ⟨a, rfl⟩ := e.surjective phi
    rw [rightDualMap_apply_apply]
    exact hb a

@[simp]
theorem ofRightDualEquiv_functional_apply [Module.Projective k A]
    (e : A ≃ₗ[Aᵐᵒᵖ] RightDual k A) (a : A) :
    (ofRightDualEquiv e).functional a = e 1 a := (rfl)

end FrobeniusFunctional

/-- A Frobenius functional whose multiplication pairing is symmetric. -/
@[ext]
structure SymmetricFrobeniusFunctional extends FrobeniusFunctional k A where
  /-- The functional is a trace: it is unchanged by swapping a product's factors. -/
  trace_mul_comm : ∀ a b : A, functional (a * b) = functional (b * a)

namespace SymmetricFrobeniusFunctional

variable {k A}

/-- The multiplication pairing of a symmetric Frobenius functional is symmetric. -/
theorem isSymm_mulPairing (lambda : SymmetricFrobeniusFunctional k A) :
    (mulPairing lambda.functional).IsSymm := ⟨lambda.trace_mul_comm⟩

end SymmetricFrobeniusFunctional

end Semiring

section FiniteDimensional

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

namespace FrobeniusFunctional

/-- Left nondegeneracy says exactly that the multiplication pairing is injective in its first
argument. -/
theorem mulPairing_injective (lambda : FrobeniusFunctional k A) :
    Function.Injective (mulPairing lambda.functional) :=
  LinearMap.ker_eq_bot.mp <|
    LinearMap.separatingLeft_iff_ker_eq_bot.mp lambda.left_nondegenerate

/-- Right nondegeneracy says exactly that the flipped multiplication pairing is injective. -/
theorem mulPairing_flip_injective (lambda : FrobeniusFunctional k A) :
    Function.Injective (mulPairing lambda.functional).flip :=
  LinearMap.ker_eq_bot.mp <|
    LinearMap.separatingLeft_iff_ker_eq_bot.mp lambda.right_nondegenerate

/-- The multiplication pairing of a finite-dimensional Frobenius algebra is perfect. -/
instance isPerfPair_mulPairing [FiniteDimensional k A] (lambda : FrobeniusFunctional k A) :
    (mulPairing lambda.functional).IsPerfPair :=
  LinearMap.IsPerfPair.of_injective lambda.mulPairing_injective lambda.mulPairing_flip_injective

/-- On a finite-dimensional algebra, the canonical map to the right dual attached to a Frobenius
functional is bijective. -/
theorem toRightDualLinearMap_bijective [FiniteDimensional k A]
    (lambda : FrobeniusFunctional k A) :
    Function.Bijective (toRightDualLinearMap lambda.functional) :=
  (RightDual.ofDual (k := k) (A := A)).bijective.comp
    lambda.isPerfPair_mulPairing.bijective_left

/-- A Frobenius functional identifies the regular right module with its right dual. -/
noncomputable def toRightDualEquiv [FiniteDimensional k A] (lambda : FrobeniusFunctional k A) :
    A ≃ₗ[Aᵐᵒᵖ] RightDual k A :=
  LinearEquiv.ofBijective (toRightDualLinearMap lambda.functional)
    lambda.toRightDualLinearMap_bijective

@[simp]
theorem toRightDualEquiv_apply_apply [FiniteDimensional k A]
    (lambda : FrobeniusFunctional k A) (a b : A) :
    lambda.toRightDualEquiv a b = lambda.functional (a * b) := by
  have h : lambda.toRightDualEquiv a = toRightDualLinearMap lambda.functional a := by
    unfold toRightDualEquiv
    apply LinearEquiv.ofBijective_apply
  rw [h, toRightDualLinearMap_apply_apply]

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
  exact (rightDualMap_apply_apply e a b).symm

/-- Frobenius functionals are equivalent to right-module identifications with the right dual. -/
noncomputable def equivRightDualEquiv [FiniteDimensional k A] :
    FrobeniusFunctional k A ≃ (A ≃ₗ[Aᵐᵒᵖ] RightDual k A) where
  toFun := toRightDualEquiv
  invFun := ofRightDualEquiv
  left_inv := ofRightDualEquiv_toRightDualEquiv
  right_inv := toRightDualEquiv_ofRightDualEquiv

@[simp]
theorem equivRightDualEquiv_apply [FiniteDimensional k A] (lambda : FrobeniusFunctional k A) :
    equivRightDualEquiv lambda = lambda.toRightDualEquiv := (rfl)

@[simp]
theorem equivRightDualEquiv_symm_apply [FiniteDimensional k A]
    (e : A ≃ₗ[Aᵐᵒᵖ] RightDual k A) :
    (equivRightDualEquiv (k := k) (A := A)).symm e = ofRightDualEquiv e := (rfl)

end FrobeniusFunctional

end FiniteDimensional

end TauCeti
