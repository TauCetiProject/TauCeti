/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# First-order endomorphisms of a commutative algebra

An endomorphism is algebraically of order at most one if its double commutators with
multiplication operators vanish. Such an endomorphism has a unique decomposition into a
derivation and multiplication by its value at one. This is the algebraic step in recognizing
first-order differential operators on scalar functions; no continuity assumption is needed.

* `LinearMap.forall_lie_lie_mulLeft_eq_zero_iff` expresses the commutator condition as a
  modified Leibniz rule.
* `LinearMap.derivationOfDoubleCommutator` extracts the derivation by subtracting multiplication
  by the value at one.
* `TauCeti.firstOrderOperatorsEquivDerivationProd` identifies the module of these endomorphisms
  with `Derivation R A A × A`.
-/

public section

attribute [local instance] LieRing.ofAssociativeRing

namespace LinearMap

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- Commuting with multiplication measures the failure of linearity over the algebra. -/
theorem lie_mulLeft_apply (D : Module.End R A) (a b : A) :
    ⁅D, mulLeft R a⁆ b = D (a * b) - a * D b := by
  simp [Ring.lie_def, mul_apply_eq_comp]

/-- An endomorphism commuting with every multiplication operator is multiplication by its
value at one. -/
theorem forall_lie_mulLeft_eq_zero_iff (D : Module.End R A) :
    (∀ a : A, ⁅D, mulLeft R a⁆ = 0) ↔ D = mulLeft R (D 1) := by
  constructor
  · intro h
    ext a
    have ha := congrArg (fun T : Module.End R A ↦ T 1) (h a)
    simp only [lie_mulLeft_apply, mul_one, LinearMap.zero_apply] at ha
    simpa [mul_comm] using sub_eq_zero.mp ha
  · rintro h a
    rw [h]
    ext b
    rw [lie_mulLeft_apply]
    simp [mul_left_comm]

/-- Vanishing double commutators are equivalent to the Leibniz rule with the correction
term `a * b * D 1`. -/
theorem forall_lie_lie_mulLeft_eq_zero_iff (D : Module.End R A) :
    (∀ a b : A, ⁅⁅D, mulLeft R a⁆, mulLeft R b⁆ = 0) ↔
      ∀ a b, D (a * b) = a * D b + b * D a - a * b * D 1 := by
  constructor
  · intro h a b
    have hab := congrArg (fun T : Module.End R A ↦ T b)
      ((forall_lie_mulLeft_eq_zero_iff ⁅D, mulLeft R a⁆).mp (h a))
    simp only [lie_mulLeft_apply, mulLeft_apply, mul_one] at hab
    linear_combination hab
  · intro h a b
    ext c
    simp only [lie_mulLeft_apply, h, mul_sub, LinearMap.zero_apply]
    ring

/-- Subtracting multiplication by `D 1` from an endomorphism with vanishing double commutators
produces a derivation. -/
def derivationOfDoubleCommutator (D : Module.End R A)
    (hD : ∀ a b : A, ⁅⁅D, mulLeft R a⁆, mulLeft R b⁆ = 0) : Derivation R A A :=
  Derivation.mk' (D - mulLeft R (D 1)) fun a b ↦ by
    simp only [LinearMap.sub_apply, mulLeft_apply, smul_eq_mul]
    rw [(forall_lie_lie_mulLeft_eq_zero_iff D).mp hD a b]
    ring

/-- The derivation part of `D` acts by subtracting the zeroth-order term. -/
@[simp]
theorem derivationOfDoubleCommutator_apply (D : Module.End R A)
    (hD : ∀ a b : A, ⁅⁅D, mulLeft R a⁆, mulLeft R b⁆ = 0) (a : A) :
    D.derivationOfDoubleCommutator hD a = D a - D 1 * a := (rfl)

/-- Every first-order endomorphism is the sum of its derivation part and multiplication
by its value at one. -/
theorem derivationOfDoubleCommutator_add_mulLeft (D : Module.End R A)
    (hD : ∀ a b : A, ⁅⁅D, mulLeft R a⁆, mulLeft R b⁆ = 0) :
    (D.derivationOfDoubleCommutator hD).toLinearMap + mulLeft R (D 1) = D := by
  ext a
  simp

/-- A first-order endomorphism commutes with multiplication up to multiplication by its
extracted derivation. -/
theorem lie_mulLeft_eq_mulLeft_derivationOfDoubleCommutator (D : Module.End R A)
    (hD : ∀ a b : A, ⁅⁅D, mulLeft R a⁆, mulLeft R b⁆ = 0) (a : A) :
    ⁅D, mulLeft R a⁆ = mulLeft R (D.derivationOfDoubleCommutator hD a) := by
  simpa [lie_mulLeft_apply, mul_comm] using
    (forall_lie_mulLeft_eq_zero_iff ⁅D, mulLeft R a⁆).mp (hD a)

end LinearMap

namespace Derivation

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- The commutator of a derivation with multiplication is multiplication by the derivative. -/
@[simp]
theorem lie_mulLeft (δ : Derivation R A A) (a : A) :
    ⁅δ.toLinearMap, LinearMap.mulLeft R a⁆ = LinearMap.mulLeft R (δ a) := by
  ext b
  rw [LinearMap.lie_mulLeft_apply]
  simp [smul_eq_mul, mul_comm]

end Derivation

namespace TauCeti

variable (R A : Type*) [CommSemiring R] [CommRing A] [Algebra R A]

/-- The algebraic first-order endomorphisms of a commutative algebra: those whose double
commutators with multiplication vanish. The scalar action multiplies the output. -/
def firstOrderOperators : Submodule A (Module.End R A) where
  carrier := {D | ∀ a b : A, ⁅⁅D, LinearMap.mulLeft R a⁆, LinearMap.mulLeft R b⁆ = 0}
  zero_mem' := by simp
  add_mem' {D E} hD hE := by
    intro a b
    simp only [add_lie, hD a b, hE a b, add_zero]
  smul_mem' c D hD := by
    apply (LinearMap.forall_lie_lie_mulLeft_eq_zero_iff _).mpr
    have h := (LinearMap.forall_lie_lie_mulLeft_eq_zero_iff D).mp hD
    intro a b
    simp only [LinearMap.smul_apply, smul_eq_mul, h]
    ring

end TauCeti

namespace LinearMap

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- Membership is precisely the vanishing double-commutator condition. -/
@[simp]
theorem mem_firstOrderOperators (D : Module.End R A) :
    D ∈ TauCeti.firstOrderOperators R A ↔
      ∀ a b : A, ⁅⁅D, LinearMap.mulLeft R a⁆, LinearMap.mulLeft R b⁆ = 0 := Iff.rfl

/-- Multiplication is an algebraic first-order endomorphism. -/
theorem mulLeft_mem_firstOrderOperators (c : A) :
    mulLeft R c ∈ TauCeti.firstOrderOperators R A := by
  rw [mem_firstOrderOperators]
  intro a b
  rw [(forall_lie_mulLeft_eq_zero_iff (mulLeft R c)).mpr (by simp) a, zero_lie]

end LinearMap

namespace Derivation

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- A derivation is an algebraic first-order endomorphism. -/
theorem toLinearMap_mem_firstOrderOperators (δ : Derivation R A A) :
    δ.toLinearMap ∈ TauCeti.firstOrderOperators R A := by
  rw [LinearMap.mem_firstOrderOperators]
  intro a b
  rw [lie_mulLeft]
  exact (LinearMap.forall_lie_mulLeft_eq_zero_iff _).mpr (by simp) b

/-- A derivation plus multiplication is an algebraic first-order endomorphism. -/
theorem add_mulLeft_mem_firstOrderOperators (δ : Derivation R A A) (c : A) :
    δ.toLinearMap + LinearMap.mulLeft R c ∈ TauCeti.firstOrderOperators R A := by
  exact add_mem δ.toLinearMap_mem_firstOrderOperators (LinearMap.mulLeft_mem_firstOrderOperators c)

end Derivation

namespace TauCeti

variable (R A : Type*) [CommSemiring R] [CommRing A] [Algebra R A]

/-- First-order endomorphisms split uniquely and linearly into a derivation and a multiplication
operator. The multiplication coefficient is evaluation at one. -/
def firstOrderOperatorsEquivDerivationProd :
    firstOrderOperators R A ≃ₗ[A] Derivation R A A × A where
  toFun D := ⟨D.val.derivationOfDoubleCommutator
    ((LinearMap.mem_firstOrderOperators _).mp D.property), D.val 1⟩
  invFun p := ⟨p.1.toLinearMap + LinearMap.mulLeft R p.2,
    p.1.add_mulLeft_mem_firstOrderOperators p.2⟩
  left_inv D := by
    apply Subtype.ext
    exact D.val.derivationOfDoubleCommutator_add_mulLeft D.property
  right_inv p := by
    apply Prod.ext
    · ext a
      simp
    · simp
  map_add' D E := by
    apply Prod.ext
    · ext a
      simp
      ring
    · simp
  map_smul' c D := by
    apply Prod.ext
    · ext a
      simp [smul_eq_mul]
      ring
    · simp

/-- The derivation coordinate subtracts multiplication by the value at one. -/
@[simp]
theorem firstOrderOperatorsEquivDerivationProd_fst_apply
    (D : firstOrderOperators R A) (a : A) :
    (firstOrderOperatorsEquivDerivationProd R A D).1 a = D.val a - D.val 1 * a := (rfl)

/-- The multiplication coordinate is the value at one. -/
@[simp]
theorem firstOrderOperatorsEquivDerivationProd_snd (D : firstOrderOperators R A) :
    (firstOrderOperatorsEquivDerivationProd R A D).2 = D.val 1 := (rfl)

/-- Reconstructing a first-order endomorphism adds the derivation and multiplication. -/
@[simp]
theorem firstOrderOperatorsEquivDerivationProd_symm_apply
    (p : Derivation R A A × A) :
    ((firstOrderOperatorsEquivDerivationProd R A).symm p).val =
      p.1.toLinearMap + LinearMap.mulLeft R p.2 := (rfl)

end TauCeti
