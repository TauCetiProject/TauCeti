/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.Complex.Order

/-!
# Algebraic GNS representations

A complex-linear functional on a unital star algebra is positive when it is nonnegative on
all squares `star a * a`. Its null space is a left ideal, and the quotient is an inner product
space with a cyclic algebra representation by left multiplication. The adjoint identity holds
on this space, but the operators need not be bounded and the space need not be complete.

The construction applies in particular to positive noncommutative star-polynomial distributions.
It needs no norm, order, faithfulness or traciality on the original algebra. Normalization is
required only to make the cyclic vector a unit vector.

The inner-product construction uses Mathlib's `PreInnerProductSpace.Core` and
`InnerProductSpace.Core`, as in `PositiveLinearMap.PreGNS`, but positivity here is positivity
on squares in an arbitrary star algebra rather than order preservation on a C⋆-algebra.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 4.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3 (the algebraic GNS argument).
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace TauCeti

variable (A : Type*) [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- A complex-linear functional nonnegative on every square `star a * a`.
The algebra is not assumed to carry a norm or an order. -/
structure StarPositiveFunctional extends A →ₗ[ℂ] ℂ where
  /-- Positivity on algebraic squares. -/
  square_nonneg : ∀ a, 0 ≤ toLinearMap (star a * a)

namespace StarPositiveFunctional

variable {A}

instance : FunLike (StarPositiveFunctional A) A ℂ where
  coe φ := φ.toLinearMap
  coe_injective φ ψ h := by
    cases φ
    cases ψ
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (StarPositiveFunctional A) ℂ A ℂ where
  map_add φ := φ.toLinearMap.map_add
  map_smulₛₗ φ := φ.toLinearMap.map_smul

omit [StarModule ℂ A] in
/-- Positive functionals are determined by their values. -/
@[ext]
theorem ext {φ ψ : StarPositiveFunctional A} (h : ∀ a, φ a = ψ a) : φ = ψ :=
  DFunLike.ext φ ψ h

omit [StarModule ℂ A] in
@[simp]
theorem toLinearMap_apply (φ : StarPositiveFunctional A) (a : A) : φ.toLinearMap a = φ a :=
  (rfl)

omit [StarModule ℂ A] in
@[simp]
theorem mk_apply (f : A →ₗ[ℂ] ℂ) (h : ∀ a, 0 ≤ f (star a * a)) (a : A) :
    (StarPositiveFunctional.mk f h) a = f a := (rfl)

variable (φ : StarPositiveFunctional A)

/-- Positivity implies conjugate symmetry of the associated sesquilinear form. -/
theorem conj_apply_star_mul (a b : A) : star (φ (star a * b)) = φ (star b * a) := by
  have him (x : A) : (φ (star x * x)).im = 0 := (φ.square_nonneg x).2.symm
  have hsum := him (a + b)
  have hI := him (a + Complex.I • b)
  simp only [star_add, add_mul, mul_add, map_add, Complex.add_im, him] at hsum
  simp only [star_add, star_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    map_add, map_smul, smul_eq_mul, Complex.add_im, Complex.mul_im,
    Complex.star_def, Complex.conj_I, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, Complex.mul_re, him] at hI
  apply Complex.ext <;> simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
  · linarith
  · linarith

/-- A positive functional preserves the involution. -/
@[simp]
theorem map_star (a : A) : φ (star a) = star (φ a) := by
  simpa using (φ.conj_apply_star_mul 1 a).symm

/-- The positive semidefinite inner product before dividing out the null space. -/
private abbrev preInner : PreInnerProductSpace.Core ℂ A where
  inner a b := φ (star a * b)
  conj_inner_symm a b := φ.conj_apply_star_mul b a
  re_inner_nonneg a := (φ.square_nonneg a).1
  add_left a b c := by simp [add_mul]
  smul_left a b c := by simp

/-- A vector has zero square value exactly when it pairs to zero with every vector.
This is the null-space consequence of Cauchy–Schwarz, without a boundedness assumption. -/
theorem apply_star_mul_self_eq_zero_iff (a : A) :
    φ (star a * a) = 0 ↔ ∀ b, φ (star b * a) = 0 := by
  let := InnerProductSpace.Core.toSeminormedAddCommGroup (c := φ.preInner)
  let := InnerProductSpace.ofCore φ.preInner
  constructor
  · intro ha b
    have hnorm : ‖a‖ = 0 := by
      rw [← sq_eq_zero_iff, norm_sq_eq_re_inner (𝕜 := ℂ)]
      exact congrArg Complex.re ha
    have h := norm_inner_le_norm (𝕜 := ℂ) b a
    rw [hnorm, mul_zero, norm_le_zero_iff] at h
    exact h
  · intro h
    exact h a

/-- The null space of a positive functional. Its elements pair to zero against every element
of the algebra; equivalently, their square value is zero. -/
def nullSubmodule : Submodule ℂ A where
  carrier := {a | ∀ b, φ (star b * a) = 0}
  zero_mem' := by simp
  add_mem' ha hb c := by simp [mul_add, ha c, hb c]
  smul_mem' c a ha b := by simp [ha b]

omit [StarModule ℂ A] in
/-- Membership in the null space is vanishing of all pairings. -/
@[simp]
theorem mem_nullSubmodule (a : A) : a ∈ φ.nullSubmodule ↔ ∀ b, φ (star b * a) = 0 :=
  Iff.rfl

/-- The null space is precisely the zero set of the quadratic form. -/
theorem mem_nullSubmodule_iff (a : A) :
    a ∈ φ.nullSubmodule ↔ φ (star a * a) = 0 :=
  (φ.apply_star_mul_self_eq_zero_iff a).symm

omit [StarModule ℂ A] in
/-- The null space is a left ideal, even when the functional is not tracial. -/
theorem mul_mem_nullSubmodule (a : A) {b : A} (hb : b ∈ φ.nullSubmodule) :
    a * b ∈ φ.nullSubmodule := by
  intro c
  simpa [mul_assoc] using hb (star a * c)

/-- The algebraic GNS space: quotient by the null space, without completion. -/
abbrev GNS := A ⧸ φ.nullSubmodule

/-- The canonical linear map into the algebraic GNS space. -/
def classMap : A →ₗ[ℂ] φ.GNS := φ.nullSubmodule.mkQ

omit [StarModule ℂ A] in
/-- Every vector of the algebraic GNS space is the class of an algebra element. -/
theorem classMap_surjective : Function.Surjective φ.classMap :=
  φ.nullSubmodule.mkQ_surjective

/-- The class of an element is zero exactly when its square value is zero. -/
@[simp]
theorem classMap_eq_zero_iff (a : A) : φ.classMap a = 0 ↔ φ (star a * a) = 0 := by
  rw [classMap, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_nullSubmodule_iff]

private theorem pairing_eq_of_rel {a a' b b' : A}
    (ha : φ.nullSubmodule.quotientRel a a') (hb : φ.nullSubmodule.quotientRel b b') :
    φ (star a * b) = φ (star a' * b') := by
  have hleft := (φ.mem_nullSubmodule (a - a')).mp
    (φ.nullSubmodule.quotientRel_def.mp ha) b
  have hright := (φ.mem_nullSubmodule (b - b')).mp
    (φ.nullSubmodule.quotientRel_def.mp hb) a'
  rw [mul_sub, map_sub] at hleft
  have hleft' := congrArg star hleft
  simp only [star_sub, φ.conj_apply_star_mul, star_zero] at hleft'
  simp only [mul_sub, map_sub] at hright
  exact (sub_eq_zero.mp hleft').trans (sub_eq_zero.mp hright)

private def quotientInner (x y : φ.GNS) : ℂ :=
  Quotient.liftOn₂ x y (fun a b => φ (star a * b)) fun _ _ _ _ ha hb =>
    φ.pairing_eq_of_rel ha hb

private theorem quotientInner_classMap (a b : A) :
    φ.quotientInner (φ.classMap a) (φ.classMap b) = φ (star a * b) := rfl

private abbrev innerCore : InnerProductSpace.Core ℂ φ.GNS where
  inner := φ.quotientInner
  conj_inner_symm := by
    intro x y
    obtain ⟨a, rfl⟩ := φ.classMap_surjective x
    obtain ⟨b, rfl⟩ := φ.classMap_surjective y
    exact φ.conj_apply_star_mul b a
  re_inner_nonneg := by
    intro x
    obtain ⟨a, rfl⟩ := φ.classMap_surjective x
    exact (φ.square_nonneg a).1
  add_left := by
    intro x y z
    obtain ⟨a, rfl⟩ := φ.classMap_surjective x
    obtain ⟨b, rfl⟩ := φ.classMap_surjective y
    obtain ⟨c, rfl⟩ := φ.classMap_surjective z
    rw [← map_add, φ.quotientInner_classMap, φ.quotientInner_classMap,
      φ.quotientInner_classMap]
    simp [add_mul]
  smul_left := by
    intro x y r
    obtain ⟨a, rfl⟩ := φ.classMap_surjective x
    obtain ⟨b, rfl⟩ := φ.classMap_surjective y
    rw [← map_smul, φ.quotientInner_classMap, φ.quotientInner_classMap]
    simp
  definite := by
    intro x hx
    obtain ⟨a, rfl⟩ := φ.classMap_surjective x
    exact (φ.classMap_eq_zero_iff a).mpr hx

@[no_expose]
instance : NormedAddCommGroup φ.GNS := by
  exact (innerCore φ).toNormedAddCommGroup

@[no_expose]
instance : InnerProductSpace ℂ φ.GNS := by
  exact InnerProductSpace.ofCore (innerCore φ).toCore

/-- Inner products of classes are the original square pairings. -/
@[simp]
theorem inner_classMap (a b : A) :
    ⟪φ.classMap a, φ.classMap b⟫_ℂ = φ (star a * b) :=
  φ.quotientInner_classMap a b

/-- The GNS norm of a class is determined by the quadratic form. -/
theorem norm_classMap_sq (a : A) : ‖φ.classMap a‖ ^ 2 = (φ (star a * a)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), φ.inner_classMap]
  rfl

private def leftMul (a : A) : Module.End ℂ φ.GNS :=
  φ.nullSubmodule.mapQ φ.nullSubmodule (LinearMap.mul ℂ A a)
    (fun _ hb => φ.mul_mem_nullSubmodule a hb)

omit [StarModule ℂ A] in
private theorem leftMul_classMap (a b : A) :
    φ.leftMul a (φ.classMap b) = φ.classMap (a * b) := rfl

/-- The algebra acts on its algebraic GNS space by left multiplication.
The endomorphisms are algebraic linear maps and are not asserted to be continuous. -/
def representation : A →ₐ[ℂ] Module.End ℂ φ.GNS where
  toFun := φ.leftMul
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := φ.classMap_surjective x
    simp only [φ.leftMul_classMap, one_mul, Module.End.one_apply]
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := φ.classMap_surjective x
    simp only [Module.End.mul_apply, φ.leftMul_classMap, mul_assoc]
  map_zero' := by
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := φ.classMap_surjective x
    simp only [φ.leftMul_classMap, zero_mul, map_zero, LinearMap.zero_apply]
  map_add' a b := by
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := φ.classMap_surjective x
    simp only [LinearMap.add_apply, φ.leftMul_classMap, add_mul, map_add]
  commutes' r := by
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := φ.classMap_surjective x
    simp only [φ.leftMul_classMap, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, map_smul, LinearMap.smul_apply, Module.End.one_apply]

omit [StarModule ℂ A] in
/-- The action on classes is left multiplication. -/
@[simp]
theorem representation_classMap (a b : A) :
    φ.representation a (φ.classMap b) = φ.classMap (a * b) := (rfl)

/-- The representation respects adjoints on the algebraic GNS domain. -/
theorem inner_representation (a : A) (x y : φ.GNS) :
    ⟪φ.representation a x, y⟫_ℂ = ⟪x, φ.representation (star a) y⟫_ℂ := by
  obtain ⟨b, rfl⟩ := φ.classMap_surjective x
  obtain ⟨c, rfl⟩ := φ.classMap_surjective y
  simp [mul_assoc]

/-- The canonical cyclic vector is the class of the unit. -/
def cyclicVector : φ.GNS := φ.classMap 1

omit [StarModule ℂ A] in
/-- The cyclic vector is the class of the unit. -/
theorem cyclicVector_def : φ.cyclicVector = φ.classMap 1 := (rfl)

omit [StarModule ℂ A] in
/-- Acting on the cyclic vector produces the class of the acting element. -/
@[simp]
theorem representation_cyclicVector (a : A) :
    φ.representation a φ.cyclicVector = φ.classMap a := by
  simp [cyclicVector_def]

omit [StarModule ℂ A] in
/-- The orbit of the canonical vector consists of every vector of the algebraic GNS space. -/
theorem representation_cyclicVector_surjective :
    Function.Surjective (fun a => φ.representation a φ.cyclicVector) := by
  simpa using φ.classMap_surjective

/-- The original functional is the vector functional of its algebraic GNS representation. -/
@[simp]
theorem inner_cyclicVector_classMap (a : A) :
    ⟪φ.cyclicVector, φ.classMap a⟫_ℂ = φ a := by
  simp [cyclicVector_def]

/-- The squared norm of the cyclic vector is the mass of the functional. -/
theorem norm_cyclicVector_sq : ‖φ.cyclicVector‖ ^ 2 = (φ 1).re := by
  rw [cyclicVector_def, φ.norm_classMap_sq]
  simp

/-- A normalized positive functional is realized at a unit cyclic vector. -/
theorem norm_cyclicVector (hφ : φ 1 = 1) : ‖φ.cyclicVector‖ = 1 := by
  have h := φ.norm_cyclicVector_sq
  rw [hφ, Complex.one_re] at h
  nlinarith [norm_nonneg φ.cyclicVector]

end StarPositiveFunctional

end TauCeti
