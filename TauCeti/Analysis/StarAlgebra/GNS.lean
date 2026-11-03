/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.Complex.Order

/-!
# Algebraic GNS representations

A complex-linear functional on a possibly non-unital star algebra is positive when it is
nonnegative on all squares `star a * a`. Its null space is a left ideal, and the quotient is an
inner product space with an action by left multiplication. In the unital case this action is
cyclic. The adjoint identity holds on this space, but the operators need not be bounded and the
space need not be complete.

The construction applies in particular to positive noncommutative star-polynomial distributions.
It needs no norm, order, faithfulness or traciality on the original algebra. Normalization is
required only to make the cyclic vector a unit vector.

The seminormed construction uses Mathlib's `PreInnerProductSpace.Core`, as in
`PositiveLinearMap.PreGNS`, followed by `SeparationQuotient` and its inner-product instance.
Positivity here is positivity on squares in an arbitrary star algebra rather than order
preservation on a C⋆-algebra.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 4.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3 (the algebraic GNS argument).
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace TauCeti

section NonUnital

variable (A : Type*) [NonUnitalRing A] [Module ℂ A] [StarRing A]

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

/-- Positive functionals are determined by their values. -/
@[ext]
theorem ext {φ ψ : StarPositiveFunctional A} (h : ∀ a, φ a = ψ a) : φ = ψ :=
  DFunLike.ext φ ψ h

@[simp]
theorem toLinearMap_apply (φ : StarPositiveFunctional A) (a : A) : φ.toLinearMap a = φ a :=
  (rfl)

@[simp]
theorem mk_apply (f : A →ₗ[ℂ] ℂ) (h : ∀ a, 0 ≤ f (star a * a)) (a : A) :
    (StarPositiveFunctional.mk f h) a = f a := (rfl)

variable (φ : StarPositiveFunctional A)

variable [StarModule ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- Positivity implies conjugate symmetry of the associated sesquilinear form. -/
theorem star_apply_star_mul (a b : A) : star (φ (star a * b)) = φ (star b * a) := by
  have him (x : A) : (φ (star x * x)).im = 0 := (φ.square_nonneg x).2.symm
  have hsum := him (a + b)
  have hI := him (a + Complex.I • b)
  simp [add_mul, mul_add, him] at hsum
  simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, him] at hI
  rw [Complex.ext_iff]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
  constructor <;> linarith

/-- A copy of the algebra carrying the seminorm induced by the positive functional. -/
def PreGNS (_φ : StarPositiveFunctional A) := A

@[no_expose]
instance : AddCommGroup φ.PreGNS := inferInstanceAs (AddCommGroup A)

@[no_expose]
instance : Module ℂ φ.PreGNS := inferInstanceAs (Module ℂ A)

/-- Identify the algebra with the space carrying its GNS seminorm. -/
def toPreGNS : A ≃ₗ[ℂ] φ.PreGNS := LinearEquiv.refl ℂ A

/-- The positive semidefinite inner product before dividing out the null space. -/
private abbrev preInner : PreInnerProductSpace.Core ℂ φ.PreGNS where
  inner a b := φ (star (φ.toPreGNS.symm a) * φ.toPreGNS.symm b)
  conj_inner_symm a b := φ.star_apply_star_mul _ _
  re_inner_nonneg a := (φ.square_nonneg _).1
  add_left a b c := by simp [add_mul]
  smul_left a b c := by simp [smul_mul_assoc]

@[no_expose]
instance : SeminormedAddCommGroup φ.PreGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := φ.preInner)

@[no_expose]
instance : InnerProductSpace ℂ φ.PreGNS := InnerProductSpace.ofCore φ.preInner

/-- The inner product before taking the separation quotient is the original pairing. -/
@[simp]
theorem inner_toPreGNS (a b : A) :
    ⟪φ.toPreGNS a, φ.toPreGNS b⟫_ℂ = φ (star a * b) := (rfl)

/-- A vector has zero square value exactly when it pairs to zero with every vector.
This is the null-space consequence of Cauchy–Schwarz, without a boundedness assumption. -/
theorem apply_star_mul_self_eq_zero_iff (a : A) :
    φ (star a * a) = 0 ↔ ∀ b, φ (star b * a) = 0 := by
  constructor
  · intro ha b
    have hnorm : ‖φ.toPreGNS a‖ = 0 := by
      rw [← sq_eq_zero_iff, norm_sq_eq_re_inner (𝕜 := ℂ), φ.inner_toPreGNS]
      exact congrArg (RCLike.re (K := ℂ)) ha
    simpa using inner_eq_zero_of_right (𝕜 := ℂ) (φ.toPreGNS b) hnorm
  · intro h
    exact h a

/-- The null space of the GNS seminorm, transported back to the original algebra. -/
def nullSubmodule : Submodule ℂ A :=
  (_root_.nullSubmodule ℂ φ.PreGNS).comap φ.toPreGNS.toLinearMap

/-- An algebra element is null exactly when its GNS seminorm vanishes. -/
theorem mem_nullSubmodule_iff_norm_eq_zero (a : A) :
    a ∈ φ.nullSubmodule ↔ ‖φ.toPreGNS a‖ = 0 := by
  rw [nullSubmodule, Submodule.mem_comap, _root_.mem_nullSubmodule_iff,
    LinearEquiv.coe_coe]

/-- The null space is precisely the zero set of the quadratic form. -/
@[simp]
theorem mem_nullSubmodule_iff_apply_star_mul_self_eq_zero (a : A) :
    a ∈ φ.nullSubmodule ↔ φ (star a * a) = 0 := by
  rw [φ.mem_nullSubmodule_iff_norm_eq_zero]
  constructor
  · intro h
    rw [← φ.inner_toPreGNS]
    exact inner_eq_zero_of_right (𝕜 := ℂ) (φ.toPreGNS a) h
  · intro h
    rw [← sq_eq_zero_iff, norm_sq_eq_re_inner (𝕜 := ℂ), φ.inner_toPreGNS, h]
    simp

/-- Membership in the null space is vanishing of all pairings. -/
theorem mem_nullSubmodule (a : A) : a ∈ φ.nullSubmodule ↔ ∀ b, φ (star b * a) = 0 := by
  rw [φ.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    φ.apply_star_mul_self_eq_zero_iff]

/-- The null space is a left ideal, even when the functional is not tracial. -/
theorem mul_mem_nullSubmodule (a : A) {b : A} (hb : b ∈ φ.nullSubmodule) :
    a * b ∈ φ.nullSubmodule := by
  rw [φ.mem_nullSubmodule] at hb ⊢
  intro c
  simpa [mul_assoc] using hb (star a * c)

/-- The algebraic GNS space: the separation quotient of the GNS seminorm, without completion. -/
abbrev GNS := SeparationQuotient φ.PreGNS

/-- The canonical linear map into the algebraic GNS space. -/
def classMap : A →ₗ[ℂ] φ.GNS :=
  (SeparationQuotient.mkCLM ℂ φ.PreGNS).toLinearMap.comp φ.toPreGNS.toLinearMap

/-- The canonical map sends an algebra element to its separation class. -/
theorem classMap_apply (a : A) :
    φ.classMap a = SeparationQuotient.mk (φ.toPreGNS a) := (rfl)

/-- Every vector of the algebraic GNS space is the class of an algebra element. -/
theorem classMap_surjective : Function.Surjective φ.classMap :=
  SeparationQuotient.surjective_mk.comp φ.toPreGNS.surjective

/-- Two algebra elements have the same class exactly when their difference is null. -/
theorem classMap_eq_classMap_iff (a b : A) :
    φ.classMap a = φ.classMap b ↔ a - b ∈ φ.nullSubmodule := by
  rw [← sub_eq_zero, ← map_sub]
  rw [φ.classMap_apply, φ.mem_nullSubmodule_iff_norm_eq_zero]
  exact SeparationQuotient.mk_eq_zero_iff

/-- Linear maps out of the GNS space are determined by their values on algebra classes. -/
@[ext]
theorem classMap_ext {E : Type*} [AddCommMonoid E] [Module ℂ E]
    {f g : φ.GNS →ₗ[ℂ] E} (h : ∀ a, f (φ.classMap a) = g (φ.classMap a)) : f = g :=
  LinearMap.ext <| φ.classMap_surjective.forall.mpr h

/-- The class of an element is zero exactly when its square value is zero. -/
@[simp]
theorem classMap_eq_zero_iff (a : A) : φ.classMap a = 0 ↔ φ (star a * a) = 0 := by
  rw [← map_zero φ.classMap, φ.classMap_eq_classMap_iff, sub_zero,
    φ.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero]

/-- Inner products of classes are the original square pairings. -/
@[simp]
theorem inner_classMap (a b : A) :
    ⟪φ.classMap a, φ.classMap b⟫_ℂ = φ (star a * b) :=
  SeparationQuotient.inner_mk_mk (φ.toPreGNS a) (φ.toPreGNS b)

/-- The GNS norm of a class is determined by the quadratic form. -/
theorem norm_classMap_sq (a : A) : ‖φ.classMap a‖ ^ 2 = (φ (star a * a)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), φ.inner_classMap, RCLike.re_to_complex]

/-- Left multiplication on the algebraic GNS space, without a continuity assertion. -/
def leftMul (a : A) : Module.End ℂ φ.GNS where
  toFun := SeparationQuotient.lift
    (fun b => φ.classMap (a * φ.toPreGNS.symm b)) (by
      intro b c h
      rw [φ.classMap_eq_classMap_iff, ← mul_sub]
      apply φ.mul_mem_nullSubmodule
      rw [φ.mem_nullSubmodule_iff_norm_eq_zero]
      simpa [dist_eq_norm] using h.dist_eq_zero)
  map_add' := by
    intro x y
    obtain ⟨b, rfl⟩ := φ.classMap_surjective x
    obtain ⟨c, rfl⟩ := φ.classMap_surjective y
    -- On representatives, the quotient lift computes to multiplication.
    change φ.classMap (a * (b + c)) = φ.classMap (a * b) + φ.classMap (a * c)
    simp [mul_add]
  map_smul' := by
    intro r x
    obtain ⟨b, rfl⟩ := φ.classMap_surjective x
    -- On representatives, the quotient lift computes to multiplication.
    change φ.classMap (a * (r • b)) = r • φ.classMap (a * b)
    simp [mul_smul_comm]

/-- Left multiplication acts on classes by the original multiplication. -/
@[simp]
theorem leftMul_classMap (a b : A) :
    φ.leftMul a (φ.classMap b) = φ.classMap (a * b) := (rfl)

/-- The non-unital algebra acts on its GNS space by algebraic linear endomorphisms. -/
def nonUnitalRepresentation : A →ₙₐ[ℂ] Module.End ℂ φ.GNS where
  toFun := φ.leftMul
  map_mul' a b := by
    apply φ.classMap_ext
    intro c
    simp [mul_apply_eq_comp, mul_assoc]
  map_zero' := by
    apply φ.classMap_ext
    intro b
    simp
  map_add' a b := by
    apply φ.classMap_ext
    intro c
    simp [add_mul]
  map_smul' r a := by
    apply φ.classMap_ext
    intro b
    simp [smul_mul_assoc]

/-- The non-unital representation acts on classes by left multiplication. -/
@[simp]
theorem nonUnitalRepresentation_classMap (a b : A) :
    φ.nonUnitalRepresentation a (φ.classMap b) = φ.classMap (a * b) := (rfl)

/-- Left multiplication respects adjoints on the algebraic GNS domain. -/
theorem inner_leftMul (a : A) (x y : φ.GNS) :
    ⟪φ.leftMul a x, y⟫_ℂ = ⟪x, φ.leftMul (star a) y⟫_ℂ := by
  obtain ⟨b, rfl⟩ := φ.classMap_surjective x
  obtain ⟨c, rfl⟩ := φ.classMap_surjective y
  simp [mul_assoc]

end StarPositiveFunctional

end NonUnital

namespace StarPositiveFunctional

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  (φ : StarPositiveFunctional A)

/-- A positive functional preserves the involution. -/
@[simp]
theorem map_star (a : A) : φ (star a) = star (φ a) := by
  simpa using (φ.star_apply_star_mul 1 a).symm

/-- The algebra acts on its algebraic GNS space by left multiplication.
The endomorphisms are algebraic linear maps and are not asserted to be continuous. -/
def representation : A →ₐ[ℂ] Module.End ℂ φ.GNS where
  __ := φ.nonUnitalRepresentation
  map_one' := by
    apply φ.classMap_ext
    intro b
    simp
  commutes' r := by
    apply φ.classMap_ext
    intro b
    simp [Algebra.algebraMap_eq_smul_one]

/-- The action on classes is left multiplication. -/
@[simp]
theorem representation_classMap (a b : A) :
    φ.representation a (φ.classMap b) = φ.classMap (a * b) := (rfl)

/-- The representation respects adjoints on the algebraic GNS domain. -/
theorem inner_representation (a : A) (x y : φ.GNS) :
    ⟪φ.representation a x, y⟫_ℂ = ⟪x, φ.representation (star a) y⟫_ℂ :=
  φ.inner_leftMul a x y

/-- The canonical cyclic vector is the class of the unit. -/
def cyclicVector : φ.GNS := φ.classMap 1

/-- The cyclic vector is the class of the unit. -/
theorem cyclicVector_def : φ.cyclicVector = φ.classMap 1 := (rfl)

/-- Acting on the cyclic vector produces the class of the acting element. -/
@[simp]
theorem representation_cyclicVector (a : A) :
    φ.representation a φ.cyclicVector = φ.classMap a := by
  simp [cyclicVector_def]

/-- The orbit of the canonical vector consists of every vector of the algebraic GNS space. -/
theorem representation_cyclicVector_surjective :
    Function.Surjective (fun a => φ.representation a φ.cyclicVector) := by
  simpa using φ.classMap_surjective

/-- The original functional is the vector functional of its algebraic GNS representation. -/
@[simp]
theorem inner_cyclicVector_classMap (a : A) :
    ⟪φ.cyclicVector, φ.classMap a⟫_ℂ = φ a := by
  simp [cyclicVector_def]

/-- Pairing a class with the cyclic vector evaluates the involution of its representative. -/
@[simp]
theorem inner_classMap_cyclicVector (a : A) :
    ⟪φ.classMap a, φ.cyclicVector⟫_ℂ = φ (star a) := by
  simp [cyclicVector_def]

/-- The square pairing of the cyclic vector is the mass of the functional. -/
@[simp high]
theorem inner_cyclicVector_self : ⟪φ.cyclicVector, φ.cyclicVector⟫_ℂ = φ 1 := by
  rw [cyclicVector_def, φ.inner_classMap]
  simp

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
