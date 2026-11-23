/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.QuantumGroups.HalfAlgebra.Pairing

import Mathlib.LinearAlgebra.Quotient.Bilinear
import TauCeti.Algebra.FreeAlgebra

/-!
# The half quantum algebra

For a symmetric matrix `χ` over a commutative ring, `Half χ hχ` is the free algebra on the
simple generators modulo the radical of `freePairing χ`. Its pairing is symmetric and
nondegenerate, and its left and right skew derivatives descend from the free algebra.
The construction works over arbitrary commutative coefficient rings and symmetric parameter
matrices.

The normalization is that of `freePairing`: the simple generators have pairing one with
themselves. The symmetry proof is a parameter of the quotient so that its two-sided ideal
instance is available to callers. The caller's `DecidableEq I` is retained throughout.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Birkhäuser, 1993, §1.2.
* I. Heckenberger, *Lusztig isomorphisms for Drinfel'd doubles of bosonizations of Nichols
  algebras*, Journal of Algebra 323 (2010), 2130–2182, for skew derivatives.
-/

public section

noncomputable section

namespace TauCeti

open FreeAlgebra

section Ideal

variable {R I : Type*} [CommSemiring R] [DecidableEq I]
variable (χ : I → I → R) (hχ : ∀ i j, χ i j = χ j i)

/-- The radical of the free pairing as an ideal. The symmetry parameter supplies right stability
when constructing the algebra quotient. -/
def halfIdeal (_hχ : ∀ i j, χ i j = χ j i) : Ideal (FreeAlgebra R I) where
  carrier := halfRadical χ
  zero_mem' := (halfRadical χ).zero_mem
  add_mem' := (halfRadical χ).add_mem
  smul_mem' x _ hy := mul_mem_halfRadical_left x hy

/-- Membership in the ideal is membership in the radical of the free pairing. -/
@[simp]
theorem mem_halfIdeal {x : FreeAlgebra R I} :
    x ∈ halfIdeal χ hχ ↔ x ∈ halfRadical χ := Iff.rfl

instance : (halfIdeal χ hχ).IsTwoSided where
  mul_mem_of_left y hx := mul_mem_halfRadical_right hχ hx y

end Ideal

variable {R I : Type*} [CommRing R] [DecidableEq I]
variable (χ : I → I → R) (hχ : ∀ i j, χ i j = χ j i)

/-- The half quantum algebra, the free algebra modulo the radical of its pairing.
The quotient presentation exposes the native algebra and module instances. -/
abbrev Half := FreeAlgebra R I ⧸ halfIdeal χ hχ

/-- The canonical algebra map to the half quantum algebra. -/
def halfMk : FreeAlgebra R I →ₐ[R] Half χ hχ :=
  Ideal.Quotient.mkₐ R (halfIdeal χ hχ)

/-- A simple generator of the half quantum algebra. -/
def halfGenerator (i : I) : Half χ hχ := halfMk χ hχ (ι R i)

/-- The quotient map sends a free generator to the corresponding simple generator. -/
@[simp]
theorem halfMk_ι (i : I) : halfMk χ hχ (ι R i) = halfGenerator χ hχ i := by rfl

/-- Every element of the half algebra has a free-algebra representative. -/
theorem halfMk_surjective : Function.Surjective (halfMk χ hχ) :=
  Ideal.Quotient.mkₐ_surjective R (halfIdeal χ hχ)

/-- A representative vanishes precisely when it is in the radical. -/
@[simp]
theorem halfMk_eq_zero_iff (x : FreeAlgebra R I) :
    halfMk χ hχ x = 0 ↔ x ∈ halfRadical χ :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Two representatives agree precisely when their difference is in the radical. -/
theorem halfMk_eq_halfMk_iff (x y : FreeAlgebra R I) :
    halfMk χ hχ x = halfMk χ hχ y ↔ x - y ∈ halfRadical χ :=
  Ideal.Quotient.mk_eq_mk_iff_sub_mem x y

/-- The algebra universal property: algebra maps annihilating the radical descend. -/
def halfLift {A : Type*} [Semiring A] [Algebra R A] (f : FreeAlgebra R I →ₐ[R] A)
    (hf : ∀ x ∈ halfRadical χ, f x = 0) : Half χ hχ →ₐ[R] A :=
  Ideal.Quotient.liftₐ (halfIdeal χ hχ) f hf

/-- The descended algebra map has the prescribed value on representatives. -/
@[simp]
theorem halfLift_halfMk {A : Type*} [Semiring A] [Algebra R A]
    (f : FreeAlgebra R I →ₐ[R] A) (hf : ∀ x ∈ halfRadical χ, f x = 0)
    (x : FreeAlgebra R I) : halfLift χ hχ f hf (halfMk χ hχ x) = f x :=
  Ideal.Quotient.lift_mk _ _ _

/-- A descended algebra map acts on the simple generators by the original free-algebra map. -/
@[simp]
theorem halfLift_generator {A : Type*} [Semiring A] [Algebra R A]
    (f : FreeAlgebra R I →ₐ[R] A) (hf : ∀ x ∈ halfRadical χ, f x = 0) (i : I) :
    halfLift χ hχ f hf (halfGenerator χ hχ i) = f (ι R i) :=
  halfLift_halfMk χ hχ f hf (ι R i)

/-- Algebra maps out of the half algebra are determined by their free representatives. -/
theorem half_algHom_ext {A : Type*} [Semiring A] [Algebra R A]
    {f g : Half χ hχ →ₐ[R] A} (h : f.comp (halfMk χ hχ) = g.comp (halfMk χ hχ)) :
    f = g := Ideal.Quotient.algHom_ext R h

/-- Algebra maps out of the half algebra are determined by their values on simple generators. -/
@[ext]
theorem half_algHom_ext_generators {A : Type*} [Semiring A] [Algebra R A]
    {f g : Half χ hχ →ₐ[R] A}
    (h : ∀ i, f (halfGenerator χ hχ i) = g (halfGenerator χ hχ i)) : f = g := by
  apply half_algHom_ext χ hχ
  exact FreeAlgebra.hom_ext (funext h)

/-- Constant term descends to the half algebra. -/
def halfAugmentation : Half χ hχ →ₐ[R] R :=
  halfLift χ hχ algebraMapInv fun x hx => by
    simpa using (mem_halfRadical.mp hx) 1

/-- The augmentation of a representative is its constant term. -/
@[simp]
theorem halfAugmentation_halfMk (x : FreeAlgebra R I) :
    halfAugmentation χ hχ (halfMk χ hχ x) = algebraMapInv x := by
  simp [halfAugmentation]

/-- The augmentation vanishes on the simple generators. -/
@[simp]
theorem halfAugmentation_generator (i : I) :
    halfAugmentation χ hχ (halfGenerator χ hχ i) = 0 := by
  rw [halfGenerator, halfAugmentation_halfMk, algebraMapInv_ι]

/-- The symmetric pairing descended from the free pairing.
Both arguments use the scalar restriction of the algebra ideal, giving the native
algebra-quotient module over the coefficient ring. -/
def halfPairing : LinearMap.BilinForm R (Half χ hχ) :=
  (isSymm_freePairing χ hχ).isRefl.liftQ₂ (freePairing χ)
    ((halfIdeal χ hχ).restrictScalars R)
    (fun _ hx => LinearMap.ext fun y => mem_halfRadical.mp hx y)

/-- The descended pairing agrees with the free pairing on representatives. -/
@[simp↓]
theorem halfPairing_halfMk (x y : FreeAlgebra R I) :
    halfPairing χ hχ (halfMk χ hχ x) (halfMk χ hχ y) = freePairing χ x y := by rfl

/-- The descended pairing is symmetric. -/
theorem isSymm_halfPairing : (halfPairing χ hχ).IsSymm := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  obtain ⟨y, rfl⟩ := halfMk_surjective χ hχ y
  exact (isSymm_freePairing χ hχ).eq x y

/-- Quotienting by the radical makes the pairing nondegenerate on both sides. -/
theorem halfPairing_nondegenerate : (halfPairing χ hχ).Nondegenerate := by
  apply (isSymm_halfPairing χ hχ).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  exact (halfMk_eq_zero_iff χ hχ x).mpr
    (mem_halfRadical.mpr fun y => hx (halfMk χ hχ y))

/-- Pairing against one computes the augmentation. -/
@[simp]
theorem halfPairing_one_left (x : Half χ hχ) :
    halfPairing χ hχ 1 x = halfAugmentation χ hχ x := by
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  simpa only [map_one, freePairing_one_left, halfAugmentation_halfMk]
    using halfPairing_halfMk χ hχ 1 x

/-- Pairing with one computes the augmentation. -/
@[simp]
theorem halfPairing_one_right (x : Half χ hχ) :
    halfPairing χ hχ x 1 = halfAugmentation χ hχ x := by
  rw [(isSymm_halfPairing χ hχ).eq, halfPairing_one_left]

/-- The simple generators remain orthonormal in the quotient. -/
@[simp]
theorem halfPairing_generator_generator (i j : I) :
    halfPairing χ hχ (halfGenerator χ hχ i) (halfGenerator χ hχ j) =
      if i = j then 1 else 0 := by
  simpa only [halfGenerator, halfPairing_halfMk] using freePairing_ι_ι χ i j

/-- The quotient preserves the coefficient ring faithfully. -/
theorem half_algebraMap_injective : Function.Injective (algebraMap R (Half χ hχ)) := by
  have h : Function.LeftInverse (halfAugmentation χ hχ) (algebraMap R (Half χ hχ)) :=
    (halfAugmentation χ hχ).commutes
  exact h.injective

/-- Every diagonal scaling of the generators descends to an algebra endomorphism. -/
def halfScale (c : I → R) : Half χ hχ →ₐ[R] Half χ hχ :=
  halfLift χ hχ ((halfMk χ hχ).comp (freeHalfScale c)) fun _ hx =>
    (halfMk_eq_zero_iff χ hχ _).mpr (freeHalfScale_mem_halfRadical c hx)

/-- Diagonal scaling on a free representative. -/
@[simp]
theorem halfScale_halfMk (c : I → R) (x : FreeAlgebra R I) :
    halfScale χ hχ c (halfMk χ hχ x) = halfMk χ hχ (freeHalfScale c x) := by
  exact halfLift_halfMk χ hχ _ _ x

/-- Diagonal scaling multiplies each generator by its chosen coefficient. -/
@[simp]
theorem halfScale_generator (c : I → R) (i : I) :
    halfScale χ hχ c (halfGenerator χ hχ i) = c i • halfGenerator χ hχ i := by
  simp only [halfGenerator, halfScale_halfMk, freeHalfScale_ι, map_smul]

/-- Scaling by one is the identity algebra endomorphism. -/
@[simp]
theorem halfScale_one : halfScale χ hχ (1 : I → R) = AlgHom.id R (Half χ hχ) := by
  apply half_algHom_ext χ hχ
  apply AlgHom.ext
  intro x
  simp

/-- Composition of diagonal scalings is pointwise multiplication of their coefficients. -/
theorem halfScale_comp_halfScale (c d : I → R) :
    (halfScale χ hχ c).comp (halfScale χ hχ d) = halfScale χ hχ (c * d) := by
  apply half_algHom_ext χ hχ
  apply AlgHom.ext
  intro x
  simp [freeHalfScale_freeHalfScale]

/-- Diagonal scaling preserves the augmentation. -/
@[simp]
theorem halfAugmentation_halfScale (c : I → R) (x : Half χ hχ) :
    halfAugmentation χ hχ (halfScale χ hχ c x) = halfAugmentation χ hχ x := by
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  simp

/-- The left skew derivative descended to the radical quotient. -/
def halfRemove (i : I) : SigmaDerivation (halfScale χ hχ (χ i)) where
  toLinearMap := Submodule.mapQ ((halfIdeal χ hχ).restrictScalars R)
    ((halfIdeal χ hχ).restrictScalars R) (freeRemove χ i).toLinearMap
    (fun _ hx => freeRemove_mem_halfRadical (hχ i) hx)
  leibniz' x y := by
    obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
    obtain ⟨y, rfl⟩ := halfMk_surjective χ hχ y
    -- The linear-map field is a `mapQ`, whose values here are classes of free derivatives.
    change halfMk χ hχ (freeRemove χ i (x * y)) =
      halfScale χ hχ (χ i) (halfMk χ hχ x) * halfMk χ hχ (freeRemove χ i y) +
        halfMk χ hχ (freeRemove χ i x) * halfMk χ hχ y
    simp only [SigmaDerivation.leibniz, map_add, map_mul, halfScale_halfMk]
  map_one' := by
    -- Use the class of the free-algebra unit to evaluate the `mapQ` field.
    change halfMk χ hχ (freeRemove χ i 1) = 0
    simp

/-- The right skew derivative descended to the radical quotient. -/
def halfRemoveRight (i : I) : Half χ hχ →ₗ[R] Half χ hχ :=
  Submodule.mapQ ((halfIdeal χ hχ).restrictScalars R)
    ((halfIdeal χ hχ).restrictScalars R) (freeRemoveRight χ i)
    (fun _ hx => freeRemoveRight_mem_halfRadical hx)

/-- The left skew derivative is computed on any free representative. -/
@[simp]
theorem halfRemove_halfMk (i : I) (x : FreeAlgebra R I) :
    halfRemove χ hχ i (halfMk χ hχ x) = halfMk χ hχ (freeRemove χ i x) := by rfl

/-- The right skew derivative is computed on any free representative. -/
@[simp]
theorem halfRemoveRight_halfMk (i : I) (x : FreeAlgebra R I) :
    halfRemoveRight χ hχ i (halfMk χ hχ x) = halfMk χ hχ (freeRemoveRight χ i x) := by rfl

/-- The right skew derivative annihilates the unit. -/
@[simp]
theorem halfRemoveRight_one (i : I) : halfRemoveRight χ hχ i 1 = 0 := by
  simpa using halfRemoveRight_halfMk χ hχ i (1 : FreeAlgebra R I)

/-- The left skew derivative takes its expected value on generators. -/
@[simp]
theorem halfRemove_generator (i j : I) :
    halfRemove χ hχ i (halfGenerator χ hχ j) = if i = j then 1 else 0 := by
  rw [halfGenerator, halfRemove_halfMk, freeRemove_ι]
  split_ifs <;> simp

/-- The right skew derivative takes its expected value on generators. -/
@[simp]
theorem halfRemoveRight_generator (i j : I) :
    halfRemoveRight χ hχ i (halfGenerator χ hχ j) = if i = j then 1 else 0 := by
  rw [halfGenerator, halfRemoveRight_halfMk, freeRemoveRight_ι]
  split_ifs <;> simp

/-- Left multiplication by a generator is adjoint to the left skew derivative. -/
theorem halfPairing_generator_mul_left (i : I) (x y : Half χ hχ) :
    halfPairing χ hχ (halfGenerator χ hχ i * x) y =
      halfPairing χ hχ x (halfRemove χ hχ i y) := by
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  obtain ⟨y, rfl⟩ := halfMk_surjective χ hχ y
  simp only [halfGenerator, ← map_mul, halfPairing_halfMk, halfRemove_halfMk,
    freePairing_ι_mul_left]

/-- Right multiplication by a generator is adjoint to the right skew derivative. -/
theorem halfPairing_mul_generator_left (i : I) (x y : Half χ hχ) :
    halfPairing χ hχ (x * halfGenerator χ hχ i) y =
      halfPairing χ hχ x (halfRemoveRight χ hχ i y) := by
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  obtain ⟨y, rfl⟩ := halfMk_surjective χ hχ y
  simpa only [halfGenerator, ← map_mul, halfPairing_halfMk, halfRemoveRight_halfMk]
    using freePairing_mul_ι_left χ (hχ i) x y

/-- Left and right skew derivatives commute. -/
theorem halfRemove_halfRemoveRight (i j : I) (x : Half χ hχ) :
    halfRemove χ hχ i (halfRemoveRight χ hχ j x) =
      halfRemoveRight χ hχ j (halfRemove χ hχ i x) := by
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  simpa only [halfRemove_halfMk, halfRemoveRight_halfMk]
    using congrArg (halfMk χ hχ) (freeRemove_freeRemoveRight χ (hχ i j) x)

/-- The common kernel of the left skew derivatives consists exactly of scalars. -/
theorem forall_halfRemove_eq_zero_iff (x : Half χ hχ) :
    (∀ i, halfRemove χ hχ i x = 0) ↔
      x = algebraMap R (Half χ hχ) (halfAugmentation χ hχ x) := by
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  simp only [halfRemove_halfMk, halfMk_eq_zero_iff, halfAugmentation_halfMk]
  rw [forall_freeRemove_mem_halfRadical_iff hχ, ← halfMk_eq_zero_iff χ hχ,
    map_sub, AlgHom.commutes, sub_eq_zero]

/-- The common kernel of the right skew derivatives consists exactly of scalars. -/
theorem forall_halfRemoveRight_eq_zero_iff (x : Half χ hχ) :
    (∀ i, halfRemoveRight χ hχ i x = 0) ↔
      x = algebraMap R (Half χ hχ) (halfAugmentation χ hχ x) := by
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  simp only [halfRemoveRight_halfMk, halfMk_eq_zero_iff, halfAugmentation_halfMk]
  have haug : algebraMapInv (star x) = algebraMapInv x := by
    simpa only [star_one, freePairing_one_left] using freePairing_star_star χ hχ 1 x
  have hkernel := forall_freeRemove_mem_halfRadical_iff hχ (x := star x)
  rw [haug, ← star_algebraMap (algebraMapInv x), ← star_sub,
    star_mem_halfRadical_iff hχ] at hkernel
  simp only [freeRemove_star, star_mem_halfRadical_iff hχ] at hkernel
  rw [hkernel, ← halfMk_eq_zero_iff χ hχ, map_sub, AlgHom.commutes, sub_eq_zero]

/-- The right skew Leibniz rule on the half algebra. -/
theorem halfRemoveRight_mul (i : I) (x y : Half χ hχ) :
    halfRemoveRight χ hχ i (x * y) =
      x * halfRemoveRight χ hχ i y + halfRemoveRight χ hχ i x * halfScale χ hχ (χ i) y := by
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  obtain ⟨y, rfl⟩ := halfMk_surjective χ hχ y
  rw [← map_mul, halfRemoveRight_halfMk, freeRemoveRight_mul]
  simp only [map_add, map_mul, halfScale_halfMk, halfRemoveRight_halfMk]

/-- Diagonal scaling intertwines the left derivative with its generator coefficient. -/
theorem halfRemove_halfScale (i : I) (c : I → R) (x : Half χ hχ) :
    halfRemove χ hχ i (halfScale χ hχ c x) = c i • halfScale χ hχ c (halfRemove χ hχ i x) := by
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  simp [freeRemove_freeHalfScale]

/-- Diagonal scaling intertwines the right derivative with its generator coefficient. -/
theorem halfRemoveRight_halfScale (i : I) (c : I → R) (x : Half χ hχ) :
    halfRemoveRight χ hχ i (halfScale χ hχ c x) =
      c i • halfScale χ hχ c (halfRemoveRight χ hχ i x) := by
  obtain ⟨x, rfl⟩ := halfMk_surjective χ hχ x
  simp [freeRemoveRight_freeHalfScale]

end TauCeti
