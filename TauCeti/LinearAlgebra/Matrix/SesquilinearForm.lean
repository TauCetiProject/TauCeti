/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Algebra.Order.Star.Basic

/-!
# The standard sesquilinear form with a specified automorphism

The form `sesquilinearForm σ` is linear in its first argument and `σ`-semilinear in its
second: `h(x,y) = ∑ i, x i * σ (y i)`. It identifies the second coordinate space
semilinearly with the dual of the first. When `σ` is involutive, the form has Hermitian
symmetry. This orientation is useful for Hermitian duals of codes over finite fields.

This identification with the dual gives a nondegenerate pairing for studying orthogonality
in finite coordinate spaces.

The API is in `RingEquiv`: use `σ.sesquilinearForm`, or `RingEquiv.sesquilinearForm σ`.

For a module with a finite basis `b`, Mathlib's `Matrix.toLinearMapₛₗ₂ σ b b 1` is the
sesquilinear form, `σ`-semilinear in its first argument, for which `b` is orthonormal. In
coordinates it is `∑ i, σ (x i) * y i` (`Matrix.toLinearMapₛₗ₂_one_apply`). For complex
conjugation, or any star ring, it is Hermitian (`Matrix.star_toLinearMapₛₗ₂_one_apply`), and over
a star-ordered ring without zero divisors it is positive definite
(`Matrix.toLinearMapₛₗ₂_one_self_nonneg`, `Matrix.toLinearMapₛₗ₂_one_self_eq_zero_iff`). This is
the Hermitian metric making a chosen basis orthonormal, for instance the increasing wedge basis of
an exterior algebra.
-/

public section

namespace RingEquiv

open Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The standard sesquilinear form, linear in the first argument and twisted by `σ`
in the second. It is Hermitian when `σ` is involutive. -/
noncomputable def sesquilinearForm (σ : R ≃+* R) :
    (ι → R) →ₗ[R] (ι → R) →ₛₗ[(σ : R →+* R)] R := by
  classical
  exact Matrix.toLinearMapₛₗ₂' R (RingHom.id R) (σ : R →+* R) 1

/-- The standard sesquilinear form evaluates as the coordinate sum `∑ i, x i * σ (y i)`. -/
@[simp]
theorem sesquilinearForm_apply (σ : R ≃+* R) (x y : ι → R) :
    sesquilinearForm σ x y = ∑ i, x i * σ (y i) := by
  classical
  unfold sesquilinearForm
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp [Matrix.one_apply, smul_eq_mul]

/-- Swapping the arguments and inverting the automorphism applies the inverse automorphism
to the value of the standard sesquilinear form. -/
theorem sesquilinearForm_symm_swap (σ : R ≃+* R) (x y : ι → R) :
    sesquilinearForm σ.symm y x = σ.symm (sesquilinearForm σ x y) := by
  simp [sesquilinearForm_apply, mul_comm]

/-- For an involutive automorphism, swapping the arguments conjugates the value. -/
theorem sesquilinearForm_swap (σ : R ≃+* R) (hσ : Function.Involutive σ) (x y : ι → R) :
    sesquilinearForm σ y x = σ (sesquilinearForm σ x y) := by
  simp only [sesquilinearForm_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hσ (y i), mul_comm]

/-- The standard sesquilinear form is nondegenerate over any commutative semiring. -/
theorem nondegenerate_sesquilinearForm (σ : R ≃+* R) :
    (sesquilinearForm σ (ι := ι)).Nondegenerate := by
  classical
  constructor
  · intro x hx
    ext i
    simpa [sesquilinearForm_apply, Pi.single_apply] using hx (Pi.single i 1)
  · intro y hy
    ext i
    have h : σ (y i) = 0 := by
      simpa [sesquilinearForm_apply, Pi.single_apply] using hy (Pi.single i 1)
    exact σ.injective (h.trans σ.map_zero.symm)

/-- The second argument of the standard sesquilinear form identifies the coordinate space
with its dual. -/
theorem sesquilinearForm_flip_bijective (σ : R ≃+* R) :
    Function.Bijective (sesquilinearForm σ (ι := ι)).flip := by
  classical
  constructor
  · intro x y h
    ext i
    apply σ.injective
    have := LinearMap.congr_fun h (Pi.single i 1)
    simpa [sesquilinearForm_apply, Pi.single_apply] using this
  · intro f
    obtain ⟨y, rfl⟩ := (dotProductEquiv R ι).surjective f
    refine ⟨fun i ↦ σ.symm (y i), ?_⟩
    ext x
    simp [sesquilinearForm_apply, dotProduct, mul_comm]

end RingEquiv

namespace Matrix

variable {R M n : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype n]
  [DecidableEq n] (b : Module.Basis n R M)

/-- **The sesquilinear form of the identity matrix in coordinates**: for a basis `b`,
`toLinearMapₛₗ₂ σ b b 1 x y = ∑ i, σ (x i) * y i`, the form for which `b` is orthonormal. -/
theorem toLinearMapₛₗ₂_one_apply (σ : R →+* R) (x y : M) :
    toLinearMapₛₗ₂ σ b b (1 : Matrix n n R) x y = ∑ i, σ (b.repr x i) * b.repr y i := by
  simp [toLinearMapₛₗ₂_apply, one_apply, smul_eq_mul]

/-- For the form making a basis orthonormal, the functional attached to a basis vector is its
coordinate functional. -/
theorem toLinearMapₛₗ₂_one_basis_eq_coord (σ : R →+* R) (i : n) :
    toLinearMapₛₗ₂ σ b b (1 : Matrix n n R) (b i) = b.coord i := by
  refine b.ext fun j ↦ ?_
  simp [one_apply, Finsupp.single_apply, eq_comm]

variable [StarRing R]

/-- **The orthonormal-basis form is Hermitian**: for complex conjugation, or the star of any star
ring, swapping the arguments of `toLinearMapₛₗ₂ (starRingEnd R) b b 1` conjugates its value. -/
theorem star_toLinearMapₛₗ₂_one_apply (x y : M) :
    star (toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix n n R) x y) =
      toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix n n R) y x := by
  simp only [toLinearMapₛₗ₂_one_apply, star_sum, star_mul, starRingEnd_apply, star_star]

/-- **The orthonormal-basis form is positive semidefinite** over a star-ordered ring. -/
theorem toLinearMapₛₗ₂_one_self_nonneg [PartialOrder R] [StarOrderedRing R] (x : M) :
    0 ≤ toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix n n R) x x := by
  rw [toLinearMapₛₗ₂_one_apply]
  exact Finset.sum_nonneg fun i _ ↦ star_mul_self_nonneg _

/-- **The orthonormal-basis form is definite** over a star-ordered ring without zero divisors:
`toLinearMapₛₗ₂ (starRingEnd R) b b 1 x x = 0` only for `x = 0`. -/
theorem toLinearMapₛₗ₂_one_self_eq_zero_iff [PartialOrder R] [StarOrderedRing R]
    [NoZeroDivisors R] {x : M} :
    toLinearMapₛₗ₂ (starRingEnd R) b b (1 : Matrix n n R) x x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by simp [hx]⟩
  simp only [toLinearMapₛₗ₂_one_apply, starRingEnd_apply] at hx
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ star_mul_self_nonneg _] at hx
  refine b.repr.injective (Finsupp.ext fun i ↦ ?_)
  have hi := hx i (Finset.mem_univ i)
  rw [mul_eq_zero, star_eq_zero, or_self] at hi
  rw [hi, map_zero, Finsupp.coe_zero, Pi.zero_apply]

end Matrix
