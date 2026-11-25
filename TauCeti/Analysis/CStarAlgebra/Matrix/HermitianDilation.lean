/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic

/-!
# The Hermitian dilation of an element of a C⋆-algebra

For an element `x` of a star algebra `A`, the *Hermitian dilation* of `x` is the self-adjoint
`2 × 2` matrix `!![0, x; x⋆, 0]` in `CStarMatrix (Fin 2) (Fin 2) A`. It is additive and real
linear in `x`, its off-diagonal corner recovers `x`, and the product of two dilations is the
diagonal matrix `diag(x y⋆, x⋆ y)`.

Over a C⋆-algebra, the dilation is isometric, and for families `x`, `y` indexed by a finite set

`‖∑ₖ D(xₖ) D(yₖ)‖ = max ‖∑ₖ xₖ yₖ⋆‖ ‖∑ₖ xₖ⋆ yₖ‖`,

where `D` is the dilation. Taking `y = x`, the square function `‖∑ₖ D(xₖ)²‖` of the self-adjoint
family `D(xₖ)` is the larger of the row and column square functions `‖∑ₖ xₖ xₖ⋆‖` and
`‖∑ₖ xₖ⋆ xₖ‖` of `x`. This is how estimates on Rademacher sums `∑ₖ εₖ xₖ` proved for self-adjoint
families in `M₂(A)`, such as the fourth-moment and truncation steps of Pisier's proof of the
noncommutative Khintchine inequality at `p = 1`, apply to arbitrary families in `A`: one proves
them for `D(xₖ)` and reads off the `(0, 1)` entry, which does not increase norms
(`CStarMatrix.norm_entry_le_norm`).

## Main declarations

* `CStarMatrix.hermitianDilation`: the additive map `x ↦ !![0, x; x⋆, 0]`.
* `CStarMatrix.isSelfAdjoint_hermitianDilation`: the dilation is self-adjoint.
* `CStarMatrix.hermitianDilation_mul_hermitianDilation`: `D(x) D(y) = diag(x y⋆, x⋆ y)`.
* `CStarMatrix.norm_hermitianDilation`: `‖D(x)‖ = ‖x‖`.
* `CStarMatrix.norm_sum_hermitianDilation_mul_hermitianDilation`: the norm of `∑ₖ D(xₖ) D(yₖ)`.

## References

* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012),
  §9, proof of Theorem 9.1.
-/

public section

open Matrix

namespace CStarMatrix

section Algebraic

variable {A : Type*} [AddCommMonoid A] [StarAddMonoid A]

/-- The Hermitian dilation `!![0, x; x⋆, 0]` of `x`, a self-adjoint `2 × 2` matrix with `x` in
its `(0, 1)` entry. -/
def hermitianDilation : A →+ CStarMatrix (Fin 2) (Fin 2) A where
  toFun x := ofMatrix !![0, x; star x, 0]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem hermitianDilation_apply (x : A) : hermitianDilation x = ofMatrix !![0, x; star x, 0] :=
  (rfl)

@[simp]
theorem hermitianDilation_apply_zero_zero (x : A) : hermitianDilation x 0 0 = 0 :=
  (rfl)

@[simp]
theorem hermitianDilation_apply_zero_one (x : A) : hermitianDilation x 0 1 = x :=
  (rfl)

@[simp]
theorem hermitianDilation_apply_one_zero (x : A) : hermitianDilation x 1 0 = star x :=
  (rfl)

@[simp]
theorem hermitianDilation_apply_one_one (x : A) : hermitianDilation x 1 1 = 0 :=
  (rfl)

theorem hermitianDilation_injective : Function.Injective (hermitianDilation (A := A)) :=
  fun x y h => by simpa using congrFun₂ h 0 1

@[simp]
theorem hermitianDilation_inj {x y : A} : hermitianDilation x = hermitianDilation y ↔ x = y :=
  hermitianDilation_injective.eq_iff

/-- The Hermitian dilation is self-adjoint. -/
theorem isSelfAdjoint_hermitianDilation (x : A) : IsSelfAdjoint (hermitianDilation x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [star_apply]

/-- The star of a Hermitian dilation is itself, as a rewrite rule for `simp`. -/
@[simp]
theorem star_hermitianDilation (x : A) : star (hermitianDilation x) = hermitianDilation x :=
  (isSelfAdjoint_hermitianDilation x).star_eq

/-- The Hermitian dilation commutes with scalars whose star is trivial, such as real scalars
acting on a complex star algebra. -/
@[simp]
theorem hermitianDilation_smul {R : Type*} [Star R] [TrivialStar R] [SMulZeroClass R A]
    [StarModule R A] (r : R) (x : A) :
    hermitianDilation (r • x) = r • hermitianDilation x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [star_smul]

end Algebraic

/-- The product of two Hermitian dilations is diagonal: `D(x) D(y) = diag(x y⋆, x⋆ y)`. -/
theorem hermitianDilation_mul_hermitianDilation {A : Type*} [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] (x y : A) :
    hermitianDilation x * hermitianDilation y = ofMatrix (diagonal ![x * star y, star x * y]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

section Norm

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For finite families `x`, `y`, the sum `∑ₖ D(xₖ) D(yₖ)` of products of Hermitian dilations
has norm `max ‖∑ₖ xₖ yₖ⋆‖ ‖∑ₖ xₖ⋆ yₖ‖`. For `y = x` this is the larger of the row and column
square functions of `x`. -/
theorem norm_sum_hermitianDilation_mul_hermitianDilation {ι : Type*} (s : Finset ι)
    (x y : ι → A) :
    ‖∑ k ∈ s, hermitianDilation (x k) * hermitianDilation (y k)‖ =
      max ‖∑ k ∈ s, x k * star (y k)‖ ‖∑ k ∈ s, star (x k) * y k‖ := by
  have h : ∑ k ∈ s, hermitianDilation (x k) * hermitianDilation (y k) =
      ofMatrix (diagonal ![∑ k ∈ s, x k * star (y k), ∑ k ∈ s, star (x k) * y k]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sum_apply, hermitianDilation_mul_hermitianDilation]
  rw [h, norm_ofMatrix_diagonal_fin_two]

/-- The Hermitian dilation is isometric: `‖!![0, x; x⋆, 0]‖ = ‖x‖`. -/
@[simp]
theorem norm_hermitianDilation (x : A) : ‖hermitianDilation x‖ = ‖x‖ := by
  have h := CStarRing.norm_star_mul_self (x := hermitianDilation x)
  rw [star_hermitianDilation, hermitianDilation_mul_hermitianDilation,
    norm_ofMatrix_diagonal_fin_two, CStarRing.norm_self_mul_star, CStarRing.norm_star_mul_self,
    max_self] at h
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 h.symm

end Norm

end CStarMatrix
