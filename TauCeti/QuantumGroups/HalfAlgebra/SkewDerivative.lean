/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Free
public import TauCeti.Algebra.OreExtension.Triangular

import TauCeti.Algebra.FreeAlgebra
import TauCeti.Algebra.Star.Free
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Skew derivatives of the free algebra on the simple generators

Let `T = R⟨θᵢ : i ∈ I⟩` be the free algebra on the simple generators of a quantum group and let
`χ : I → I → R` record a bicharacter on the simple roots, `χ i j = χ(αᵢ, αⱼ)`. For a word `x` of
multidegree `β = αᵢ₁ + ⋯ + αᵢₙ` put `χ(αᵢ, β) = χ i i₁ ⋯ χ i iₙ`. Lusztig's skew derivatives are the
linear maps `Lᵢ`, `Rᵢ` of `T` with `Lᵢ θⱼ = Rᵢ θⱼ = δᵢⱼ` and, for homogeneous `x` and `y`,

`Lᵢ (x y) = Lᵢ x · y + χ(αᵢ, |x|) x · Lᵢ y`,
`Rᵢ (x y) = χ(αᵢ, |y|) Rᵢ x · y + x · Rᵢ y`.

The factor `χ(αᵢ, |x|)` is the action on `x` of the diagonal scaling `θⱼ ↦ χ i j θⱼ`, so `Lᵢ` is a
skew derivation of `T` twisted by an algebra endomorphism, and `Rᵢ` is its mirror image under word
reversal. They are the components of the braided coproduct `r(x)` along `θᵢ ⊗ T` and `T ⊗ θᵢ`,
and they compute the bilinear form whose radical defines the positive part `f` of the quantum
group.

## Main definitions

* `TauCeti.freeHalfScale c`: the diagonal scaling `θⱼ ↦ cⱼ θⱼ` of the free algebra, through which
  the torus acts.
* `TauCeti.freeRemove χ i`: the left skew derivative `Lᵢ`, a `TauCeti.SigmaDerivation` for the
  scaling `freeHalfScale (χ i)`.
* `TauCeti.freeRemoveRight χ i`: the right skew derivative `Rᵢ`, the conjugate of `Lᵢ` by word
  reversal.

## Main results

* `TauCeti.freeRemove_ι_mul`: `Lᵢ (θⱼ x) = δᵢⱼ x + χ i j θⱼ Lᵢ x`, the recursion on words.
* `TauCeti.freeRemoveRight_mul`: the twisted Leibniz rule of `Rᵢ`.
* `TauCeti.freeRemove_freeHalfScale`, `TauCeti.freeRemoveRight_freeHalfScale`: the skew
  derivatives are homogeneous of degree `-αᵢ` for every diagonal scaling.
* `TauCeti.algebraMapInv_freeRemoveRight`: `Lᵢ` and `Rᵢ` have the same constant term.
* `TauCeti.freeRemove_freeRemoveRight`: `Lᵢ Rⱼ = Rⱼ Lᵢ` when `χ i j = χ j i`.
* `TauCeti.freeRemove_ι_pow_succ`: in rank one, `Lᵢ θᵢⁿ⁺¹ = (1 + χ i i + ⋯ + χ i iⁿ) θᵢⁿ`.

## Implementation notes

The left skew derivative is the upper-right entry of the algebra map
`x ↦ !![freeHalfScale (χ i) x, Lᵢ x; 0, x]` into `2 × 2` matrices, produced by the universal
property of the free algebra (`TauCeti.SigmaDerivation.ofMatrix`), so its Leibniz rule holds by
construction. The right skew derivative is defined as `x ↦ star (Lᵢ (star x))`, where `star` is
Mathlib's word reversal on the free algebra.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §1.2.
* I. Heckenberger, *Lusztig isomorphisms for Drinfel'd doubles of bosonizations of Nichols
  algebras of diagonal type*, J. Algebra 323 (2010), Lemmas 4.15 and 4.16.
-/

public section

noncomputable section

namespace TauCeti

open FreeAlgebra

variable {R I : Type*} [CommSemiring R]

/-! ### Diagonal scalings -/

/-- The diagonal scaling `θⱼ ↦ cⱼ θⱼ` of the free algebra on the simple generators. On a word of
multidegree `β` it acts by the scalar `c^β`. -/
def freeHalfScale (c : I → R) : FreeAlgebra R I →ₐ[R] FreeAlgebra R I :=
  lift R fun j => c j • ι R j

@[simp]
theorem freeHalfScale_ι (c : I → R) (j : I) : freeHalfScale c (ι R j) = c j • ι R j :=
  lift_ι_apply _ _

@[simp]
theorem freeHalfScale_one : freeHalfScale (1 : I → R) = AlgHom.id R (FreeAlgebra R I) := by
  ext; simp

theorem freeHalfScale_comp_freeHalfScale (c d : I → R) :
    (freeHalfScale c).comp (freeHalfScale d) = freeHalfScale (c * d) := by
  ext; simp [smul_smul, mul_comm]

@[simp]
theorem freeHalfScale_freeHalfScale (c d : I → R) (x : FreeAlgebra R I) :
    freeHalfScale c (freeHalfScale d x) = freeHalfScale (c * d) x :=
  DFunLike.congr_fun (freeHalfScale_comp_freeHalfScale c d) x

/-- Two diagonal scalings commute. -/
theorem freeHalfScale_comm (c d : I → R) (x : FreeAlgebra R I) :
    freeHalfScale c (freeHalfScale d x) = freeHalfScale d (freeHalfScale c x) := by
  rw [freeHalfScale_freeHalfScale, freeHalfScale_freeHalfScale, mul_comm]

/-- A diagonal scaling does not change the constant term. -/
@[simp]
theorem algebraMapInv_freeHalfScale (c : I → R) (x : FreeAlgebra R I) :
    algebraMapInv (freeHalfScale c x) = algebraMapInv x :=
  DFunLike.congr_fun (show algebraMapInv.comp (freeHalfScale c) = algebraMapInv by ext; simp) x

/-- Diagonal scalings commute with word reversal. -/
theorem star_freeHalfScale (c : I → R) (x : FreeAlgebra R I) :
    star (freeHalfScale c x) = freeHalfScale c (star x) := by
  induction x using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 j => simp [Algebra.smul_def, Algebra.commutes]
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

/-! ### The left skew derivative -/

variable [DecidableEq I]

/-- The algebra map `x ↦ !![freeHalfScale (χ i) x, Lᵢ x; 0, x]` whose upper-right entry is the left
skew derivative `Lᵢ`. -/
private def removeMatrix (χ : I → I → R) (i : I) :
    FreeAlgebra R I →ₐ[R] Matrix (Fin 2) (Fin 2) (FreeAlgebra R I) :=
  lift R fun j => !![χ i j • ι R j, if i = j then 1 else 0; 0, ι R j]

private theorem removeMatrix_shape (χ : I → I → R) (i : I) (x : FreeAlgebra R I) :
    removeMatrix χ i x 0 0 = freeHalfScale (χ i) x ∧ removeMatrix χ i x 1 0 = 0 ∧
      removeMatrix χ i x 1 1 = x := by
  induction x using FreeAlgebra.induction with
  | grade0 r => simp [Matrix.algebraMap_matrix_apply]
  | grade1 j => simp [removeMatrix]
  | mul x y hx hy =>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]
  | add x y hx hy => simp [hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]

/-- The left skew derivative `Lᵢ` of the free algebra: the skew derivation for the scaling
`θⱼ ↦ χ i j θⱼ` with `Lᵢ θⱼ = δᵢⱼ`. On homogeneous elements its Leibniz rule reads
`Lᵢ (x y) = Lᵢ x · y + χ(αᵢ, |x|) x · Lᵢ y`. -/
def freeRemove (χ : I → I → R) (i : I) : SigmaDerivation (freeHalfScale (χ i)) :=
  SigmaDerivation.ofMatrix (removeMatrix χ i) (fun x => (removeMatrix_shape χ i x).1)
    (fun x => (removeMatrix_shape χ i x).2.2)

variable (χ : I → I → R)

@[simp]
theorem freeRemove_ι (i j : I) : freeRemove χ i (ι R j) = if i = j then 1 else 0 := by
  simp [freeRemove, removeMatrix]

@[simp]
theorem freeRemove_algebraMap (i : I) (r : R) :
    freeRemove χ i (algebraMap R (FreeAlgebra R I) r) = 0 := by
  simp [freeRemove, Matrix.algebraMap_matrix_apply]

/-- The recursion of the left skew derivative on words:
`Lᵢ (θⱼ x) = δᵢⱼ x + χ i j θⱼ Lᵢ x`. -/
theorem freeRemove_ι_mul (i j : I) (x : FreeAlgebra R I) :
    freeRemove χ i (ι R j * x) =
      (if i = j then x else 0) + χ i j • (ι R j * freeRemove χ i x) := by
  rw [SigmaDerivation.leibniz, freeHalfScale_ι, freeRemove_ι, smul_mul_assoc, add_comm]
  split_ifs <;> simp

/-- The left skew derivatives are homogeneous of degree `-αᵢ`: for every diagonal scaling,
`Lᵢ (c · x) = cᵢ (c · Lᵢ x)`. -/
theorem freeRemove_freeHalfScale (i : I) (c : I → R) (x : FreeAlgebra R I) :
    freeRemove χ i (freeHalfScale c x) = c i • freeHalfScale c (freeRemove χ i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 j =>
    simp only [freeHalfScale_ι, map_smul, freeRemove_ι]
    split_ifs with h
    · simp [h]
    · simp
  | mul x y hx hy =>
    simp only [map_mul, SigmaDerivation.leibniz, hx, hy, map_add, smul_add, mul_smul_comm,
      smul_mul_assoc, freeHalfScale_comm c (χ i)]
  | add x y hx hy => simp [hx, hy]

/-- In rank one, `Lᵢ θᵢⁿ⁺¹ = (1 + χ i i + ⋯ + χ i iⁿ) θᵢⁿ`. -/
theorem freeRemove_ι_pow_succ (i : I) (n : ℕ) :
    freeRemove χ i (ι R i ^ (n + 1)) = (∑ m ∈ Finset.range (n + 1), χ i i ^ m) • ι R i ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', freeRemove_ι_mul, ih, Finset.sum_range_succ' _ (n + 1)]
    simp [smul_smul, Finset.mul_sum, add_smul, ← pow_succ', add_comm]

/-! ### The right skew derivative -/

/-- The right skew derivative `Rᵢ` of the free algebra, the conjugate of the left skew derivative
by word reversal: `Rᵢ θⱼ = δᵢⱼ` and, on homogeneous elements,
`Rᵢ (x y) = χ(αᵢ, |y|) Rᵢ x · y + x · Rᵢ y`. -/
def freeRemoveRight (i : I) : FreeAlgebra R I →ₗ[R] FreeAlgebra R I where
  toFun x := star (freeRemove χ i (star x))
  map_add' x y := by simp
  map_smul' r x := by simp

theorem freeRemoveRight_eq_star (i : I) (x : FreeAlgebra R I) :
    freeRemoveRight χ i x = star (freeRemove χ i (star x)) :=
  (rfl)

/-- Word reversal exchanges the two skew derivatives. -/
theorem freeRemove_star (i : I) (x : FreeAlgebra R I) :
    freeRemove χ i (star x) = star (freeRemoveRight χ i x) := by
  rw [freeRemoveRight_eq_star, star_star]

/-- The mirror of `freeRemove_star`: `Rᵢ (star x) = star (Lᵢ x)`. -/
theorem freeRemoveRight_star (i : I) (x : FreeAlgebra R I) :
    freeRemoveRight χ i (star x) = star (freeRemove χ i x) := by
  rw [freeRemoveRight_eq_star, star_star]

@[simp]
theorem freeRemoveRight_ι (i j : I) : freeRemoveRight χ i (ι R j) = if i = j then 1 else 0 := by
  rw [freeRemoveRight_eq_star, star_ι, freeRemove_ι]
  split_ifs <;> simp

@[simp]
theorem freeRemoveRight_algebraMap (i : I) (r : R) :
    freeRemoveRight χ i (algebraMap R (FreeAlgebra R I) r) = 0 := by
  simp [freeRemoveRight_eq_star]

@[simp]
theorem freeRemoveRight_one (i : I) : freeRemoveRight χ i 1 = 0 := by
  simp [freeRemoveRight_eq_star]

/-- The twisted Leibniz rule of the right skew derivative:
`Rᵢ (x y) = x Rᵢ y + Rᵢ x · (χ i) · y`, where `(χ i) · y` is the scaling `θⱼ ↦ χ i j θⱼ`. -/
theorem freeRemoveRight_mul (i : I) (x y : FreeAlgebra R I) :
    freeRemoveRight χ i (x * y) =
      x * freeRemoveRight χ i y + freeRemoveRight χ i x * freeHalfScale (χ i) y := by
  simp [freeRemoveRight_eq_star, SigmaDerivation.leibniz, star_freeHalfScale, add_comm]

/-- The recursion of the right skew derivative on words:
`Rᵢ (x θⱼ) = δᵢⱼ x + χ i j Rᵢ x θⱼ`. -/
theorem freeRemoveRight_mul_ι (i j : I) (x : FreeAlgebra R I) :
    freeRemoveRight χ i (x * ι R j) =
      (if i = j then x else 0) + χ i j • (freeRemoveRight χ i x * ι R j) := by
  rw [freeRemoveRight_mul, freeRemoveRight_ι, freeHalfScale_ι, mul_smul_comm]
  split_ifs <;> simp

/-- The right skew derivatives are homogeneous of degree `-αᵢ`: for every diagonal scaling,
`Rᵢ (c · x) = cᵢ (c · Rᵢ x)`. -/
theorem freeRemoveRight_freeHalfScale (i : I) (c : I → R) (x : FreeAlgebra R I) :
    freeRemoveRight χ i (freeHalfScale c x) = c i • freeHalfScale c (freeRemoveRight χ i x) := by
  rw [freeRemoveRight_eq_star, freeRemoveRight_eq_star, star_freeHalfScale,
    freeRemove_freeHalfScale, FreeAlgebra.star_smul, star_freeHalfScale]

/-- The two skew derivatives have the same constant term: both read off the coefficient of `θᵢ`. -/
theorem algebraMapInv_freeRemoveRight (i : I) (x : FreeAlgebra R I) :
    algebraMapInv (freeRemoveRight χ i x) = algebraMapInv (freeRemove χ i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 j =>
    simp only [freeRemoveRight_ι, freeRemove_ι]
  | mul x y hx hy =>
    simp [freeRemoveRight_mul, SigmaDerivation.leibniz, hx, hy, mul_comm]
  | add x y hx hy => simp [hx, hy]

/-! ### Commutation of the two skew derivatives -/

/-- **The left and right skew derivatives commute**: `Lᵢ Rⱼ = Rⱼ Lᵢ` whenever
`χ i j = χ j i`. -/
theorem freeRemove_freeRemoveRight {i j : I} (h : χ i j = χ j i) (x : FreeAlgebra R I) :
    freeRemove χ i (freeRemoveRight χ j x) = freeRemoveRight χ j (freeRemove χ i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 k =>
    simp only [freeRemoveRight_ι, freeRemove_ι]
    split_ifs <;> simp
  | mul x y hx hy =>
    simp only [freeRemoveRight_mul, SigmaDerivation.leibniz, map_add, freeRemove_freeHalfScale,
      freeRemoveRight_freeHalfScale, hx, hy, h, mul_smul_comm, smul_mul_assoc]
    abel
  | add x y hx hy => simp [hx, hy]

end TauCeti
