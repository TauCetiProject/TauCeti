/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Pi.Units

/-!
# Diagonal matrices: products with matrix units, and commutation

This file records generic identities about diagonal matrices. Multiplying a rectangular matrix
unit on both sides by diagonal matrices of the corresponding row and column sizes rescales its one
nonzero entry. And a matrix commuting with a diagonal matrix has no entry away from the diagonal
wherever that diagonal matrix separates two coordinates, so a matrix commuting with a diagonal
matrix of pairwise distinct entries is itself diagonal.

Neither statement needs a unit or an associative multiplication in the entries: the first holds
over a `NonUnitalNonAssocSemiring`, and the second adds commutativity and cancellation by nonzero
elements, which is what forces the off-diagonal entries to vanish.

For linear maps between based modules, the coordinate matrix is diagonal exactly when each source
basis vector maps to the corresponding scalar multiple of the target basis vector.

## Main results

* `TauCeti.diagonal_mul_single_mul_diagonal`: multiplying `Eᵢⱼ(c)` on the left and right by
  diagonal matrices rescales its entry by the corresponding diagonal coefficients.
* `TauCeti.isUnit_diagonal_iff`: a diagonal matrix over a possibly noncommutative semiring is a
  unit exactly when its diagonal is.
* `TauCeti.isUnit_diagonal_snoc_one_iff`: `diagonal (1, …, 1, x)` is a unit exactly when `x` is.
* `TauCeti.apply_eq_zero_of_commute_diagonal`: a matrix commuting with a diagonal matrix has
  vanishing `(i, j)` entry wherever that diagonal matrix separates `i` from `j`.
* `TauCeti.isDiag_of_commute_diagonal`: a matrix commuting with a diagonal matrix of pairwise
  distinct entries is itself diagonal.
* `Module.Basis.toMatrix_eq_diagonal_iff`: a linear map has a specified diagonal matrix in two
  bases exactly when it scales the corresponding basis vectors by the diagonal entries.
-/

public section

open Matrix

namespace TauCeti

variable {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
variable {A : Type*} [NonUnitalNonAssocSemiring A] {i : m} {j : n}

/-- Multiplying a matrix unit on the left and right by diagonal matrices rescales its nonzero
entry by the corresponding diagonal entries. -/
@[simp]
theorem diagonal_mul_single_mul_diagonal {v : m → A} {w : n → A} (c : A) :
    diagonal v * single i j c * diagonal w = single i j (v i * c * w j) := by
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

/-- A diagonal matrix is a unit exactly when its family of diagonal entries is. Unlike Mathlib's
`Matrix.isUnit_diagonal`, the entries need not commute. -/
theorem isUnit_diagonal_iff {R : Type*} [Semiring R] {v : n → R} :
    IsUnit (diagonal v) ↔ IsUnit v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map (diagonalRingHom n R)⟩
  obtain ⟨M, h₁, h₂⟩ := isUnit_iff_exists.1 h
  refine isUnit_iff_exists.2 ⟨fun i ↦ M i i, funext fun i ↦ ?_, funext fun i ↦ ?_⟩
  · simpa [diagonal_mul] using congr_fun₂ h₁ i i
  · simpa [mul_diagonal] using congr_fun₂ h₂ i i

/-- `diagonal (1, …, 1, x)` is a unit exactly when `x` is. -/
theorem isUnit_diagonal_snoc_one_iff {R : Type*} [Semiring R] {d : ℕ} (x : R) :
    IsUnit (diagonal (Fin.snoc (α := fun _ ↦ R) (1 : Fin d → R) x)) ↔ IsUnit x := by
  simp [isUnit_diagonal_iff, Pi.isUnit_iff, Fin.forall_fin_succ']

section Commute

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k : Type*} [NonUnitalNonAssocCommSemiring k] [IsLeftCancelMulZero k]

/-- A matrix commuting with a diagonal matrix has vanishing `(i, j)` entry whenever the diagonal
matrix separates the coordinates `i` and `j`. -/
theorem apply_eq_zero_of_commute_diagonal {t : ι → k} {g : Matrix ι ι k}
    (hg : Commute (Matrix.diagonal t) g) {i j : ι} (hij : t i ≠ t j) : g i j = 0 := by
  have hentry : (Matrix.diagonal t * g) i j = (g * Matrix.diagonal t) i j := by rw [hg.eq]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
  -- `hentry : t i * g i j = g i j * t j`; cancelling `g i j` on the left would give `t i = t j`.
  by_contra h
  exact hij (mul_left_cancel₀ h (by rw [mul_comm (g i j) (t i)]; exact hentry))

/-- **A matrix commuting with a diagonal matrix of pairwise distinct entries is diagonal.** -/
theorem isDiag_of_commute_diagonal {t : ι → k} (ht : Function.Injective t)
    {g : Matrix ι ι k} (hg : Commute (Matrix.diagonal t) g) : g.IsDiag :=
  fun _ _ hij => apply_eq_zero_of_commute_diagonal hg (ht.ne hij)

end Commute

end TauCeti

namespace Module.Basis

/-- A linear map has a specified diagonal matrix in two bases exactly when it scales the
corresponding basis vectors by the diagonal entries. -/
@[simp]
theorem toMatrix_eq_diagonal_iff
    {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (f : M →ₗ[R] N) (c : ι → R) :
    LinearMap.toMatrix b b' f = Matrix.diagonal c ↔ ∀ i, f (b i) = c i • b' i := by
  rw [← (Matrix.toLin b b').injective.eq_iff, Matrix.toLin_toMatrix]
  constructor
  · intro h i
    simpa only [Matrix.toLin_self, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using congrArg (fun g : M →ₗ[R] N => g (b i)) h
  · intro hf
    apply b.ext
    intro i
    simpa only [Matrix.toLin_self, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hf i

end Module.Basis
