/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `normalizerMonoidHom` occurs in the definition of `diagGLConj`.
public import Mathlib.GroupTheory.Subgroup.Centralizer
-- `diagGL` occurs in the statements.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- `upperUnitriangularGroup` and `superdiagonalHom` occur in the statements.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Superdiagonal

/-!
# Conjugation by the diagonal torus on the upper-unitriangular group

Let `ι` be a finite type with decidable equality. Over a semiring `R`, conjugation by a diagonal
invertible matrix `t = diag(tᵢ, …)` rescales the `(i, j)` entry of every matrix by `tᵢ tⱼ⁻¹`
(`TauCeti.diagGL_mul_mul_inv_apply`). Over a ring `R` and a finite linearly ordered `ι`, the
entries below the diagonal of an upper-unitriangular matrix stay zero and its diagonal entries
stay one, so the diagonal torus normalizes the upper-unitriangular group `U_ι(R)` and acts on it
by conjugation: `TauCeti.UpperUnitriangularGroup.diagGLConj`. On the first superdiagonal
`TauCeti.UpperUnitriangularGroup.superdiagonalHom`, conjugation by `t` multiplies the `i`-th entry
by `tᵢ tᵢ₊₁⁻¹`, the value at `t` of the root `εᵢ - εᵢ₊₁`.

## Main declarations

* `TauCeti.diagGL_mul_mul_inv_apply`: the entries of `t g t⁻¹` are `tᵢ gᵢⱼ tⱼ⁻¹`.
* `TauCeti.UpperUnitriangularGroup.diagGL_mem_normalizer`: diagonal matrices normalize
  `U_ι(R)`.
* `TauCeti.UpperUnitriangularGroup.diagGLConj`: the conjugation action of the diagonal torus.
* `TauCeti.UpperUnitriangularGroup.coe_diagGLConj_apply_apply`: the entries of `t u t⁻¹`.
* `TauCeti.UpperUnitriangularGroup.superdiagonalHom_diagGLConj`: conjugation scales the `i`-th
  entry of the first superdiagonal by `tᵢ tᵢ₊₁⁻¹`.

## References

* R. W. Carter, *Finite Groups of Lie Type*, Chapter 5.
* F. Digne, J. Michel, *Representations of Finite Groups of Lie Type*, Cambridge University Press,
  1991, §9.1.
-/

public section

open Matrix

namespace TauCeti

universe u v

variable {R : Type u} {ι : Type v} [Fintype ι]

section DecidableEq

variable [DecidableEq ι] [Semiring R]

/-- Conjugation by a diagonal matrix `t` rescales the `(i, j)` entry of a matrix by `tᵢ tⱼ⁻¹`. -/
theorem diagGL_mul_mul_inv_apply (t : ι → Rˣ) (g : GL ι R) (i j : ι) :
    ((diagGL t * g * (diagGL t)⁻¹ : GL ι R) : Matrix ι ι R) i j =
      ((t i : Rˣ) : R) * ((g : GL ι R) : Matrix ι ι R) i j * (((t j)⁻¹ : Rˣ) : R) := by
  have hval : (((diagGL t)⁻¹ : GL ι R) : Matrix ι ι R) =
      Matrix.diagonal fun a => (((t a)⁻¹ : Rˣ) : R) := by
    rw [← map_inv diagGL t, diagGL_coe]
    simp
  simp only [Units.val_mul, diagGL_coe, hval, Matrix.diagonal_mul, Matrix.mul_diagonal]

end DecidableEq

variable [Ring R]

namespace UpperUnitriangularGroup

variable [LinearOrder ι] {n : ℕ}

/-- Conjugation by a diagonal matrix preserves the upper-unitriangular group. -/
theorem diagGL_mem_normalizer (t : ι → Rˣ) :
    diagGL t ∈ Subgroup.normalizer (upperUnitriangularGroup ι R : Set (GL ι R)) := by
  have hmem (t : ι → Rˣ) {u : GL ι R} (hu : u ∈ upperUnitriangularGroup ι R) :
      diagGL t * u * (diagGL t)⁻¹ ∈ upperUnitriangularGroup ι R := by
    rw [mem_iff, isUpperUnitriangular_iff] at hu ⊢
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [diagGL_mul_mul_inv_apply, hu.1 hji, mul_zero, zero_mul]
    · rw [diagGL_mul_mul_inv_apply, hu.2 i, mul_one, Units.mul_inv]
  refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨hmem t, fun hu => ?_⟩
  have h := hmem t⁻¹ hu
  simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

/-- The conjugation action of the diagonal torus on the upper-unitriangular group. -/
def diagGLConj : (ι → Rˣ) →* MulAut (upperUnitriangularGroup ι R) :=
  (upperUnitriangularGroup ι R).normalizerMonoidHom.comp
    ((diagGL (k := R) (ι := ι)).codRestrict _ diagGL_mem_normalizer)

/-- The conjugate of `u` by a diagonal matrix `t` is `t u t⁻¹`. -/
theorem coe_diagGLConj_apply (t : ι → Rˣ) (u : upperUnitriangularGroup ι R) :
    ((diagGLConj t u : upperUnitriangularGroup ι R) : GL ι R) = diagGL t * ↑u * (diagGL t)⁻¹ := by
  simp [diagGLConj]

/-- Conjugation by `t` rescales the `(i, j)` entry of an upper-unitriangular matrix by `tᵢ tⱼ⁻¹`. -/
@[simp]
theorem coe_diagGLConj_apply_apply (t : ι → Rˣ) (u : upperUnitriangularGroup ι R) (i j : ι) :
    (((diagGLConj t u : upperUnitriangularGroup ι R) : GL ι R) : Matrix ι ι R) i j =
      ((t i : Rˣ) : R) * (((u : upperUnitriangularGroup ι R) : GL ι R) : Matrix ι ι R) i j *
        (((t j)⁻¹ : Rˣ) : R) := by
  rw [coe_diagGLConj_apply, diagGL_mul_mul_inv_apply]

/-- Conjugation by `t` scales the `i`-th entry of the first superdiagonal by `tᵢ tᵢ₊₁⁻¹`. -/
theorem superdiagonalHom_diagGLConj (t : Fin (n + 1) → Rˣ)
    (u : upperUnitriangularGroup (Fin (n + 1)) R) (i : Fin n) :
    superdiagonalHom (diagGLConj t u) i =
      ((t i.castSucc : Rˣ) : R) * superdiagonalHom u i * (((t i.succ)⁻¹ : Rˣ) : R) := by
  simp only [superdiagonalHom_apply, coe_diagGLConj_apply_apply]

end UpperUnitriangularGroup

end TauCeti
