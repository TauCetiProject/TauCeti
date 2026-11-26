/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `normalizerMonoidHom` occurs in the definition of `diagGLConj`.
public import Mathlib.GroupTheory.Subgroup.Centralizer
-- `diagGL` occurs in the statements, and `diagGL_mul_mul_inv_apply` computes the conjugates.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- `upperUnitriangularGroup` and `adjacentHom` occur in the statements.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.AdjacentQuotient

/-!
# Conjugation by the diagonal torus on the upper-unitriangular group

Let `R` be a ring and `ι` a finite linearly ordered type. Conjugation by a diagonal invertible
matrix `t = diag(tᵢ, …)` acts on the `(i, j)` entry of a matrix by `x ↦ tᵢ x tⱼ⁻¹`
(`TauCeti.diagGL_mul_mul_inv_apply`). So the entries below the diagonal of an
upper-unitriangular matrix stay zero and its diagonal entries stay one: the diagonal torus
normalizes the upper-unitriangular group `U_ι(R)` and acts on it by conjugation,
`TauCeti.UpperUnitriangularGroup.diagGLConj`. On the first superdiagonal, read off by
`TauCeti.UpperUnitriangularGroup.adjacentHom`, conjugation by `t` sends the `i`-th entry `x`
to `tᵢ x tᵢ₊₁⁻¹`. When `R` is commutative this is multiplication by the scalar `tᵢ tᵢ₊₁⁻¹`, the
value at `t` of the simple root `εᵢ - εᵢ₊₁`.

## Main declarations

* `TauCeti.UpperUnitriangularGroup.diagGL_mem_normalizer`: diagonal matrices normalize
  `U_ι(R)`.
* `TauCeti.UpperUnitriangularGroup.diagGLConj`: the conjugation action of the diagonal torus.
* `TauCeti.UpperUnitriangularGroup.coe_diagGLConj_apply_apply`: the entries of `t u t⁻¹`.
* `TauCeti.UpperUnitriangularGroup.adjacentHom_diagGLConj`: conjugation sends the `i`-th
  entry `x` of the first superdiagonal to `tᵢ x tᵢ₊₁⁻¹`.

## Implementation notes

`diagGLConj` follows the conjugation action
`TauCeti.BlockUpperUnitriangularGroup.blockDiagonalConj` of the block-diagonal Levi subgroup on
the block upper-unitriangular group in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/UpperUnitriangular/Block.lean`, which served as
the template for its construction through `Subgroup.normalizerMonoidHom`.

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

variable [Ring R]

namespace UpperUnitriangularGroup

variable [LinearOrder ι] {n : ℕ}

/-- Conjugation by a diagonal matrix preserves the upper-unitriangular group. -/
theorem diagGL_mem_normalizer (t : ι → Rˣ) :
    diagGL t ∈ Subgroup.normalizer (upperUnitriangularGroup ι R : Set (GL ι R)) := by
  have hmem (t : ι → Rˣ) {u : GL ι R} (hu : u ∈ upperUnitriangularGroup ι R) :
      diagGL t * u * (diagGL t)⁻¹ ∈ upperUnitriangularGroup ι R := by
    rw [mem_iff] at hu ⊢
    simpa [Units.val_mul, diagGL_coe, ← map_inv] using
      hu.diagonal_mul_mul_diagonal (d := fun i => (t i : R)) (e := fun i => ((t i)⁻¹ : Rˣ))
        fun i => (t i).mul_inv
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

/-- Conjugation by `t` acts on the `(i, j)` entry of an upper-unitriangular matrix by
`x ↦ tᵢ x tⱼ⁻¹`. -/
@[simp]
theorem coe_diagGLConj_apply_apply (t : ι → Rˣ) (u : upperUnitriangularGroup ι R) (i j : ι) :
    (((diagGLConj t u : upperUnitriangularGroup ι R) : GL ι R) : Matrix ι ι R) i j =
      ((t i : Rˣ) : R) * (((u : upperUnitriangularGroup ι R) : GL ι R) : Matrix ι ι R) i j *
        (((t j)⁻¹ : Rˣ) : R) := by
  rw [coe_diagGLConj_apply, diagGL_mul_mul_inv_apply]

/-- Conjugation by `t` sends the `i`-th entry `x` of the first superdiagonal to `tᵢ x tᵢ₊₁⁻¹`. -/
theorem adjacentHom_diagGLConj (t : Fin (n + 1) → Rˣ)
    (u : upperUnitriangularGroup (Fin (n + 1)) R) (i : Fin n) :
    (adjacentHom R n (diagGLConj t u)).toAdd i =
      ((t i.castSucc : Rˣ) : R) * (adjacentHom R n u).toAdd i * (((t i.succ)⁻¹ : Rˣ) : R) := by
  simp only [toAdd_adjacentHom_apply, coe_diagGLConj_apply_apply]

end UpperUnitriangularGroup

end TauCeti
