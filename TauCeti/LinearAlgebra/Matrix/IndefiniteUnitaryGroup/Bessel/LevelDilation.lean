/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel

/-!
# The level dilation of the split form

Let `R` be a commutative semiring with involution and `t` a unit of `R`. On the basis
`e₀, …, e_{ϱ-1}`, middle block, `e*₀, …, e*_{ϱ-1}` (index type `TauCeti.SplitIndex ϱ μ`), whose
vectors carry the levels `TauCeti.splitLevel` (`a` for `e_a`, `ϱ` on the middle block, `2ϱ - a`
for `e*_a`), the **level dilation** `TauCeti.levelDilation ϱ μ t` is the diagonal matrix
`d = diag(t ^ (ϱ - level i))`.

Conjugating by `d` multiplies the `(i, j)` entry of a matrix by `t ^ (level i - level j)`. When
`t` is self-adjoint, `d` is an isometry of the split form `TauCeti.splitGram ϱ M` for every middle
block `M`: the form pairs `e_a` only with `e*_a`, whose exponents `ϱ - a` and `a - ϱ` add up to
zero, and `d` is the identity on the middle block.

## Main definitions

* `TauCeti.levelDilation ϱ μ t`: the diagonal element `diag(t ^ (ϱ - level i))` of the general
  linear group.

## Main results

* `TauCeti.inv_levelDilation_mul_mul_apply`: `(d⁻¹ * u * d) i j = t ^ (level i - level j) * u i j`
  for every matrix `u`.
* `TauCeti.levelDilation_mem_unitaryGroupOf`: for self-adjoint `t`, `d` lies in the unitary group
  of the split form of every middle block.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, declaration `New.RealPlace.exists_dilation`.
* H. Xue, *Bessel models for real unitary groups: the tempered case*, Duke Math. J. 172 (2023).
-/

public section

open Matrix

namespace TauCeti

variable (ϱ : ℕ) (μ : Type*) [Fintype μ] [DecidableEq μ]

section Semiring

variable {R : Type*} [Semiring R]

/-- The **level dilation** `diag(t ^ (ϱ - level i))` on the basis of the split form with `ϱ`
hyperbolic pairs and middle index type `μ`. -/
def levelDilation (t : Rˣ) : GL (SplitIndex ϱ μ) R :=
  diagGL fun i ↦ t ^ ((ϱ : ℤ) - splitLevel i)

variable {ϱ μ}

/-- The matrix of the level dilation is the diagonal matrix with entries `t ^ (ϱ - level i)`. -/
@[simp]
theorem levelDilation_coe (t : Rˣ) :
    (levelDilation ϱ μ t : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) =
      diagonal fun i ↦ ((t ^ ((ϱ : ℤ) - splitLevel i) : Rˣ) : R) :=
  diagGL_coe _

/-- The matrix of the inverse of the level dilation is the diagonal matrix with entries
`t ^ (level i - ϱ)`. -/
@[simp]
theorem levelDilation_inv_coe (t : Rˣ) :
    (((levelDilation ϱ μ t)⁻¹ : GL (SplitIndex ϱ μ) R) :
        Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) =
      diagonal fun i ↦ ((t ^ ((splitLevel i : ℤ) - ϱ) : Rˣ) : R) := by
  rw [levelDilation, ← map_inv, diagGL_coe]
  congr! with i
  rw [Pi.inv_apply, ← _root_.zpow_neg, neg_sub]

end Semiring

section CommSemiring

variable {ϱ μ} {R : Type*} [CommSemiring R]

/-- **Conjugation by the level dilation** multiplies the `(i, j)` entry of any matrix by
`t ^ (level i - level j)`. -/
theorem inv_levelDilation_mul_mul_apply (t : Rˣ)
    (u : Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) (i j : SplitIndex ϱ μ) :
    ((((levelDilation ϱ μ t)⁻¹ : GL (SplitIndex ϱ μ) R) :
        Matrix (SplitIndex ϱ μ) (SplitIndex ϱ μ) R) * u * levelDilation ϱ μ t) i j =
      ((t ^ ((splitLevel i : ℤ) - splitLevel j) : Rˣ) : R) * u i j := by
  rw [levelDilation_inv_coe, levelDilation_coe, mul_diagonal, diagonal_mul, mul_right_comm,
    ← Units.val_mul, ← _root_.zpow_add, sub_add_sub_cancel]

variable [StarRing R]

/-- For a self-adjoint unit `t`, the level dilation is an isometry of the split form of every
middle block `M`. -/
theorem levelDilation_mem_unitaryGroupOf {t : Rˣ} (ht : star (t : R) = t)
    (M : Matrix μ μ R) : levelDilation ϱ μ t ∈ unitaryGroupOf (splitGram ϱ M) := by
  have htu : star t = t := Units.ext (by rw [Units.coe_star, ht])
  have hstar (k : ℤ) : star ((t ^ k : Rˣ) : R) = (t ^ k : Rˣ) := by
    rw [← Units.coe_star, star_zpow, htu]
  have hexp (a : Fin ϱ) : (ϱ : ℤ) - a + (ϱ - ((2 * ϱ : ℕ) - a)) = 0 := by
    push_cast
    ring
  have hpair (a : Fin ϱ) :
      ((t ^ ((ϱ : ℤ) - a) : Rˣ) : R) * ((t ^ ((ϱ : ℤ) - (2 * ϱ - a : ℕ)) : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, ← _root_.zpow_add, Nat.cast_sub (by omega), hexp, zpow_zero,
      Units.val_one]
  rw [mem_unitaryGroupOf_iff, levelDilation_coe, star_eq_conjTranspose, diagonal_conjTranspose]
  ext (a | i | a) (b | j | b)
  all_goals simp only [mul_diagonal, diagonal_mul, Pi.star_apply, hstar, splitGram_inl_inl,
    splitGram_inl_middle, splitGram_middle_inl, splitGram_middle_middle, splitGram_inl_eStar,
    splitGram_eStar_inl, splitGram_middle_eStar, splitGram_eStar_middle, splitGram_eStar_eStar,
    splitLevel_inl, splitLevel_middle, splitLevel_eStar, mul_zero, zero_mul]
  · -- the pairing of `e_a` with `e*_b`
    rcases eq_or_ne a b with rfl | hab
    · rw [one_apply_eq, mul_one, hpair]
    · rw [one_apply_ne hab, mul_zero, zero_mul]
  · -- the middle block, where the exponent is zero
    simp
  · -- the pairing of `e*_a` with `e_b`
    rcases eq_or_ne a b with rfl | hab
    · rw [one_apply_eq, mul_one, mul_comm, hpair]
    · rw [one_apply_ne hab, mul_zero, zero_mul]

end CommSemiring

end TauCeti
