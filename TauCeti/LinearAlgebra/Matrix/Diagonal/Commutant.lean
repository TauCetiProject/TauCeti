/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The block diagonal part of a matrix

For a labelling `t : ι → β` of the indices, the **block diagonal part** `x.blockDiagPart t` of a
square matrix `x` keeps the entries `x a b` with `t a = t b` and replaces the others by `0`
(`Matrix.blockDiagPart`). It is the projection onto the matrices that are block diagonal for the
partition of the indices into the fibres of `t`. For labels in a commutative ring of entries without
zero divisors, these are the matrices commuting with `diagonal t`
(`Matrix.commute_diagonal_iff_blockDiagPart_eq`).

For a sign vector `ε : ι → ℤˣ`, the matrix `diag(ε)` is an involution and conjugating by it changes
the sign of the entries off the blocks, so `x + diag(ε) x diag(ε) = 2 · x.blockDiagPart ε`
(`Matrix.add_diagonal_mul_mul_diagonal_eq_two_smul_blockDiagPart`). For the indefinite unitary
group `U(diag ε) ≅ U(p, q)`, the block diagonal part of `g` is the pair of its diagonal blocks, and
the block diagonal elements are those of the maximal compact subgroup `U(p) × U(q)`.

## Main definitions

* `Matrix.blockDiagPart x t`: the block diagonal part of `x` for the labelling `t`.

## Main results

* `Matrix.blockDiagPart_eq_self_iff`: `x` is its own block diagonal part when its entries between
  different labels vanish.
* `Matrix.commute_diagonal_blockDiagPart`, `Matrix.commute_diagonal_iff_blockDiagPart_eq`: the
  block diagonal part commutes with `diagonal t`, and the matrices commuting with `diagonal t` are
  their own block diagonal parts.
* `Matrix.add_diagonal_mul_mul_diagonal_eq_two_smul_blockDiagPart`,
  `Matrix.blockDiagPart_eq_inv_two_smul`: for signs `ε`, the block diagonal part of `x` is
  `(x + diag(ε) x diag(ε)) / 2`.
-/

public section

namespace Matrix

variable {ι β R : Type*} [DecidableEq β]

section Zero

variable [Zero R]

/-- The **block diagonal part** of `x` for a labelling `t` of the indices: the entries `x a b` with
`t a = t b` are kept, the others replaced by `0`. -/
def blockDiagPart (x : Matrix ι ι R) (t : ι → β) : Matrix ι ι R :=
  of fun a b ↦ if t a = t b then x a b else 0

@[simp]
theorem blockDiagPart_apply (x : Matrix ι ι R) (t : ι → β) (a b : ι) :
    x.blockDiagPart t a b = if t a = t b then x a b else 0 :=
  (rfl)

theorem blockDiagPart_apply_of_eq (x : Matrix ι ι R) {t : ι → β} {a b : ι} (h : t a = t b) :
    x.blockDiagPart t a b = x a b := by
  simp [h]

theorem blockDiagPart_apply_of_ne (x : Matrix ι ι R) {t : ι → β} {a b : ι} (h : t a ≠ t b) :
    x.blockDiagPart t a b = 0 := by
  simp [h]

/-- A matrix is its own block diagonal part exactly when its entries between indices of different
labels vanish. -/
theorem blockDiagPart_eq_self_iff {x : Matrix ι ι R} {t : ι → β} :
    x.blockDiagPart t = x ↔ ∀ a b, t a ≠ t b → x a b = 0 := by
  refine ⟨fun h a b hab ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, blockDiagPart_apply_of_ne _ hab]
  · ext a b
    by_cases hab : t a = t b
    · exact blockDiagPart_apply_of_eq x hab
    · rw [blockDiagPart_apply_of_ne x hab, h a b hab]

@[simp]
theorem blockDiagPart_blockDiagPart (x : Matrix ι ι R) (t : ι → β) :
    (x.blockDiagPart t).blockDiagPart t = x.blockDiagPart t :=
  blockDiagPart_eq_self_iff.2 fun _ _ ↦ blockDiagPart_apply_of_ne x

/-- Relabelling by an injective map does not change the block diagonal part. -/
theorem blockDiagPart_comp {γ : Type*} [DecidableEq γ] {f : β → γ} (hf : Function.Injective f)
    (x : Matrix ι ι R) (t : ι → β) : x.blockDiagPart (f ∘ t) = x.blockDiagPart t := by
  ext a b
  simp [hf.eq_iff]

@[simp]
theorem blockDiagPart_zero (t : ι → β) : (0 : Matrix ι ι R).blockDiagPart t = 0 := by
  ext a b
  simp

@[simp]
theorem blockDiagPart_diagonal [DecidableEq ι] (d : ι → R) (t : ι → β) :
    (diagonal d).blockDiagPart t = diagonal d :=
  blockDiagPart_eq_self_iff.2 fun _ _ hab ↦ diagonal_apply_ne d fun h ↦ hab (h ▸ rfl)

@[simp]
theorem blockDiagPart_one [DecidableEq ι] [One R] (t : ι → β) :
    (1 : Matrix ι ι R).blockDiagPart t = 1 :=
  blockDiagPart_diagonal _ t

end Zero

@[simp]
theorem conjTranspose_blockDiagPart [AddMonoid R] [StarAddMonoid R] (x : Matrix ι ι R)
    (t : ι → β) : (x.blockDiagPart t)ᴴ = xᴴ.blockDiagPart t := by
  ext a b
  by_cases h : t a = t b
  · simp [h]
  · simp [h, Ne.symm h]

@[simp]
theorem blockDiagPart_add [AddZeroClass R] (x y : Matrix ι ι R) (t : ι → β) :
    (x + y).blockDiagPart t = x.blockDiagPart t + y.blockDiagPart t := by
  ext a b
  by_cases h : t a = t b <;> simp [h]

@[simp]
theorem blockDiagPart_smul {S : Type*} [Zero R] [SMulZeroClass S R] (c : S) (x : Matrix ι ι R)
    (t : ι → β) : (c • x).blockDiagPart t = c • x.blockDiagPart t := by
  ext a b
  by_cases h : t a = t b <;> simp [h]

section Commute

variable [Fintype ι] [DecidableEq ι] [NonUnitalNonAssocCommSemiring R] [DecidableEq R]

/-- The block diagonal part of `x` for the labels `d` commutes with `diagonal d`. -/
theorem commute_diagonal_blockDiagPart (d : ι → R) (x : Matrix ι ι R) :
    Commute (diagonal d) (x.blockDiagPart d) :=
  TauCeti.commute_diagonal_of_apply_eq_zero fun _ _ ↦ blockDiagPart_apply_of_ne x

/-- Over a ring without zero divisors, a matrix commutes with `diagonal d` exactly when it is its
own block diagonal part for the labels `d`. -/
theorem commute_diagonal_iff_blockDiagPart_eq [IsLeftCancelMulZero R] {d : ι → R}
    {x : Matrix ι ι R} : Commute (diagonal d) x ↔ x.blockDiagPart d = x := by
  rw [TauCeti.commute_diagonal_iff, blockDiagPart_eq_self_iff]

end Commute

section Signs

variable [Fintype ι] [DecidableEq ι]

/-- **The block diagonal part for signs.** For a sign vector `ε`, conjugating `x` by `diag(ε)`
changes the sign of the entries between indices of different signs, so
`x + diag(ε) x diag(ε) = 2 · x.blockDiagPart ε`. -/
theorem add_diagonal_mul_mul_diagonal_eq_two_smul_blockDiagPart [Ring R] (ε : ι → ℤˣ)
    (x : Matrix ι ι R) :
    x + diagonal (fun a ↦ ((ε a : ℤ) : R)) * x * diagonal (fun a ↦ ((ε a : ℤ) : R)) =
      (2 : R) • x.blockDiagPart ε := by
  refine Matrix.ext fun a b ↦ ?_
  rw [Matrix.add_apply, mul_diagonal, diagonal_mul, Matrix.smul_apply, blockDiagPart_apply,
    smul_eq_mul]
  rcases Int.units_eq_one_or (ε a) with ha | ha <;>
    rcases Int.units_eq_one_or (ε b) with hb | hb <;> simp [ha, hb, two_mul]

/-- For a sign vector `ε` over a division ring of characteristic not `2`, the block diagonal part
of `x` is `(x + diag(ε) x diag(ε)) / 2`. -/
theorem blockDiagPart_eq_inv_two_smul [DivisionRing R] [NeZero (2 : R)] (ε : ι → ℤˣ)
    (x : Matrix ι ι R) :
    x.blockDiagPart ε =
      (2 : R)⁻¹ • (x + diagonal (fun a ↦ ((ε a : ℤ) : R)) * x *
        diagonal (fun a ↦ ((ε a : ℤ) : R))) := by
  rw [add_diagonal_mul_mul_diagonal_eq_two_smul_blockDiagPart, smul_smul,
    inv_mul_cancel₀ (NeZero.ne 2), one_smul]

end Signs

end Matrix
