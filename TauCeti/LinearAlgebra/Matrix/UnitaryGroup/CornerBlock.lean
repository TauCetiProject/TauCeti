/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The block-diagonal embedding `U(1) × U(m) → U(m + 1)` over a star semiring

A unitary scalar `c` and a unitary matrix `B` of size `m` over a star semiring `α` give the
block-diagonal unitary matrix `diag(c, B)` of size `m + 1`, with `c` in the corner indexed by `0`.
This embeds `unitary α × unitary (Matrix (Fin m) (Fin m) α)` in
`unitary (Matrix (Fin (m + 1)) (Fin (m + 1)) α)` as a group.

No commutativity is assumed, so the construction applies to the quaternions, where it embeds
`Sp(1) × Sp(m)` in the compact symplectic group `Sp(m + 1)`. Over a division ring its image
consists of the unitary matrices whose column `0` vanishes below the corner
(`Matrix.mem_range_unitaryProdBlockSucc_iff`): the stabilizer of the right line spanned by `e₀`.
The entries of row `0` to the right of the corner then vanish too, because the inverse of a
unitary matrix is its conjugate transpose and the corner, a nonzero element of a division ring,
is invertible on both sides.

## Main definitions

* `Matrix.unitaryProdBlockSucc`: the embedding `(c, B) ↦ diag(c, B)`.

## Main results

* `Matrix.unitaryProdBlockSucc_injective`: the embedding is injective.
* `Matrix.mem_range_unitaryProdBlockSucc_iff`: over a division ring, its image is the subgroup of
  unitary matrices whose column `0` vanishes below the corner.
-/

public section

open scoped Matrix

namespace Matrix

variable {α : Type*} {m : ℕ}

section Semiring

variable [Semiring α]

/-- The block-diagonal matrix `diag(c, B)` of size `m + 1`, with `c` in the corner indexed by `0`
and `B` on the indices `Fin.succ`. -/
private def blockSucc (c : α) (B : Matrix (Fin m) (Fin m) α) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) α :=
  of (Fin.cons (Fin.cons c 0) fun i ↦ Fin.cons 0 (B i))

@[simp]
private theorem blockSucc_zero_zero (c : α) (B : Matrix (Fin m) (Fin m) α) :
    blockSucc c B 0 0 = c :=
  rfl

@[simp]
private theorem blockSucc_zero_succ (c : α) (B : Matrix (Fin m) (Fin m) α) (j : Fin m) :
    blockSucc c B 0 j.succ = 0 :=
  rfl

@[simp]
private theorem blockSucc_succ_zero (c : α) (B : Matrix (Fin m) (Fin m) α) (i : Fin m) :
    blockSucc c B i.succ 0 = 0 :=
  rfl

@[simp]
private theorem blockSucc_succ_succ (c : α) (B : Matrix (Fin m) (Fin m) α) (i j : Fin m) :
    blockSucc c B i.succ j.succ = B i j :=
  rfl

private theorem blockSucc_mul (c c' : α) (B B' : Matrix (Fin m) (Fin m) α) :
    blockSucc c B * blockSucc c' B' = blockSucc (c * c') (B * B') := by
  ext p q
  refine Fin.cases ?_ (fun i ↦ ?_) p <;> refine Fin.cases ?_ (fun j ↦ ?_) q <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem blockSucc_one : blockSucc (1 : α) (1 : Matrix (Fin m) (Fin m) α) = 1 := by
  ext p q
  refine Fin.cases ?_ (fun i ↦ ?_) p <;> refine Fin.cases ?_ (fun j ↦ ?_) q <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

variable [StarRing α]

private theorem star_blockSucc (c : α) (B : Matrix (Fin m) (Fin m) α) :
    star (blockSucc c B) = blockSucc (star c) (star B) := by
  ext p q
  refine Fin.cases ?_ (fun i ↦ ?_) p <;> refine Fin.cases ?_ (fun j ↦ ?_) q <;>
    simp [star_eq_conjTranspose, conjTranspose_apply]

private theorem blockSucc_mem_unitary {c : α} (hc : c ∈ unitary α) {B : Matrix (Fin m) (Fin m) α}
    (hB : B ∈ unitary (Matrix (Fin m) (Fin m) α)) :
    blockSucc c B ∈ unitary (Matrix (Fin (m + 1)) (Fin (m + 1)) α) := by
  refine ⟨?_, ?_⟩ <;> rw [star_blockSucc, blockSucc_mul, ← blockSucc_one]
  · rw [hc.1, hB.1]
  · rw [hc.2, hB.2]

variable (α m) in
/-- The **block-diagonal embedding** `(c, B) ↦ diag(c, B)` of
`unitary α × unitary (Matrix (Fin m) (Fin m) α)` in
`unitary (Matrix (Fin (m + 1)) (Fin (m + 1)) α)`: the unitary scalar `c` occupies the corner
indexed by `0`, and `B` the indices `Fin.succ`. -/
def unitaryProdBlockSucc :
    unitary α × unitary (Matrix (Fin m) (Fin m) α) →*
      unitary (Matrix (Fin (m + 1)) (Fin (m + 1)) α) where
  toFun cB := ⟨blockSucc cB.1.1 cB.2.1, blockSucc_mem_unitary cB.1.2 cB.2.2⟩
  map_one' := Subtype.ext blockSucc_one
  map_mul' _ _ := Subtype.ext (blockSucc_mul _ _ _ _).symm

@[simp]
theorem unitaryProdBlockSucc_apply_zero_zero (cB : unitary α × unitary (Matrix (Fin m) (Fin m) α)) :
    (unitaryProdBlockSucc α m cB).1 0 0 = cB.1 :=
  (rfl)

@[simp]
theorem unitaryProdBlockSucc_apply_zero_succ (cB : unitary α × unitary (Matrix (Fin m) (Fin m) α))
    (j : Fin m) : (unitaryProdBlockSucc α m cB).1 0 j.succ = 0 :=
  (rfl)

@[simp]
theorem unitaryProdBlockSucc_apply_succ_zero (cB : unitary α × unitary (Matrix (Fin m) (Fin m) α))
    (i : Fin m) : (unitaryProdBlockSucc α m cB).1 i.succ 0 = 0 :=
  (rfl)

@[simp]
theorem unitaryProdBlockSucc_apply_succ_succ (cB : unitary α × unitary (Matrix (Fin m) (Fin m) α))
    (i j : Fin m) : (unitaryProdBlockSucc α m cB).1 i.succ j.succ = cB.2.1 i j :=
  (rfl)

/-- The block-diagonal embedding of `unitary α × unitary (Matrix (Fin m) (Fin m) α)` is
injective. -/
theorem unitaryProdBlockSucc_injective : Function.Injective (unitaryProdBlockSucc α m) := by
  rintro ⟨c, B⟩ ⟨c', B'⟩ h
  have h' := congrArg Subtype.val h
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext (Matrix.ext fun i j ↦ ?_))
  · simpa using congrFun (congrFun h' 0) 0
  · simpa using congrFun (congrFun h' i.succ) j.succ

end Semiring

section DivisionRing

variable [DivisionRing α] [StarRing α]

/-- **The block-diagonal unitary matrices `diag(c, B)` are those whose first column is a multiple
of `e₀`**: over a division ring, a unitary matrix of size `m + 1` lies in the image of
`unitary α × unitary (Matrix (Fin m) (Fin m) α)` exactly when its entries below the corner in the
column `0` vanish. -/
theorem mem_range_unitaryProdBlockSucc_iff {A : unitary (Matrix (Fin (m + 1)) (Fin (m + 1)) α)} :
    A ∈ (unitaryProdBlockSucc α m).range ↔ ∀ i : Fin m, A.1 i.succ 0 = 0 := by
  refine ⟨?_, fun hA ↦ ?_⟩
  · rintro ⟨cB, rfl⟩ i
    exact unitaryProdBlockSucc_apply_succ_zero cB i
  have hentry (p q : Fin (m + 1)) :
      ∑ k, star (A.1 k p) * A.1 k q = if p = q then 1 else 0 := by
    simpa [Matrix.mul_apply, star_eq_conjTranspose, Matrix.one_apply] using
      congrFun (congrFun A.2.1 p) q
  -- The corner is a unitary scalar: its left inverse is two-sided in a division ring.
  have hc : star (A.1 0 0) * A.1 0 0 = 1 := by simpa [Fin.sum_univ_succ, hA] using hentry 0 0
  have hc' : A.1 0 0 * star (A.1 0 0) = 1 := by
    have h0 : A.1 0 0 ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hc
      exact zero_ne_one hc
    rw [eq_inv_of_mul_eq_one_left hc, mul_inv_cancel₀ h0]
  -- The row `0` vanishes off the corner.
  have hrow (j : Fin m) : A.1 0 j.succ = 0 := by
    have h := hentry 0 j.succ
    simp only [Fin.sum_univ_succ, hA, star_zero, zero_mul, Finset.sum_const_zero, add_zero,
      (Fin.succ_ne_zero j).symm, ite_false] at h
    calc A.1 0 j.succ = A.1 0 0 * star (A.1 0 0) * A.1 0 j.succ := by rw [hc', one_mul]
      _ = 0 := by rw [mul_assoc, h, mul_zero]
  let B : Matrix (Fin m) (Fin m) α := fun i j ↦ A.1 i.succ j.succ
  have hAB : A.1 = blockSucc (A.1 0 0) B := by
    ext p q
    refine Fin.cases ?_ (fun i ↦ ?_) p <;> refine Fin.cases ?_ (fun j ↦ ?_) q <;>
      first | rfl | exact hrow j | exact hA i
  have hB : B ∈ unitary (Matrix (Fin m) (Fin m) α) := by
    have h₁ := A.2.1
    have h₂ := A.2.2
    rw [hAB, star_blockSucc, blockSucc_mul, ← blockSucc_one] at h₁ h₂
    refine ⟨Matrix.ext fun i j ↦ ?_, Matrix.ext fun i j ↦ ?_⟩
    · simpa using congrFun (congrFun h₁ i.succ) j.succ
    · simpa using congrFun (congrFun h₂ i.succ) j.succ
  exact ⟨(⟨A.1 0 0, hc, hc'⟩, ⟨B, hB⟩), Subtype.ext hAB.symm⟩

end DivisionRing

end Matrix
