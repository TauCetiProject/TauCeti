/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Data.ZMod.Basic

/-!
# The commutant of the cyclic shift

For an additive group `n` and `k : n`, the matrix `circulant (Pi.single k 1)` is the permutation
matrix of the translation by `k`: it sends the basis vector at `j` to the basis vector at `k + j`.
For `n = ZMod N` and `k = 1` it is the cyclic shift. This file proves that the matrices commuting
with the cyclic shift are exactly the circulant matrices. The vector `circulant v *ᵥ x` is the
cyclic convolution of `v` and `x`, so the linear maps of `ZMod N → α` given by matrices that
commute with the cyclic shift are exactly the convolutions.

The coefficients lie in any `NonAssocSemiring`: the shift has entries `0` and `1` only, so no
commutativity of the coefficients is needed.

## Main results

* `Matrix.mul_circulant_single_apply`, `Matrix.circulant_single_mul_apply`: multiplying by
  `circulant (Pi.single k a)` on the right or on the left translates the column index by `k` or
  the row index by `-k`, and multiplies by `a`.
* `Matrix.exists_eq_circulant_iff`: a matrix is circulant exactly when its entries are invariant
  under the translation of both indices by the same element.
* `Matrix.commute_circulant_single_iff_apply_add_add`: a matrix commutes with
  `circulant (Pi.single k 1)` exactly when its entries are invariant under the translation of both
  indices by `k`.
* `Matrix.commute_circulant_single_iff_of_zmultiples_eq_top`: if `g` generates `n`, a matrix
  commutes with `circulant (Pi.single g 1)` exactly when it is circulant.
* `Matrix.commute_circulant_single_iff`: a matrix indexed by `ZMod N` commutes with the cyclic
  shift `circulant (Pi.single 1 1)` exactly when it is circulant.
-/

public section

namespace Matrix

variable {α n : Type*}

section Apply

variable [NonUnitalNonAssocSemiring α] [Fintype n] [DecidableEq n] [AddGroup n]

/-- Right multiplication by `circulant (Pi.single k a)` translates the columns by `k` and
multiplies on the right by `a`. -/
@[simp]
theorem mul_circulant_single_apply (M : Matrix n n α) (k : n) (a : α) (i j : n) :
    (M * circulant (Pi.single k a)) i j = M i (k + j) * a := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (k + j)]
  · simp
  · intro l hl
    rw [circulant_apply, Pi.single_eq_of_ne (by rwa [Ne, sub_eq_iff_eq_add]), mul_zero]

/-- Left multiplication by `circulant (Pi.single k a)` translates the rows by `-k` and multiplies
on the left by `a`. -/
@[simp]
theorem circulant_single_mul_apply (M : Matrix n n α) (k : n) (a : α) (i j : n) :
    (circulant (Pi.single k a) * M) i j = a * M (-k + i) j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (-k + i)]
  · simp
  · intro l hl
    rw [circulant_apply, Pi.single_eq_of_ne, zero_mul]
    rintro h
    exact hl (by simp [← h])

end Apply

/-- A matrix indexed by an additive group is circulant exactly when its entries are invariant
under the translation of both indices by the same element. The vector is then the first column
`fun i => M i 0`. -/
theorem exists_eq_circulant_iff [AddGroup n] (M : Matrix n n α) :
    (∃ v, M = circulant v) ↔ ∀ i j k, M (i + k) (j + k) = M i j := by
  constructor
  · rintro ⟨v, rfl⟩ i j k
    simp [add_sub_add_right_eq_sub]
  · intro h
    exact ⟨fun i => M i 0, ext fun i j => by simpa using h (i - j) 0 j⟩

section Commute

variable [NonAssocSemiring α] [Fintype n] [DecidableEq n] [AddGroup n]

/-- A matrix commutes with `circulant (Pi.single k 1)`, the permutation matrix of the translation
by `k`, exactly when its entries are invariant under the translation of both indices by `k`. -/
theorem commute_circulant_single_iff_apply_add_add (M : Matrix n n α) (k : n) :
    Commute M (circulant (Pi.single k 1)) ↔ ∀ i j, M (k + i) (k + j) = M i j := by
  simp only [commute_iff_eq, ← Matrix.ext_iff, mul_circulant_single_apply,
    circulant_single_mul_apply, mul_one, one_mul]
  constructor
  · intro h i j
    simpa using h (k + i) j
  · intro h i j
    simpa using h (-k + i) j

/-- If `g` generates the additive group `n`, a matrix commutes with `circulant (Pi.single g 1)`,
the permutation matrix of the translation by `g`, exactly when it is circulant. -/
theorem commute_circulant_single_iff_of_zmultiples_eq_top {g : n}
    (hg : AddSubgroup.zmultiples g = ⊤) (M : Matrix n n α) :
    Commute M (circulant (Pi.single g 1)) ↔ ∃ v, M = circulant v := by
  -- A cyclic group is commutative.
  have hcomm (x y : n) : x + y = y + x := by
    obtain ⟨a, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (hg ▸ AddSubgroup.mem_top x)
    obtain ⟨b, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (hg ▸ AddSubgroup.mem_top y)
    exact (AddCommute.zsmul_zsmul_self g a b).eq
  rw [commute_circulant_single_iff_apply_add_add, exists_eq_circulant_iff]
  refine ⟨fun h i j k => ?_, fun h i j => by rw [hcomm g i, hcomm g j, h]⟩
  -- The translations under which the entries of `M` are invariant form a subgroup, which
  -- contains `g` and so is everything.
  let S : AddSubgroup n :=
    { carrier := {k | ∀ i j, M (k + i) (k + j) = M i j}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb i j => by
        simp only [add_assoc, ha (b + i), hb i j]
      neg_mem' := fun {a} ha i j => by
        rw [← ha (-a + i) (-a + j)]
        simp }
  have hS : ⊤ ≤ S := hg ▸ AddSubgroup.zmultiples_le.2 h
  rw [hcomm i, hcomm j]
  exact hS (AddSubgroup.mem_top k) i j

/-- A matrix indexed by `ZMod N` commutes with the cyclic shift `circulant (Pi.single 1 1)`
exactly when it is circulant. -/
theorem commute_circulant_single_iff {N : ℕ} [NeZero N] (M : Matrix (ZMod N) (ZMod N) α) :
    Commute M (circulant (Pi.single 1 1)) ↔ ∃ v, M = circulant v :=
  commute_circulant_single_iff_of_zmultiples_eq_top ((AddSubgroup.eq_top_iff' _).2 fun x => by
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
    exact AddSubgroup.mem_zmultiples_iff.2 ⟨m, by rw [zsmul_one]⟩) M

end Commute

end Matrix
