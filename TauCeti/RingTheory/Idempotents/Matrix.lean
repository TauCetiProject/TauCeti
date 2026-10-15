/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.RingTheory.Idempotents.Corner

/-!
# The corner of a diagonal matrix unit

For a ring `α` and an index `i`, the diagonal matrix unit `Eᵢᵢ = Matrix.single i i 1` is an
idempotent of `Matrix n n α`. Its corner `Eᵢᵢ · Matrix n n α · Eᵢᵢ` consists of the matrices
supported on the entry `(i, i)`, so it is a copy of `α`; and `Eᵢᵢ` is **full**, generating the
whole matrix ring as a two-sided ideal, because `1 = ∑ⱼ Eⱼᵢ Eᵢᵢ Eᵢⱼ`.

Together these say that `α` is a full idempotent corner of `Matrix n n α`, the standard instance of
Morita equivalence. In a product of matrix rings over division rings, one such unit per factor
selects a full idempotent whose corner is a product of division rings.

## Main definitions

* `Matrix.cornerSingleOneEquiv`: the corner of `Eᵢᵢ` is isomorphic to the coefficient ring.

## Main results

* `Matrix.isIdempotentElem_single_one`: the diagonal matrix unit `Eᵢᵢ` is idempotent.
* `Matrix.single_apply_eq_of_mem_corner`: a matrix in the corner of `Eᵢᵢ` is supported on the
  entry `(i, i)`.
* `Matrix.twoSidedIdeal_span_single_one_eq_top`: the diagonal matrix unit `Eᵢᵢ` is full.
-/

public section

namespace Matrix

variable {n α : Type*} [Fintype n] [DecidableEq n]

section Semiring

variable [Semiring α]

/-- The diagonal matrix unit `Eᵢᵢ` is idempotent. -/
theorem isIdempotentElem_single_one (i : n) : IsIdempotentElem (single i i (1 : α)) := by
  simp [IsIdempotentElem]

/-- A matrix in the corner of `Eᵢᵢ` is supported on the entry `(i, i)`. -/
theorem single_apply_eq_of_mem_corner {i : n} {x : Matrix n n α}
    (hx : x ∈ Subsemigroup.corner (single i i (1 : α))) : single i i (x i i) = x := by
  obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff (isIdempotentElem_single_one i)).mp hx
  calc single i i (x i i) = single i i (1 : α) * x * single i i 1 := by
        rw [single_mul_mul_single, one_mul, mul_one]
    _ = x := by rw [hl, hr]

/-- **The corner of the diagonal matrix unit `Eᵢᵢ` is the coefficient ring**, through the
`(i, i)` entry. -/
def cornerSingleOneEquiv (i : n) : (isIdempotentElem_single_one (α := α) i).Corner ≃+* α where
  toFun x := x.1 i i
  invFun a := ⟨single i i a, (Subsemigroup.mem_corner_iff (isIdempotentElem_single_one i)).mpr
    ⟨by simp, by simp⟩⟩
  left_inv x := Subtype.ext (single_apply_eq_of_mem_corner x.2)
  right_inv a := by simp
  map_mul' x y := by
    rw [IsIdempotentElem.Corner.val_mul]
    conv_lhs => rw [← single_apply_eq_of_mem_corner x.2, ← single_apply_eq_of_mem_corner y.2]
    simp
  map_add' _ _ := rfl

@[simp]
theorem cornerSingleOneEquiv_apply (i : n) (x : (isIdempotentElem_single_one (α := α) i).Corner) :
    cornerSingleOneEquiv i x = x.1 i i :=
  (rfl)

@[simp]
theorem val_cornerSingleOneEquiv_symm_apply (i : n) (a : α) :
    ((cornerSingleOneEquiv i).symm a).1 = single i i a :=
  (rfl)

end Semiring

/-- **The diagonal matrix unit `Eᵢᵢ` is full**: it generates `Matrix n n α` as a two-sided ideal,
since `1 = ∑ⱼ Eⱼᵢ Eᵢᵢ Eᵢⱼ`. -/
theorem twoSidedIdeal_span_single_one_eq_top [NonAssocRing α] (i : n) :
    TwoSidedIdeal.span {single i i (1 : α)} = ⊤ := by
  refine (TwoSidedIdeal.one_mem_iff _).mp ?_
  rw [← sum_single_one]
  refine sum_mem fun j _ ↦ ?_
  have h : single j i (1 : α) * single i i 1 * single i j 1 = single j j 1 := by simp
  rw [← h]
  exact TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span rfl))

end Matrix
