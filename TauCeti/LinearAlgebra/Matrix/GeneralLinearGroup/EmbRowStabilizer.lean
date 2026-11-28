/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ColumnRowFixing

/-!
# The row stabiliser of an embedding

Let `φ : R →+* S` be a ring homomorphism, `e : r ↪ n` an embedding of index types with `n`
finite and `w` a matrix over `S` with columns indexed by `n`. The subgroup
`embRowStabilizer φ w e` of `GL n R` consists of the invertible matrices `A` whose columns off
`Set.range e` are those of the identity matrix (that is,
`A ∈ TauCeti.columnRowFixingSubgroup R (Set.range e)ᶜ ∅`) and which fix `w` after base change
along `φ`: `w * A.map φ = w`.

For such `A`, the condition `w * A.map φ = w` holds automatically on the columns off `e`, so
membership only depends on the columns `e` of `A`.

This subgroup is unrelated to the finite adelic row stabiliser of a lattice,
`finiteAdelicRowStabilizer`.

## Main definitions

* `TauCeti.embRowStabilizer φ w e`: the row stabiliser `H(φ, w, e)`.

## Main results

* `TauCeti.mem_embRowStabilizer_iff_of_mem_columnRowFixingSubgroup`: for `z` with standard
  columns off `e`, membership in the row stabiliser depends only on the columns `e` of `z`.

## References

The definition follows the formal proof in the folder `grh` of
https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
`New/OneLift/ComparisonOperator/OneExchange.lean` (`New.Rows.rowStabilizer`).
-/

public section

open Matrix

namespace TauCeti

variable {n r m R S : Type*} [Fintype n] [DecidableEq n] [Semiring R] [Semiring S]

/-- The row stabiliser `H(φ, w, e)`: the invertible matrices `A` over `R` whose columns off the
image of `e` are those of the identity matrix and with `w * A.map φ = w`. -/
def embRowStabilizer (φ : R →+* S) (w : Matrix m n S) (e : r ↪ n) : Subgroup (GL n R) where
  carrier := {A | A ∈ columnRowFixingSubgroup R (Set.range e)ᶜ ∅ ∧
    w * (A : Matrix n n R).map φ = w}
  one_mem' := ⟨one_mem _, by simp [Matrix.map_one φ φ.map_zero φ.map_one]⟩
  mul_mem' {A B} hA hB := ⟨mul_mem hA.1 hB.1, by
    rw [Units.val_mul, Matrix.map_mul, ← Matrix.mul_assoc, hA.2, hB.2]⟩
  inv_mem' {A} hA := ⟨inv_mem hA.1, by
    conv_lhs => rw [← hA.2]
    rw [Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one φ φ.map_zero φ.map_one, Matrix.mul_one]⟩

variable {φ : R →+* S} {w : Matrix m n S} {e : r ↪ n}

/-- Membership in the row stabiliser: standard columns off the image of `e`, and
`w * A.map φ = w`. -/
theorem mem_embRowStabilizer_iff {A : GL n R} :
    A ∈ embRowStabilizer φ w e ↔
      A ∈ columnRowFixingSubgroup R (Set.range e)ᶜ ∅ ∧ w * (A : Matrix n n R).map φ = w :=
  Iff.rfl

/-- For `z` whose columns off the image of `e` are those of the identity matrix, `z` lies in the
row stabiliser exactly when `w` times the columns `e` of `z.map φ` are the columns `e` of `w`. -/
theorem mem_embRowStabilizer_iff_of_mem_columnRowFixingSubgroup {z : GL n R}
    (hz : z ∈ columnRowFixingSubgroup R (Set.range e)ᶜ ∅) :
    z ∈ embRowStabilizer φ w e ↔
      w * ((z : Matrix n n R).submatrix id e).map φ = w.submatrix id e := by
  have hcol := (mem_columnRowFixingSubgroup_iff.mp hz).1
  rw [mem_embRowStabilizer_iff, and_iff_right hz]
  constructor
  · intro h
    ext i j
    simpa [Matrix.mul_apply] using congrFun (congrFun h i) (e j)
  · intro h
    ext i k
    by_cases hk : k ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hk
      simpa [Matrix.mul_apply] using congrFun (congrFun h i) j
    · have hk' : ∀ l, (z : Matrix n n R).map φ l k = (1 : Matrix n n S) l k := fun l ↦ by
        simp [hcol k hk l, Matrix.one_apply, apply_ite φ]
      simp only [Matrix.mul_apply, hk']
      rw [← Matrix.mul_apply, Matrix.mul_one]

end TauCeti
