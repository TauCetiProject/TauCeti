/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Matrix.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.CharP

/-!
# Upper unitriangular matrix groups in prime characteristic

The upper unitriangular `n × n` matrices over a ring `R` form a subgroup of the units of the
matrix ring: a strictly upper triangular matrix `N` has vanishing `n`th power, so an upper
unitriangular matrix `1 + N` has the finite Neumann series `∑ k < n, (-N) ^ k` as its inverse.
When `R` has prime characteristic `p`, the same nilpotence gives `(1 + N) ^ p ^ n = 1`, so this
subgroup is a `p`-group.
-/

public section

namespace Matrix

variable {n : ℕ} {R : Type*}

/-- A power `N ^ j` of a strictly upper triangular matrix vanishes at every entry `(a, b)` with
`b < a + j`. -/
theorem pow_apply_eq_zero_of_lt_add [Semiring R] {N : Matrix (Fin n) (Fin n) R}
    (hN : ∀ a b, b ≤ a → N a b = 0) (j : ℕ) {a b : Fin n} (h : (b : ℕ) < a + j) :
    (N ^ j) a b = 0 := by
  induction j generalizing b with
  | zero => exact one_apply_ne (Fin.ne_of_gt h)
  | succ j ih =>
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    rcases lt_or_ge (c : ℕ) (a + j) with hc | hc
    · rw [ih hc, zero_mul]
    · rw [hN c b (Fin.le_iff_val_le_val.2 (by omega)), mul_zero]

/-- A square matrix is upper unitriangular if it agrees with the identity matrix on and below
the diagonal. -/
def IsUpperUnitriangular [Zero R] [One R] (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ a b, b ≤ a → M a b = (1 : Matrix (Fin n) (Fin n) R) a b

/-- A matrix is upper unitriangular iff its diagonal entries are `1` and its entries below the
diagonal are `0`. -/
theorem isUpperUnitriangular_iff [Zero R] [One R] {M : Matrix (Fin n) (Fin n) R} :
    M.IsUpperUnitriangular ↔ (∀ a, M a a = 1) ∧ ∀ a b, b < a → M a b = 0 := by
  refine ⟨fun h ↦ ⟨fun a ↦ by rw [h a a le_rfl, one_apply_eq],
    fun a b hab ↦ by rw [h a b hab.le, one_apply_ne hab.ne']⟩, fun ⟨hd, hl⟩ a b hab ↦ ?_⟩
  rcases hab.lt_or_eq with hab | rfl
  · rw [hl a b hab, one_apply_ne hab.ne']
  · rw [hd, one_apply_eq]

/-- The identity matrix is upper unitriangular. -/
theorem isUpperUnitriangular_one [Zero R] [One R] :
    (1 : Matrix (Fin n) (Fin n) R).IsUpperUnitriangular :=
  fun _ _ _ ↦ rfl

/-- The product of upper unitriangular matrices is upper unitriangular. -/
theorem IsUpperUnitriangular.mul [NonAssocSemiring R] {M M' : Matrix (Fin n) (Fin n) R}
    (hM : M.IsUpperUnitriangular) (hM' : M'.IsUpperUnitriangular) :
    (M * M').IsUpperUnitriangular := by
  intro a b hab
  rw [Matrix.mul_apply, Fintype.sum_eq_single a]
  · rw [hM a a le_rfl, hM' a b hab, one_apply_eq, one_mul]
  · intro c hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hM a c h.le, one_apply_ne hca.symm, zero_mul]
    · rw [hM' c b (hab.trans h.le), one_apply_ne (hab.trans_lt h).ne', mul_zero]

/-- Every natural power of an upper unitriangular matrix is upper unitriangular. -/
theorem IsUpperUnitriangular.pow [Semiring R] {M : Matrix (Fin n) (Fin n) R}
    (hM : M.IsUpperUnitriangular) (k : ℕ) : (M ^ k).IsUpperUnitriangular := by
  induction k with
  | zero => exact isUpperUnitriangular_one
  | succ k ih => rw [pow_succ]; exact ih.mul hM

/-- An upper unitriangular matrix of size `n` over a ring of prime characteristic `p` has order
dividing `p ^ n`. -/
theorem IsUpperUnitriangular.pow_eq_one [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {M : Matrix (Fin n) (Fin n) R} (hM : M.IsUpperUnitriangular) : M ^ p ^ n = 1 := by
  obtain _ | n := n
  · exact Subsingleton.elim _ _
  have hN : ∀ a b, b ≤ a → (M - 1) a b = 0 := fun a b hab ↦ by
    rw [Matrix.sub_apply, hM a b hab, sub_self]
  have hnil : (M - 1) ^ p ^ (n + 1) = 0 := by
    ext a b
    have := Nat.lt_pow_self (n := n + 1) (Fact.out : p.Prime).one_lt
    exact pow_apply_eq_zero_of_lt_add hN _ (by omega)
  rw [← add_sub_cancel 1 M, add_pow_char_pow_of_commute p (n + 1) (Commute.one_left _), one_pow,
    hnil, add_zero]

variable (n R) in
/-- The subgroup of upper unitriangular matrices among the units of the matrix ring. -/
def upperUnitriangular [Ring R] :
    Subgroup (Matrix (Fin n) (Fin n) R)ˣ where
  carrier := {u | IsUpperUnitriangular (u : Matrix (Fin n) (Fin n) R)}
  one_mem' := isUpperUnitriangular_one
  mul_mem' hu hv := by
    rw [Set.mem_ofPred_eq, Units.val_mul]
    exact hu.mul hv
  inv_mem' {u} hu := by
    -- Writing `u = 1 - N`, the inverse is the finite Neumann series `∑ k < n, N ^ k`.
    have hN : ∀ a b, b ≤ a → (1 - (u : Matrix (Fin n) (Fin n) R)) a b = 0 := fun a b hab ↦ by
      rw [Matrix.sub_apply, hu a b hab, sub_self]
    have hinv : ((u⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) =
        ∑ k ∈ Finset.range n, (1 - (u : Matrix (Fin n) (Fin n) R)) ^ k := by
      have hnil : (1 - (u : Matrix (Fin n) (Fin n) R)) ^ n = 0 := by
        ext a b
        exact pow_apply_eq_zero_of_lt_add hN n (by omega)
      refine Units.inv_eq_of_mul_eq_one_right ?_
      simpa [hnil] using mul_neg_geom_sum (1 - (u : Matrix (Fin n) (Fin n) R)) n
    intro a b hab
    rw [hinv, Matrix.sum_apply, Finset.sum_eq_single 0, pow_zero]
    · exact fun k _ hk ↦ pow_apply_eq_zero_of_lt_add hN k (by omega)
    · exact fun h ↦ absurd (Finset.mem_range.2 a.pos) h

/-- A unit lies in `upperUnitriangular n R` iff its underlying matrix is upper unitriangular. -/
@[simp] theorem mem_upperUnitriangular [Ring R] {u : (Matrix (Fin n) (Fin n) R)ˣ} :
    u ∈ upperUnitriangular n R ↔ IsUpperUnitriangular (u : Matrix (Fin n) (Fin n) R) :=
  Iff.rfl

/-- Over a ring of prime characteristic `p`, the group of upper unitriangular matrices is a
`p`-group. -/
theorem isPGroup_upperUnitriangular [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p] :
    IsPGroup p (upperUnitriangular n R) := fun u ↦
  ⟨n, Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact (mem_upperUnitriangular.1 u.2).pow_eq_one))⟩

end Matrix
