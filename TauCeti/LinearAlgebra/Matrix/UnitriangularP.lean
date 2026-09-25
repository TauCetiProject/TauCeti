/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Matrix.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.CharP

/-!
# Finite upper unitriangular matrix groups over `ZMod p`

Upper unitriangular matrices over `ZMod p` form a `p`-group of units. A bound on their orders
comes from nilpotence of strictly upper triangular matrices.
-/

public section

namespace Matrix

variable (D : ℕ) {p : ℕ}

/-- A strictly upper triangular matrix raised to the power `j` is supported on entries `(a, b)`
with `a + j ≤ b`. -/
theorem pow_apply_ne_zero_le {R : Type*} [CommRing R]
    {N : Matrix (Fin (D + 1)) (Fin (D + 1)) R} (hN : ∀ a b, b ≤ a → N a b = 0) (j : ℕ)
    (a b : Fin (D + 1)) (h : (N ^ j) a b ≠ 0) : (a : ℕ) + j ≤ b := by
  induction j generalizing b with
  | zero =>
    rw [pow_zero, Matrix.one_apply] at h
    split_ifs at h with hab
    · subst hab; simp
    · exact absurd rfl h
  | succ j ih =>
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h₁ := ih c (left_ne_zero_of_mul hc)
    have h₂ : c < b := lt_of_not_ge fun hbc ↦ right_ne_zero_of_mul hc (hN c b hbc)
    have : (c : ℕ) < b := h₂
    omega

/-- Upper unitriangularity of a square matrix over `ZMod p`. -/
def IsUnitri (p D : ℕ) (M : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)) : Prop :=
  ∀ a b, b ≤ a → M a b = (1 : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)) a b

/-- A matrix is upper unitriangular iff its diagonal entries are `1` and its entries below the
diagonal are `0`. -/
theorem isUnitri_iff {M : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)} :
    IsUnitri p D M ↔ (∀ a, M a a = 1) ∧ ∀ a b, b < a → M a b = 0 := by
  refine ⟨fun h ↦ ⟨fun a ↦ by rw [h a a le_rfl, one_apply_eq],
    fun a b hab ↦ by rw [h a b hab.le, one_apply_ne hab.ne']⟩, fun ⟨hd, hl⟩ a b hab ↦ ?_⟩
  rcases hab.lt_or_eq with hab | rfl
  · rw [hl a b hab, one_apply_ne hab.ne']
  · rw [hd, one_apply_eq]

/-- The product of upper unitriangular matrices is upper unitriangular. -/
theorem IsUnitri.mul {M M' : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)}
    (hM : IsUnitri p D M) (hM' : IsUnitri p D M') : IsUnitri p D (M * M') := by
  intro a b hab
  rw [Matrix.mul_apply, Fintype.sum_eq_single a]
  · rw [hM a a le_rfl, hM' a b hab, Matrix.one_apply_eq, one_mul]
  · intro c hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hM a c h.le, Matrix.one_apply_ne (Ne.symm hca), zero_mul]
    · rw [hM' c b (hab.trans h.le), Matrix.one_apply_ne (ne_of_gt (lt_of_le_of_lt hab h)),
        mul_zero]

/-- Every natural power of an upper unitriangular matrix is upper unitriangular. -/
theorem IsUnitri.pow {M : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)}
    (hM : IsUnitri p D M) (k : ℕ) : IsUnitri p D (M ^ k) := by
  induction k with
  | zero => exact fun _ _ _ ↦ rfl
  | succ k ih => rw [pow_succ]; exact ih.mul D hM

variable [hp : Fact p.Prime]

/-- An upper unitriangular matrix over `ZMod p` of size `D + 1` has order dividing
`p ^ (D + 1)`. -/
theorem IsUnitri.pow_eq_one {M : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)}
    (hM : IsUnitri p D M) : M ^ p ^ (D + 1) = 1 := by
  have hN : ∀ a b, b ≤ a → (M - 1) a b = 0 := fun a b hab ↦ by
    rw [Matrix.sub_apply, hM a b hab, sub_self]
  have hnil : (M - 1) ^ (D + 1) = 0 := by
    ext a b
    by_contra h
    have := pow_apply_ne_zero_le D hN (D + 1) a b h
    omega
  calc M ^ p ^ (D + 1) = (1 + (M - 1)) ^ p ^ (D + 1) := by rw [add_sub_cancel]
    _ = 1 := by
      rw [add_pow_char_pow_of_commute p (D + 1) (Commute.one_left _), one_pow,
        pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le hnil, add_zero]

/-- The subgroup of upper unitriangular matrices over `ZMod p`. -/
def unitriangular : Subgroup (Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p))ˣ where
  carrier := {u | IsUnitri p D u}
  one_mem' := fun _ _ _ ↦ rfl
  mul_mem' {u v} hu hv := by
    rw [Set.mem_ofPred, Units.val_mul]
    exact hu.mul D hv
  inv_mem' {u} hu := by
    have hpow : u ^ p ^ (D + 1) = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hu.pow_eq_one D)
    have hinv : u⁻¹ = u ^ (p ^ (D + 1) - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos), hpow]
    rw [hinv, Set.mem_ofPred, Units.val_pow_eq_pow_val]
    exact hu.pow D _

/-- A unit lies in `unitriangular D` iff its underlying matrix is upper unitriangular. -/
@[simp] theorem mem_unitriangular {u : (Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p))ˣ} :
    u ∈ unitriangular D ↔ IsUnitri p D u :=
  Iff.rfl

/-- The group of upper unitriangular matrices over `ZMod p` is a `p`-group. -/
theorem isPGroup_unitriangular : IsPGroup p (unitriangular (p := p) D) := fun u ↦
  ⟨D + 1, Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact ((mem_unitriangular D).1 u.2).pow_eq_one D))⟩

end Matrix
