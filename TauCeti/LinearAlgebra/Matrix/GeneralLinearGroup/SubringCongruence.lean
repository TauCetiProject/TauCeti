/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Congruence subgroups of `GL_n` attached to a subring and a unit

Let `R` be a commutative ring, `𝒪 ⊆ R` a subring and `g` a unit of `R`. The invertible matrices
`γ ∈ GL_n(R)` that are integral over `𝒪`, in the sense that the entries of `γ` and of `γ⁻¹` lie in
`𝒪`, and that are congruent to `1` modulo `g`, in the sense that `g⁻¹ (γ - 1)` has its entries in
`𝒪`, form a subgroup `TauCeti.subringCongruenceSubgroup n 𝒪 g` of `GL_n(R)`. The unit `g` need not
lie in `𝒪`. For the finite adeles `R` of a number field, the integral finite adeles `𝒪` and a
finite idele `g`, these are the principal congruence subgroups of `GL_n` of level `g`; intersected
with a unitary group they are the principal congruence levels of algebraic modular forms.

## Main definitions

* `TauCeti.subringCongruenceSubgroup n 𝒪 g`: the subgroup of `GL_n(R)` described above.

## Main results

* `TauCeti.mem_subringCongruenceSubgroup`: membership in terms of entries.
-/

public section

open Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] {𝒪 : Subring R}

omit [DecidableEq n] in
/-- A product of matrices with entries in a subring has entries in it. -/
private theorem mul_apply_mem {M N : Matrix n n R} (hM : ∀ i j, M i j ∈ 𝒪)
    (hN : ∀ i j, N i j ∈ 𝒪) (i j : n) : (M * N) i j ∈ 𝒪 := by
  rw [Matrix.mul_apply]
  exact 𝒪.sum_mem fun k _ => 𝒪.mul_mem (hM i k) (hN k j)

omit [Fintype n] in
/-- The identity matrix has entries in every subring. -/
private theorem one_apply_mem (i j : n) : (1 : Matrix n n R) i j ∈ 𝒪 := by
  rw [Matrix.one_apply]
  split_ifs
  exacts [𝒪.one_mem, 𝒪.zero_mem]

variable (n 𝒪) in
/-- The **congruence subgroup of `GL_n` of level `g` over a subring `𝒪`**: the invertible matrices
`γ` whose entries and whose inverse's entries lie in `𝒪`, and such that `g⁻¹ (γ - 1)` has its
entries in `𝒪`. -/
def subringCongruenceSubgroup (g : Rˣ) : Subgroup (GL n R) where
  carrier := {γ | (∀ i j, (γ : Matrix n n R) i j ∈ 𝒪) ∧
    (∀ i j, ((γ⁻¹ : GL n R) : Matrix n n R) i j ∈ 𝒪) ∧
    ∀ i j, ((g⁻¹ : Rˣ) : R) * ((γ : Matrix n n R) - 1) i j ∈ 𝒪}
  one_mem' := ⟨one_apply_mem, by simpa using one_apply_mem, by simp⟩
  mul_mem' {x y} hx hy := by
    refine ⟨mul_apply_mem hx.1 hy.1, ?_, fun i j => ?_⟩
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact mul_apply_mem hy.2.1 hx.2.1
    · -- `x y - 1 = (x - 1) y + (y - 1)`.
      have h : ((g⁻¹ : Rˣ) : R) * (((x * y : GL n R) : Matrix n n R) - 1) i j =
          (((g⁻¹ : Rˣ) : R) • ((x : Matrix n n R) - 1) * (y : Matrix n n R)) i j +
            ((g⁻¹ : Rˣ) : R) * ((y : Matrix n n R) - 1) i j := by
        simp only [Units.val_mul, Matrix.sub_apply, Matrix.smul_mul, Matrix.smul_apply,
          sub_mul, Matrix.one_mul, smul_eq_mul, ← mul_add]
        ring
      rw [h]
      exact 𝒪.add_mem (mul_apply_mem (fun i j => by simpa using hx.2.2 i j) hy.1 i j) (hy.2.2 i j)
  inv_mem' {x} hx := by
    refine ⟨hx.2.1, by simpa using hx.1, fun i j => ?_⟩
    · -- `x⁻¹ - 1 = -x⁻¹ (x - 1)`.
      have h : ((g⁻¹ : Rˣ) : R) * (((x⁻¹ : GL n R) : Matrix n n R) - 1) i j =
          -(((x⁻¹ : GL n R) : Matrix n n R) *
            (((g⁻¹ : Rˣ) : R) • ((x : Matrix n n R) - 1))) i j := by
        simp only [Matrix.sub_apply, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
          Matrix.smul_apply, smul_eq_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
        ring
      rw [h]
      exact 𝒪.neg_mem (mul_apply_mem hx.2.1 (fun i j => by simpa using hx.2.2 i j) i j)

/-- Membership in the congruence subgroup of level `g` over `𝒪`, entry by entry. -/
@[simp]
theorem mem_subringCongruenceSubgroup {g : Rˣ} {γ : GL n R} :
    γ ∈ subringCongruenceSubgroup n 𝒪 g ↔ (∀ i j, (γ : Matrix n n R) i j ∈ 𝒪) ∧
      (∀ i j, ((γ⁻¹ : GL n R) : Matrix n n R) i j ∈ 𝒪) ∧
      ∀ i j, ((g⁻¹ : Rˣ) : R) * ((γ : Matrix n n R) - 1) i j ∈ 𝒪 :=
  Iff.rfl

end TauCeti
