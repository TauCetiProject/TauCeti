/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Congruence subgroups of `GL_n` attached to a subring and a unit

Let `R` be a commutative ring, `𝒪 ⊆ R` a subring and `g` a unit of `R`. The invertible matrices
`γ ∈ GL_n(R)` that are integral over `𝒪`, in the sense that `γ` and `γ⁻¹` lie in the matrix
subring `𝒪.matrix` (so `γ` lies in the units `(𝒪.matrix).toSubmonoid.units` of that subring), and
that are congruent to `1` modulo `g`, in the sense that `g⁻¹ (γ - 1)` lies in `𝒪.matrix`, form a
subgroup `TauCeti.subringCongruenceSubgroup n 𝒪 g` of `GL_n(R)`. The unit `g` need not lie in `𝒪`.
For the finite adeles `R` of a number field, the integral finite adeles `𝒪` and a finite idele `g`
that is integral (lies in `𝒪`), these are the principal congruence subgroups of `GL_n` of level
`g`; intersected with a unitary group they are the principal congruence levels of algebraic
modular forms.

## Main definitions

* `TauCeti.subringCongruenceSubgroup n 𝒪 g`: the subgroup of `GL_n(R)` described above.

## Main results

* `TauCeti.mem_subringCongruenceSubgroup`: membership in terms of the matrix subring `𝒪.matrix`.
-/

public section

open Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] {𝒪 : Subring R}

variable (n 𝒪) in
/-- The **congruence subgroup of `GL_n` of level `g` over a subring `𝒪`**: the invertible matrices
`γ` such that `γ` and `γ⁻¹` lie in the matrix subring `𝒪.matrix`, and such that `g⁻¹ (γ - 1)` lies
in `𝒪.matrix`. -/
def subringCongruenceSubgroup (g : Rˣ) : Subgroup (GL n R) where
  carrier := {γ | γ ∈ (𝒪.matrix (n := n)).toSubmonoid.units ∧
    ((g⁻¹ : Rˣ) : R) • ((γ : Matrix n n R) - 1) ∈ 𝒪.matrix}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' {x y} hx hy := by
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    -- `x y - 1 = (x - 1) y + (y - 1)`.
    have h : ((g⁻¹ : Rˣ) : R) • (((x * y : GL n R) : Matrix n n R) - 1) =
        ((g⁻¹ : Rˣ) : R) • ((x : Matrix n n R) - 1) * (y : Matrix n n R) +
          ((g⁻¹ : Rˣ) : R) • ((y : Matrix n n R) - 1) := by
      rw [Units.val_mul, Matrix.smul_mul, sub_mul, Matrix.one_mul, ← smul_add,
        sub_add_sub_cancel]
    rw [h]
    exact add_mem (mul_mem hx.2 ((Submonoid.mem_units_iff _ _).1 hy.1).1) hy.2
  inv_mem' {x} hx := by
    refine ⟨inv_mem hx.1, ?_⟩
    -- `x⁻¹ - 1 = -x⁻¹ (x - 1)`.
    have h : ((g⁻¹ : Rˣ) : R) • (((x⁻¹ : GL n R) : Matrix n n R) - 1) =
        -(((x⁻¹ : GL n R) : Matrix n n R) * (((g⁻¹ : Rˣ) : R) • ((x : Matrix n n R) - 1))) := by
      rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, ← smul_neg, neg_sub]
    rw [h]
    exact neg_mem (mul_mem ((Submonoid.mem_units_iff _ _).1 hx.1).2 hx.2)

/-- Membership in the congruence subgroup of level `g` over `𝒪`, in terms of the matrix subring
`𝒪.matrix`. -/
@[simp]
theorem mem_subringCongruenceSubgroup {g : Rˣ} {γ : GL n R} :
    γ ∈ subringCongruenceSubgroup n 𝒪 g ↔ (γ : Matrix n n R) ∈ 𝒪.matrix ∧
      ((γ⁻¹ : GL n R) : Matrix n n R) ∈ 𝒪.matrix ∧
      ((g⁻¹ : Rˣ) : R) • ((γ : Matrix n n R) - 1) ∈ 𝒪.matrix :=
  and_assoc

end TauCeti
