/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Stabilizers under an action by monoid automorphisms

When a group `G` acts on a monoid `M` by monoid automorphisms (`MulDistribMulAction G M`), the
stabilizers of elements of `M` are compatible with its multiplication: every element of `G` fixes
`1`, an element fixing `a` and `b` fixes `a * b`, and an element fixing `a` fixes every power of
`a`. When `M` is a group, `a` and `a⁻¹` have the same stabilizer. When `M` has unique roots (for
instance, when it is commutative and torsion-free), `a ^ n` and `a` have the same stabilizer for
`n ≠ 0`.

## Main declarations

* `MulAction.stabilizer_one`: the stabilizer of `1` is the whole group;
* `MulAction.stabilizer_inv`: `a⁻¹` and `a` have the same stabilizer;
* `MulAction.stabilizer_inf_stabilizer_le_stabilizer_mul`: the stabilizers of `a` and `b` fix
  `a * b`;
* `MulAction.stabilizer_pow`, `MulAction.stabilizer_zpow`: with unique roots, `a ^ n` and `a`
  have the same stabilizer for `n ≠ 0`.
-/

public section

namespace MulAction

variable {G M : Type*} [Group G]

section Monoid

variable [Monoid M] [MulDistribMulAction G M]

/-- Under an action by monoid automorphisms, every element fixes `1`. -/
@[simp]
theorem stabilizer_one : stabilizer G (1 : M) = ⊤ :=
  eq_top_iff.2 fun g _ ↦ smul_one g

/-- Under an action by monoid automorphisms, an element fixing `a` and `b` fixes `a * b`. -/
theorem stabilizer_inf_stabilizer_le_stabilizer_mul (a b : M) :
    stabilizer G a ⊓ stabilizer G b ≤ stabilizer G (a * b) := fun g hg ↦ by
  rw [mem_stabilizer_iff, smul_mul', mem_stabilizer_iff.1 hg.1, mem_stabilizer_iff.1 hg.2]

/-- Under an action by monoid automorphisms, an element fixing `a` fixes its natural powers. -/
theorem le_stabilizer_pow (a : M) (n : ℕ) : stabilizer G a ≤ stabilizer G (a ^ n) :=
  fun g hg ↦ by rw [mem_stabilizer_iff, smul_pow', mem_stabilizer_iff.1 hg]

/-- In a monoid with unique roots acted on by monoid automorphisms, `a ^ n` and `a` have the same
stabilizer for `n ≠ 0`. -/
theorem stabilizer_pow [HasUniqueRoots M] (a : M) {n : ℕ} (hn : n ≠ 0) :
    stabilizer G (a ^ n) = stabilizer G a := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, smul_pow', pow_left_inj hn]

end Monoid

section Group

variable [Group M] [MulDistribMulAction G M]

/-- Under an action by group automorphisms, `a⁻¹` and `a` have the same stabilizer. -/
@[simp]
theorem stabilizer_inv (a : M) : stabilizer G a⁻¹ = stabilizer G a := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, smul_inv', inv_inj]

/-- Under an action by group automorphisms, an element fixing `a` fixes its integer powers. -/
theorem le_stabilizer_zpow (a : M) (n : ℤ) : stabilizer G a ≤ stabilizer G (a ^ n) :=
  fun g hg ↦ by rw [mem_stabilizer_iff, smul_zpow', mem_stabilizer_iff.1 hg]

/-- In a group with unique roots acted on by group automorphisms, `a ^ n` and `a` have the same
stabilizer for `n ≠ 0`. -/
theorem stabilizer_zpow [HasUniqueRoots M] (a : M) {n : ℤ} (hn : n ≠ 0) :
    stabilizer G (a ^ n) = stabilizer G a := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, smul_zpow', zpow_left_inj hn]

end Group

end MulAction
