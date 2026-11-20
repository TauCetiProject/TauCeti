/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Finite modules over rings with `p` in the Jacobson radical

If a natural number `p` lies in the Jacobson radical of a commutative ring `R`, every finite
`R`-module is an additive `p`-group: for `i < j` with `p ^ i • x = p ^ j • x`, the scalar
`1 - p ^ (j - i)` is a unit, so `p ^ i • x = 0`. For prime `p`, Mathlib's `IsAddPGroup.iff_card`
then says that the cardinality of a finite `R`-module is a power of `p`. The typical case is a
local ring of residue characteristic `p`, such as a discrete valuation ring whose residue field is
finite of characteristic `p`, or a power series ring over one; this is how orders of finite
Iwasawa modules are written as powers of `p`.
-/

public section

namespace IsAddPGroup

/-- **Finite modules are `p`-groups when `p` lies in the Jacobson radical.** If the natural number
`p` lies in the Jacobson radical of `R`, then every finite `R`-module is an additive `p`-group. -/
theorem of_natCast_mem_jacobson {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [Finite N] {p : ℕ} (hp : (p : R) ∈ Ring.jacobson R) : IsAddPGroup p N := by
  intro x
  -- Two of the multiples `p ^ n • x` coincide.
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite fun n : ℕ ↦ ((p : R) ^ n) • x
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm h.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
  refine ⟨i, ?_⟩
  -- The scalar `1 - p ^ (j - i)` is a unit and kills `p ^ i • x`.
  have hu : IsUnit (1 - (p : R) ^ (j - i)) := by
    have := Ring.mem_jacobson_iff.1 (Ideal.pow_mem_of_mem _ hp _ (Nat.sub_pos_of_lt hlt)) (-1)
    rwa [mul_neg_one, neg_add_eq_sub] at this
  have h0 : (1 - (p : R) ^ (j - i)) • ((p : R) ^ i • x) = (1 - (p : R) ^ (j - i)) • 0 := by
    rw [smul_zero, sub_smul, one_smul, smul_smul, ← pow_add, Nat.sub_add_cancel hlt.le]
    exact sub_eq_zero.2 h
  rw [← Nat.cast_smul_eq_nsmul R, Nat.cast_pow]
  exact hu.smul_left_cancel.1 h0

end IsAddPGroup
