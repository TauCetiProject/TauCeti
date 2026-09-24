/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Rat
import Mathlib.Tactic.Ring

/-!
# Rational spans of integer subgroups

An element of the rational span of a subgroup of integer-valued functions lies in that subgroup
after multiplication by some positive integer. This denominator-clearing result is used to pass
from rational spans back to integer lattices.
-/

public section

namespace TauCeti

variable {ι : Type*}

/-- An element of the rational span of a subgroup `P` of `ι → ℤ` becomes an element of `P` after
multiplication by some positive integer. -/
theorem AddSubgroup.exists_nat_mul_eq_intCast_of_mem_span {P : AddSubgroup (ι → ℤ)}
    {x : ι → ℚ} (hx : x ∈ Submodule.span ℚ ((fun p : ι → ℤ => ((↑) : ℤ → ℚ) ∘ p) '' P)) :
    ∃ N : ℕ, 0 < N ∧ ∃ p ∈ P, ∀ i, (p i : ℚ) = N * x i := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨1, one_pos, p, hp, fun i => by simp⟩
  | zero => exact ⟨1, one_pos, 0, zero_mem P, fun i => by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨M, hM, p, hp, hpy⟩ := hy
    obtain ⟨N, hN, q, hq, hqz⟩ := hz
    refine ⟨M * N, mul_pos hM hN, N • p + M • q, add_mem (nsmul_mem hp N) (nsmul_mem hq M),
      fun i => ?_⟩
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    push_cast [nsmul_eq_mul, hpy, hqz, Pi.add_apply]
    ring
  | smul r y _ hy =>
    obtain ⟨N, hN, p, hp, hpy⟩ := hy
    refine ⟨r.den * N, mul_pos r.den_pos hN, r.num • p, zsmul_mem hp r.num, fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, hpy, Nat.cast_mul]
    rw [← Rat.mul_den_eq_num]
    ring

end TauCeti
