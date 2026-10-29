/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.IsPrimary

/-!
# Powers of maximal ideals

The radical of a power `P ^ n` of a maximal ideal is `P`, so `P ^ n` is primary. Concretely, an
element outside `P` is a nonzerodivisor modulo `P ^ n`.

## Main results

* `Ideal.mem_pow_of_mul_mem`: if `x ∉ P` and `x * y ∈ P ^ n` for a maximal ideal `P`, then
  `y ∈ P ^ n`.
-/

public section

namespace Ideal

/-- A power of a maximal ideal is primary: if `x ∉ P` and `x * y ∈ P ^ n`, then `y ∈ P ^ n`. -/
theorem mem_pow_of_mul_mem {R : Type*} [CommRing R] {P : Ideal R} [P.IsMaximal] {n : ℕ}
    {x y : R} (hx : x ∉ P) (hxy : x * y ∈ P ^ n) : y ∈ P ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hrad : (P ^ n).radical = P := by
    rw [radical_pow P hn.ne', IsPrime.radical inferInstance]
  have hmax : (P ^ n).radical.IsMaximal := by rw [hrad]; infer_instance
  have hprim := isPrimary_iff.1 (isPrimary_of_isMaximal_radical hmax)
  rw [mul_comm] at hxy
  exact (hprim.2 hxy).resolve_right (by rwa [hrad])

end Ideal
