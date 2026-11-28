/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.SumTwoSquares
import TauCeti.NumberTheory.NumberField.CMField.Basic
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Integral norms from a CM field containing a fourth root of unity

A prime that is a sum of two squares is the product of an algebraic integer and its complex
conjugate in any CM field containing a primitive fourth root of unity. In particular, this
applies to primes congruent to `1` modulo `4` and to CM fields containing roots of unity of
order divisible by `4`.
-/

public section

open NumberField NumberField.IsCMField

namespace Nat.Prime

/-- In a CM field containing a primitive fourth root of unity, every prime other than those
congruent to `3` modulo `4` is an integral relative norm to the maximal real subfield. -/
theorem exists_mul_ringOfIntegersComplexConj_eq {p : ℕ} (hp : p.Prime) (hp4 : p % 4 ≠ 3)
    {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E]
    {i : E} (hi : IsPrimitiveRoot i 4) :
    ∃ z : 𝓞 E, z * ringOfIntegersComplexConj E z = p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hp4
  let j : 𝓞 E := ⟨i, hi.isIntegral (by decide)⟩
  have hsq : i ^ 2 = -1 := hi.sq_eq_neg_one
  have hconj : i * complexConj E i = 1 :=
    mul_complexConj_eq_one_of_pow_eq (by decide) hi.pow_eq_one (by simp)
  have hci : complexConj E i = -i := by
    apply mul_left_cancel₀ (hi.ne_zero (by decide))
    simpa only [mul_neg, ← pow_two, hsq, neg_neg] using hconj
  refine ⟨(a : 𝓞 E) + (b : 𝓞 E) * j, RingOfIntegers.ext ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, map_mul,
    ← RingOfIntegers.coe_eq_algebraMap (ringOfIntegersComplexConj E _),
    coe_ringOfIntegersComplexConj]
  have hj : algebraMap (𝓞 E) E j = i := RingOfIntegers.map_mk _ _
  simp only [map_add, map_mul, map_natCast, hj, hci]
  calc
    _ = (a : E) ^ 2 - (b : E) ^ 2 * i ^ 2 := by ring
    _ = p := by simpa [hsq] using (congrArg (fun n : ℕ ↦ (n : E)) hab)

end Nat.Prime
