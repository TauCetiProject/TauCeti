/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.EuclideanDual
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Algebra.Field.ZMod

/-!
# Weight divisibility for ternary codes

The self-dot-product of a ternary word is its Hamming weight modulo three. Consequently,
every word in a Euclidean self-orthogonal ternary code has weight divisible by three.
This supplies the weight constraint for self-dual codes such as the extended ternary Golay code.
-/

public section

namespace TauCeti

open Matrix

variable {ι : Type*} [Fintype ι]

/-- A ternary word has self-dot-product equal to its weight modulo three. -/
@[simp]
theorem dotProduct_self_eq_hammingNorm_ternary (x : ι → ZMod 3) :
    x ⬝ᵥ x = (hammingNorm x : ZMod 3) := by
  simp only [dotProduct, hammingNorm, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (by decide : ∀ a : ZMod 3, a * a = ((if a ≠ 0 then 1 else 0 : ℕ) : ZMod 3)) (x i)

/-- A ternary word is orthogonal to itself exactly when its weight is divisible by three. -/
theorem dotProduct_self_eq_zero_iff_three_dvd_hammingNorm (x : ι → ZMod 3) :
    x ⬝ᵥ x = 0 ↔ 3 ∣ hammingNorm x := by
  rw [dotProduct_self_eq_hammingNorm_ternary, ZMod.natCast_eq_zero_iff]

/-- Every word in a Euclidean self-orthogonal ternary code has weight divisible by three. -/
theorem three_dvd_hammingNorm_of_le_euclideanDual {C : Submodule (ZMod 3) (ι → ZMod 3)}
    (hC : C ≤ C.euclideanDual) {x : ι → ZMod 3} (hx : x ∈ C) :
    3 ∣ hammingNorm x := by
  exact (dotProduct_self_eq_zero_iff_three_dvd_hammingNorm x).mp
    (Submodule.mem_euclideanDual.mp (hC hx) x hx)

end TauCeti
