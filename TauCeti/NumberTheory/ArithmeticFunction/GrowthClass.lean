/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import TauCeti.NumberTheory.ArithmeticFunction.Additive
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds

/-!
# The multiplicative growth class of the binary sieve

A real arithmetic function `f` belongs to the class `M(A, B, ε)`, for `A ≥ 1`, `B > 0` and
`ε > 0`, if it is multiplicative, nonnegative, and satisfies both `f(n) ≤ A ^ Ω(n)` and
`f(n) ≤ B n ^ ε` for every `n > 0`, where `Ω` counts prime factors with multiplicity. This is the
class of functions summed over the values of a binary polynomial in Khayutin's sieve; the first
bound controls `f` at numbers with few prime factors and the second its overall size.

## Main definitions

* `TauCeti.SieveGrowthClass A B ε f`: the predicate `f ∈ M(A, B, ε)`.

## Main results

* `TauCeti.SieveGrowthClass.le_min`, `TauCeti.SieveGrowthClass.apply_prime_pow_le`: the bound
  `f(n) ≤ min (A ^ Ω(n)) (B n ^ ε)`, and at prime powers `f(p ^ k) ≤ min (A ^ k) (B p ^ (k ε))`.
* `TauCeti.SieveGrowthClass.one_le_const`: `B ≥ 1` in a nonempty class, from the value at `1`.
* `TauCeti.SieveGrowthClass.mono`: the class grows with each of `A`, `B` and `ε`.
* `TauCeti.sieveGrowthClass_zeta`: `ζ ∈ M(1, 1, ε)` for every `ε > 0`.
* `TauCeti.sieveGrowthClass_of_le_pow_cardFactors`: for `A > 1`, a nonnegative multiplicative `f`
  with `f(n) ≤ A ^ Ω(n)` belongs to `M(A, 1, log₂ A)`, since `A ^ Ω(n) ≤ n ^ log₂ A`.

## References

* I. Khayutin, *Joint equidistribution of CM points*, Ann. of Math. 189 (2019), 145–276,
  Definition 9.6.
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.Omega ArithmeticFunction.zeta

namespace TauCeti

variable {A A' B B' ε ε' : ℝ} {f : ArithmeticFunction ℝ}

/-- The multiplicative growth class `M(A, B, ε)`: a real arithmetic function `f` belongs to it if
`A ≥ 1`, `B > 0`, `ε > 0`, `f` is multiplicative and nonnegative, and
`f(n) ≤ min (A ^ Ω(n)) (B n ^ ε)` for every `n ≠ 0`. -/
structure SieveGrowthClass (A B ε : ℝ) (f : ArithmeticFunction ℝ) : Prop where
  /-- The base `A` of the bound in the number of prime factors is at least `1`. -/
  one_le_base : 1 ≤ A
  /-- The constant `B` of the power bound is positive. -/
  const_pos : 0 < B
  /-- The exponent `ε` of the power bound is positive. -/
  exponent_pos : 0 < ε
  /-- The function is multiplicative. -/
  isMultiplicative : f.IsMultiplicative
  /-- The function is nonnegative. -/
  nonneg : ∀ n, 0 ≤ f n
  /-- The bound `f(n) ≤ A ^ Ω(n)` at nonzero `n`. -/
  le_pow_cardFactors : ∀ n, n ≠ 0 → f n ≤ A ^ Ω n
  /-- The bound `f(n) ≤ B n ^ ε` at nonzero `n`. -/
  le_mul_rpow : ∀ n, n ≠ 0 → f n ≤ B * (n : ℝ) ^ ε

namespace SieveGrowthClass

/-- A function of the class `M(A, B, ε)` satisfies `f(n) ≤ min (A ^ Ω(n)) (B n ^ ε)` at `n ≠ 0`. -/
theorem le_min (h : SieveGrowthClass A B ε f) {n : ℕ} (hn : n ≠ 0) :
    f n ≤ min (A ^ Ω n) (B * (n : ℝ) ^ ε) :=
  _root_.le_min (h.le_pow_cardFactors n hn) (h.le_mul_rpow n hn)

/-- A function of the class `M(A, B, ε)` is multiplicative on coprime arguments. -/
theorem map_mul_of_coprime (h : SieveGrowthClass A B ε f) {a b : ℕ} (hab : a.Coprime b) :
    f (a * b) = f a * f b :=
  h.isMultiplicative.map_mul_of_coprime hab

/-- If the class `M(A, B, ε)` is nonempty then `B ≥ 1`: a multiplicative function has value `1`
at `1`. -/
theorem one_le_const (h : SieveGrowthClass A B ε f) : 1 ≤ B := by
  simpa [h.isMultiplicative.map_one] using h.le_mul_rpow 1 one_ne_zero

/-- At a prime power, a function of the class `M(A, B, ε)` satisfies
`f(p ^ k) ≤ min (A ^ k) (B p ^ (k ε))`. -/
theorem apply_prime_pow_le (h : SieveGrowthClass A B ε f) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    f (p ^ k) ≤ min (A ^ k) (B * (p : ℝ) ^ ((k : ℝ) * ε)) := by
  have hle := h.le_min (pow_ne_zero k hp.ne_zero)
  rwa [cardFactors_apply_prime_pow hp, Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) k,
    ← Real.rpow_mul p.cast_nonneg] at hle

/-- The class `M(A, B, ε)` grows with each of its three parameters. -/
theorem mono (h : SieveGrowthClass A B ε f) (hA : A ≤ A') (hB : B ≤ B') (hε : ε ≤ ε') :
    SieveGrowthClass A' B' ε' f where
  one_le_base := h.one_le_base.trans hA
  const_pos := h.const_pos.trans_le hB
  exponent_pos := h.exponent_pos.trans_le hε
  isMultiplicative := h.isMultiplicative
  nonneg := h.nonneg
  le_pow_cardFactors n hn := (h.le_pow_cardFactors n hn).trans
    (pow_le_pow_left₀ (zero_le_one.trans h.one_le_base) hA _)
  le_mul_rpow n hn := (h.le_mul_rpow n hn).trans <| mul_le_mul hB
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 hn)) hε)
    (Real.rpow_nonneg n.cast_nonneg _) (h.const_pos.le.trans hB)

end SieveGrowthClass

/-- The constant function `ζ` (equal to `1` at every `n ≠ 0`) belongs to `M(1, 1, ε)` for every
`ε > 0`. -/
theorem sieveGrowthClass_zeta (hε : 0 < ε) :
    SieveGrowthClass 1 1 ε ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) where
  one_le_base := le_rfl
  const_pos := one_pos
  exponent_pos := hε
  isMultiplicative := isMultiplicative_zeta.natCast
  nonneg n := by
    rw [natCoe_apply]
    exact Nat.cast_nonneg _
  le_pow_cardFactors n hn := by
    rw [natCoe_apply, zeta_apply_ne hn, Nat.cast_one, one_pow]
  le_mul_rpow n hn := by
    rw [natCoe_apply, zeta_apply_ne hn, Nat.cast_one, one_mul]
    exact Real.one_le_rpow (Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 hn)) hε.le

/-- For `A > 1`, a nonnegative multiplicative function with `f(n) ≤ A ^ Ω(n)` at every `n ≠ 0`
belongs to `M(A, 1, log₂ A)`: the power bound follows from `A ^ Ω(n) ≤ n ^ log₂ A`. -/
theorem sieveGrowthClass_of_le_pow_cardFactors (hA : 1 < A) (hf : f.IsMultiplicative)
    (hf0 : ∀ n, 0 ≤ f n) (hle : ∀ n, n ≠ 0 → f n ≤ A ^ Ω n) :
    SieveGrowthClass A 1 (Real.logb 2 A) f where
  one_le_base := hA.le
  const_pos := one_pos
  exponent_pos := Real.logb_pos one_lt_two hA
  isMultiplicative := hf
  nonneg := hf0
  le_pow_cardFactors := hle
  le_mul_rpow n hn := by
    rw [one_mul]
    exact (hle n hn).trans (pow_cardFactors_le_rpow_logb hA.le hn)

/-! ### Examples -/

/-- `ζ` belongs to `M(1, 1, 1)`. -/
example : SieveGrowthClass 1 1 1 ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) :=
  sieveGrowthClass_zeta one_pos

/-- `-ζ` belongs to no class: it is negative at `1`. -/
example : ¬SieveGrowthClass A B ε (-((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) :=
  fun h ↦ by
    have h1 := h.nonneg 1
    simp at h1
    linarith

/-- `n ↦ 2 ^ Ω(n)` belongs to `M(2, 1, 1)`, and its value at `4` is `4`, not `2`: prime factors
are counted with multiplicity. -/
example : SieveGrowthClass 2 1 1 (powOfAdditive (2 : ℝ) Ω) ∧ powOfAdditive (2 : ℝ) Ω 4 = 4 := by
  refine ⟨?_, ?_⟩
  · have h := sieveGrowthClass_of_le_pow_cardFactors one_lt_two
      (isAdditive_cardFactors.isMultiplicative_powOfAdditive (2 : ℝ)) (fun n ↦ ?_)
      fun n hn ↦ (powOfAdditive_apply (2 : ℝ) Ω hn).le
    · rwa [Real.logb_self_eq_one one_lt_two] at h
    · rcases eq_or_ne n 0 with rfl | hn
      · exact (powOfAdditive_apply_zero (2 : ℝ) Ω).ge
      · rw [powOfAdditive_apply (2 : ℝ) Ω hn]
        positivity
  · have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [powOfAdditive_apply (2 : ℝ) Ω (by norm_num), h4,
      cardFactors_apply_prime_pow Nat.prime_two]
    norm_num

/-- `n ↦ 2 ^ Ω(n)` is not in `M(1, 1, 1)`: at `n = 2` its value `2` exceeds `1 ^ Ω(2) = 1`. -/
example : ¬SieveGrowthClass 1 1 1 (powOfAdditive (2 : ℝ) Ω) := fun h ↦ by
  have h2 := h.le_pow_cardFactors 2 two_ne_zero
  rw [powOfAdditive_apply (2 : ℝ) Ω two_ne_zero, cardFactors_apply_prime Nat.prime_two] at h2
  norm_num at h2

end TauCeti
