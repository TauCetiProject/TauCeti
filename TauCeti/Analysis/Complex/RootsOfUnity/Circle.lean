/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import TauCeti.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Roots of unity in the circle

Mathlib's `ZMod.toCircle : AddChar (ZMod n) Circle` sends `j` to `e^{2πi j / n}`. This file records
that its values are exactly the `n`-th roots of unity of the circle, in the form used to compare
points of the circle with the same `n`-th power. These are the facts needed to identify the orbits
of the cyclic rotation groups `ℤ/n` acting on the circle, as in the quotient constructions of lens
spaces.

## Main results

* `ZMod.isPrimitiveRoot_stdAddChar_one`: the standard complex character at `1` is primitive.
* `MonoidHom.exists_map_stdAddChar_one_eq`: an injective multiplicative map permutes primitive
  standard character values.
* `ZMod.toCircle_pow_eq_one`: every value of `ZMod.toCircle` is an `n`-th root of unity.
* `ZMod.exists_toCircle_eq_of_pow_eq_one`: every `n`-th root of unity in the circle is a value
  of `ZMod.toCircle`.
* `ZMod.toCircle_pow_mul_eq_self_iff`: for `n` coprime to `b`, multiplication by `toCircle k ^ b`
  fixes a nonzero complex number only for `k = 0`, so `ℤ/n` acts freely on `ℂ \ {0}` this way.
* `ZMod.natCard_toCircle_pow_eq_one`: for arbitrary `b`, exactly `gcd(n, b)` elements `k` have
  `toCircle k ^ b = 1`, so the kernel of this action of `ℤ/n` has order `gcd(n, b)`.
-/

public section

namespace ZMod

variable {n : ℕ} [NeZero n]

/-- The values of `ZMod.toCircle` are `n`-th roots of unity. -/
theorem toCircle_pow_eq_one (j : ZMod n) : toCircle j ^ n = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_self, zero_mul, AddChar.map_zero_eq_one]

/-- **The `n`-th roots of unity in the circle are the values of `ZMod.toCircle`.** -/
theorem exists_toCircle_eq_of_pow_eq_one {ζ : Circle} (hζ : ζ ^ n = 1) :
    ∃ j : ZMod n, toCircle j = ζ := by
  obtain ⟨j, hj⟩ := (bijective_rootsOfUnityAddChar (n := n)).2 ⟨toUnits ζ, by
    rw [mem_rootsOfUnity, ← map_pow, hζ, map_one]⟩
  exact ⟨j, by simpa using congrArg (fun u : rootsOfUnity n Circle ↦ ((u : Circleˣ) : Circle)) hj⟩

/-- Since `toCircle` is injective, `toCircle k ^ b = 1` exactly when `b • k = 0`. -/
theorem toCircle_pow_eq_one_iff {b : ℕ} {k : ZMod n} : toCircle k ^ b = 1 ↔ b • k = 0 := by
  rw [← AddChar.map_nsmul_eq_pow, ← (toCircle (N := n)).map_zero_eq_one, injective_toCircle.eq_iff]

/-- **The rotations by `b`-th powers of `n`-th roots of unity act freely.** For `n` coprime to `b`,
multiplication by `toCircle k ^ b` fixes a nonzero complex number `w` only for `k = 0`. -/
theorem toCircle_pow_mul_eq_self_iff {b : ℕ} (hnb : n.Coprime b) {w : ℂ} (hw : w ≠ 0)
    {k : ZMod n} : ((toCircle k ^ b : Circle) : ℂ) * w = w ↔ k = 0 := by
  rw [mul_eq_right₀ hw, Circle.coe_eq_one, toCircle_pow_eq_one_iff, nsmul_eq_mul,
    ((isUnit_iff_coprime b n).2 hnb.symm).mul_right_eq_zero]

/-- **The kernel of the rotations by `b`-th powers of `n`-th roots of unity has order
`gcd(n, b)`.** Exactly `gcd(n, b)` elements `k ∈ ℤ/n` have `toCircle k ^ b = 1`, that is, act
trivially on `ℂ` by multiplication by `toCircle k ^ b`. So this action of `ℤ/n` is effective
exactly when `n` and `b` are coprime. -/
theorem natCard_toCircle_pow_eq_one (b : ℕ) :
    Nat.card {k : ZMod n // toCircle k ^ b = 1} = n.gcd b := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun k ↦ ?_)).trans
    ((IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod n) b).trans (by rw [Nat.card_zmod]))
  rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, toCircle_pow_eq_one_iff]

end ZMod

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- A standard character value at a natural number is a power of its value at `1`. -/
theorem stdAddChar_natCast (i : ℕ) :
    stdAddChar (i : ZMod N) = stdAddChar (1 : ZMod N) ^ i := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one]

/-- The generator `ζ_N = stdAddChar 1` is a primitive `N`th root of unity. -/
theorem isPrimitiveRoot_stdAddChar_one : IsPrimitiveRoot (stdAddChar (1 : ZMod N)) N :=
  (isPrimitive_stdAddChar N).isPrimitiveRoot

/-- A multiplicative map of `ℂ` sending the generator `ζ_N = stdAddChar 1` to
`stdAddChar d = ζ_N^d` sends every value `stdAddChar j` to `stdAddChar (d * j)`. -/
theorem map_stdAddChar_of_map_stdAddChar_one {F : Type*} [FunLike F ℂ ℂ]
    [MonoidHomClass F ℂ ℂ] {σ : F} {d : ZMod N}
    (hσ : σ (stdAddChar (1 : ZMod N)) = stdAddChar d)
    (j : ZMod N) : σ (stdAddChar j) = stdAddChar (d * j) := by
  rw [← natCast_zmod_val j, stdAddChar_natCast, map_pow, hσ,
    ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_zmod_val, mul_comm]

end ZMod

/-- Every injective multiplicative map of `ℂ` sends `ζ_N` to a character value indexed by a unit. -/
theorem MonoidHom.exists_map_stdAddChar_one_eq {N : ℕ} [NeZero N] (σ : ℂ →* ℂ)
    (hσ : Function.Injective σ) :
    ∃ d : (ZMod N)ˣ, σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N) := by
  have hζ := ZMod.isPrimitiveRoot_stdAddChar_one (N := N)
  obtain ⟨i, -, hi, hpow⟩ := hζ.isPrimitiveRoot_iff.mp (hζ.map_of_injective hσ)
  refine ⟨ZMod.unitOfCoprime i hi, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.stdAddChar_natCast, ← hpow]
