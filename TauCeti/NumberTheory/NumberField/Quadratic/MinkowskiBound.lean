/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.Quadratic.Model
import Mathlib.Tactic.NormNum.RealSqrt
import TauCeti.NumberTheory.EffectiveBounds.Discriminant.Basic
import TauCeti.NumberTheory.NumberField.ClassNumber.Minkowski
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta

/-!
# Minkowski's bound for the class number of a quadratic field

Let `K` be a quadratic field of discriminant `D`, with `r₂` complex places. By Minkowski's bound
(`NumberField.exists_ideal_in_class_of_norm_le`) every ideal class of `K` contains an integral
ideal of norm at most `M = (4 / π) ^ r₂ √|D| / 2`, so the class number `h` is at most the number
of integral ideals of norm at most `M` (`TauCeti.NumberField.classNumber_le_card_idealsLE`). In a
quadratic field there are at most `n` integral ideals of norm `n ≥ 1`, hence at most
`∑_{n ≤ B} n = B (B + 1) / 2` of norm at most `M`, where `B = ⌊M⌋`
(`TauCeti.NumberField.two_mul_card_idealsLE_le`). So `2 h ≤ B (B + 1)`, and `h ≤ B²` as `h ≥ 1`.
Since `M < √|D|`, this gives `h < |D|`.

Let `d > 0` be an integer that is not a square, and let `D` be the discriminant of `ℚ(√d)` (the
model `QuadraticAlgebra ℚ d 0`). Since `√d` is an irrational algebraic integer with `(√d)² = d`,
`|D| ≤ 4d` (`NumberField.abs_discr_le_int_of_sq_intCast`), and `ℚ(√d)` is real, so `r₂ = 0`.
Hence `h ≤ ⌊√D / 2⌋² ≤ D / 4 ≤ d`, with `⌊√D / 2⌋² ≠ d` because `d` is not a square. So
`h(ℚ(√d)) < d`, and `d ∤ h(ℚ(√d))`. In particular, for every prime `ℓ`, `h(ℚ(√ℓ)) < ℓ` and
`ℓ ∤ h(ℚ(√ℓ))`.

## Main results

* `TauCeti.NumberField.two_mul_classNumber_le`: `2 h ≤ B (B + 1)` with
  `B = ⌊(4 / π) ^ r₂ √|D| / 2⌋₊`, for a quadratic field.
* `TauCeti.NumberField.classNumber_lt_natAbs_discr`: `h < |D|` for a quadratic field.
* `TauCeti.QuadraticAlgebra.classNumber_lt_radicand_of_pos` and
  `TauCeti.QuadraticAlgebra.not_dvd_classNumber_of_pos`: `h(ℚ(√d)) < d` and `d ∤ h(ℚ(√d))` for
  every positive integer `d` that is not a square.
* `TauCeti.QuadraticAlgebra.classNumber_lt_radicand_of_prime` and
  `TauCeti.QuadraticAlgebra.not_dvd_classNumber_of_prime`: for a prime `ℓ`, `h(ℚ(√ℓ)) < ℓ` and
  `ℓ ∤ h(ℚ(√ℓ))`.

## References

* The statement `h(ℚ(√ℓ)) < ℓ`, hence `ℓ ∤ h(ℚ(√ℓ))`, for primes `ℓ ≡ 1 (mod 4)` is taken from
  the formal proof https://github.com/leanprover-community/riemann-hypothesis, where it is
  `UpperTheory.V.X.hQuad`, with the class number bound
  `GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred`.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §6.
-/

public section

open Module NumberField NumberField.InfinitePlace
open scoped Real nonZeroDivisors

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] (hK : finrank ℚ K = 2)
include hK

/-- **Minkowski's bound for the class number of a quadratic field.** If `K` is a quadratic field
of discriminant `D` with `r₂` complex places, then `2 h ≤ B (B + 1)` for
`B = ⌊(4 / π) ^ r₂ √|D| / 2⌋₊`, where `h` is the class number of `K`. -/
theorem two_mul_classNumber_le :
    2 * classNumber K ≤ ⌊(4 / π) ^ nrComplexPlaces K * √|(discr K : ℝ)| / 2⌋₊ *
      (⌊(4 / π) ^ nrComplexPlaces K * √|(discr K : ℝ)| / 2⌋₊ + 1) := by
  refine (Nat.mul_le_mul_left 2 (classNumber_le_card_idealsLE K (le_of_eq ?_))).trans
    (two_mul_card_idealsLE_le hK _)
  rw [hK]
  norm_num [Nat.factorial]
  ring

/-- `h ≤ B²` for `B = ⌊(4 / π) ^ r₂ √|D| / 2⌋₊`, since `2 h ≤ B (B + 1)` and `h ≥ 1`. -/
private theorem classNumber_le_sq_floor :
    classNumber K ≤ ⌊(4 / π) ^ nrComplexPlaces K * √|(discr K : ℝ)| / 2⌋₊ ^ 2 := by
  have h := two_mul_classNumber_le hK
  have := classNumber_pos K
  nlinarith

/-- **The class number of a quadratic field is less than the absolute value of its
discriminant.** If `K` is a quadratic field of discriminant `D`, then `h < |D|`, where `h` is the
class number of `K`. -/
theorem classNumber_lt_natAbs_discr : classNumber K < (discr K).natAbs := by
  set x : ℝ := (4 / π) ^ nrComplexPlaces K * √|(discr K : ℝ)| / 2 with hx
  have hD : (0 : ℝ) < |(discr K : ℝ)| := abs_cast_discr_pos K
  have hs := Real.sqrt_pos.mpr hD
  -- `(4 / π) ^ r₂ < 2`, as `r₂ ≤ 1`, so `x < √|D|`.
  have hc : (4 / π) ^ nrComplexPlaces K < 2 := by
    have := card_add_two_mul_card_eq_rank K
    obtain h0 | h1 : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1 := by omega
    · rw [h0]
      norm_num
    · rw [h1, pow_one, div_lt_iff₀ Real.pi_pos]
      linarith [Real.pi_gt_three]
  have hx0 : 0 ≤ x := by positivity
  have hxs : x < √|(discr K : ℝ)| := by
    rw [hx]
    nlinarith
  have hB : (⌊x⌋₊ : ℝ) ^ 2 < |(discr K : ℝ)| :=
    (Real.lt_sqrt (Nat.cast_nonneg _)).mp ((Nat.floor_le hx0).trans_lt hxs)
  have h := classNumber_le_sq_floor hK
  rw [← hx] at h
  have : ((⌊x⌋₊ ^ 2 : ℕ) : ℝ) < (discr K).natAbs := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact_mod_cast hB
  exact h.trans_lt (by exact_mod_cast this)

/-- **The class number of a real quadratic field is less than its discriminant.** If `K` is real
quadratic of discriminant `D`, then `h < D`, where `h` is the class number of `K`. -/
theorem classNumber_lt_discr [IsTotallyReal K] : (classNumber K : ℤ) < discr K := by
  have hD : 0 < discr K := (even_nrComplexPlaces_iff_zero_lt_discr K).mp (by simp)
  have := classNumber_lt_natAbs_discr hK
  omega

end TauCeti.NumberField

namespace TauCeti.QuadraticAlgebra

open _root_.QuadraticAlgebra

/-- **The class number of `ℚ(√d)` is less than `d`** for every positive integer `d` that is not a
square. Here `ℚ(√d)` is the model `QuadraticAlgebra ℚ d 0`, a field by the instance
`Fact (¬ IsSquare d)`. -/
theorem classNumber_lt_radicand_of_pos {d : ℤ} [hsq : Fact (¬ IsSquare d)] (hd : 0 < d) :
    (classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) : ℤ) < d := by
  have hK := finrank_eq_two (d : ℚ) 0
  -- `√d` is an irrational algebraic integer with `(√d)² = d`, so `ℚ(√d)` is real and `|D| ≤ 4 d`.
  have : IsTotallyReal (QuadraticAlgebra ℚ (d : ℚ) 0) :=
    isTotallyReal_of_minpoly_eq_X_sq_sub_C_of_nonneg minpoly_integralSqrt_omega
      adjoin_integralSqrt_omega hd.le
  have hDle := abs_discr_le_int_of_sq_intCast hK (coe_gen_sq minpoly_integralSqrt_omega)
    (gen_notMem_range minpoly_integralSqrt_omega)
  set D := NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0) with hDdef
  have hD : 0 < D := (even_nrComplexPlaces_iff_zero_lt_discr _).mp (by simp)
  rw [abs_of_pos hD, abs_of_pos hd] at hDle
  -- `h ≤ B²` with `B = ⌊√D / 2⌋₊`, and `B² ≤ D / 4 ≤ d`, `B² ≠ d`.
  have hh := TauCeti.NumberField.classNumber_le_sq_floor hK
  rw [IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, one_mul, ← hDdef,
    abs_of_pos (by exact_mod_cast hD)] at hh
  set B := ⌊√(D : ℝ) / 2⌋₊
  have h4 : √(4 : ℝ) = 2 := by norm_num
  have hBr : (B : ℝ) ^ 2 ≤ D / 4 := by
    refine (Real.le_sqrt (Nat.cast_nonneg _) (by positivity)).mp ?_
    rw [Real.sqrt_div' _ (by norm_num), h4]
    exact Nat.floor_le (by positivity)
  have hBd : ((B ^ 2 : ℕ) : ℤ) ≤ d := by
    have : ((B ^ 2 : ℕ) : ℝ) ≤ (d : ℝ) := by
      have := (by exact_mod_cast hDle : (D : ℝ) ≤ 4 * d)
      push_cast
      linarith
    exact_mod_cast this
  have hne : ((B ^ 2 : ℕ) : ℤ) ≠ d := fun h ↦ hsq.out ⟨B, by rw [← h]; push_cast; ring⟩
  have : (classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) : ℤ) ≤ ((B ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast hh
  omega

/-- **A positive integer `d` that is not a square does not divide the class number of `ℚ(√d)`.**
Here `ℚ(√d)` is the model `QuadraticAlgebra ℚ d 0`. -/
theorem not_dvd_classNumber_of_pos {d : ℤ} [Fact (¬ IsSquare d)] (hd : 0 < d) :
    ¬ d ∣ (classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) : ℤ) := fun h ↦
  (Int.le_of_dvd (by exact_mod_cast classNumber_pos _) h).not_gt
    (classNumber_lt_radicand_of_pos hd)

/-- **The class number of `ℚ(√ℓ)` for a prime `ℓ` is less than `ℓ`.** Here `ℚ(√ℓ)` is the model
`QuadraticAlgebra ℚ ℓ 0`, a field because a prime is not a square. -/
theorem classNumber_lt_radicand_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) :
    haveI : Fact (¬ IsSquare (ℓ : ℤ)) := ⟨(Nat.prime_iff_prime_int.mp hℓ).not_isSquare⟩
    classNumber (QuadraticAlgebra ℚ ((ℓ : ℤ) : ℚ) 0) < ℓ := by
  have : Fact (¬ IsSquare (ℓ : ℤ)) := ⟨(Nat.prime_iff_prime_int.mp hℓ).not_isSquare⟩
  exact_mod_cast classNumber_lt_radicand_of_pos (d := ℓ) (by exact_mod_cast hℓ.pos)

/-- **A prime `ℓ` does not divide the class number of `ℚ(√ℓ)`.** Here `ℚ(√ℓ)` is the model
`QuadraticAlgebra ℚ ℓ 0`. -/
theorem not_dvd_classNumber_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) :
    haveI : Fact (¬ IsSquare (ℓ : ℤ)) := ⟨(Nat.prime_iff_prime_int.mp hℓ).not_isSquare⟩
    ¬ ℓ ∣ classNumber (QuadraticAlgebra ℚ ((ℓ : ℤ) : ℚ) 0) := by
  have : Fact (¬ IsSquare (ℓ : ℤ)) := ⟨(Nat.prime_iff_prime_int.mp hℓ).not_isSquare⟩
  exact fun h ↦ not_dvd_classNumber_of_pos (d := ℓ) (by exact_mod_cast hℓ.pos)
    (by exact_mod_cast h)

end TauCeti.QuadraticAlgebra
