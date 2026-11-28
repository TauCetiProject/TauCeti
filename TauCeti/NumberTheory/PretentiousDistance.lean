/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Prime.Basic
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.Real.Sqrt

/-!
# The pretentious distance

For functions `f, g : ℕ → ℂ` and a real cutoff `x`, the *pretentious distance* of Granville and
Soundararajan is

  `D(f, g; x) = √(∑_{p ≤ x} (1 - Re (f(p) conj(g(p)))) / p)`,

the sum being over the primes `p ≤ x`. It measures how far the values of `f` at the primes are
from those of `g`, and is the quantity that controls mean values of multiplicative functions in
Halász's theorem. It is used for functions with values in the closed unit disc at the primes,
where every summand is nonnegative.

`D` is a distance on prime data and not a metric: `D(f, f; x)` is positive when `|f(p)| < 1` at
some prime `p ≤ x`. What holds for all functions with values in the unit disc is the triangle
inequality for products, `D(f₁ f₂, g₁ g₂; x) ≤ D(f₁, g₁; x) + D(f₂, g₂; x)`, and the triangle
inequality `D(f, h; x) ≤ D(f, g; x) + D(g, h; x)`. The second is usually deduced from the first
when `|g(p)| = 1`; here it is proved for every `g` with values in the unit disc, from the
three-point inequality `Complex.sqrt_one_sub_re_mul_conj_le`. In all statements the unit-disc
hypotheses are only required at the primes up to the cutoff.

## Main definitions

* `TauCeti.pretentiousDist f g x`: the pretentious distance `D(f, g; x)`.

## Main results

* `TauCeti.sq_pretentiousDist`: the formula for `D(f, g; x)²`.
* `TauCeti.pretentiousDist_comm`, `TauCeti.pretentiousDist_congr`,
  `TauCeti.pretentiousDist_mono`, `TauCeti.pretentiousDist_self`: symmetry, dependence on the
  values at the primes up to `x` only, monotonicity in `x`, and `D(f, f; x) = 0` for `f` of modulus
  `1` at the primes.
* `TauCeti.pretentiousDist_mul_le`: the triangle inequality for products.
* `TauCeti.pretentiousDist_triangle`: the triangle inequality.

## References

* A. Granville, K. Soundararajan, *Pretentious multiplicative functions and an inequality for the
  zeta-function*, arXiv:math/0608407.
-/

public section

open Finset
open scoped ComplexConjugate

namespace TauCeti

/-- The *pretentious distance* `D(f, g; x) = √(∑_{p ≤ x} (1 - Re (f(p) conj(g(p)))) / p)` of
Granville and Soundararajan, the sum being over the primes `p ≤ x`. It only depends on the values
of `f` and `g` at the primes up to `x`, and is meant for `f` and `g` with values in the closed
unit disc there. -/
noncomputable def pretentiousDist (f g : ℕ → ℂ) (x : ℝ) : ℝ :=
  √(∑ p ∈ Iic ⌊x⌋₊ with p.Prime, (1 - (f p * conj (g p)).re) / p)

/-- The defining formula of `pretentiousDist`. -/
theorem pretentiousDist_def (f g : ℕ → ℂ) (x : ℝ) :
    pretentiousDist f g x =
      √(∑ p ∈ Iic ⌊x⌋₊ with p.Prime, (1 - (f p * conj (g p)).re) / p) :=
  (rfl)

variable {f g h f₁ f₂ g₁ g₂ : ℕ → ℂ} {x y : ℝ}

/-- The pretentious distance is nonnegative. -/
theorem pretentiousDist_nonneg (f g : ℕ → ℂ) (x : ℝ) : 0 ≤ pretentiousDist f g x := by
  rw [pretentiousDist_def]
  exact Real.sqrt_nonneg _

/-- The summands of the pretentious distance up to `x` are nonnegative when `f` and `g` take
values in the closed unit disc at the primes up to `x`. -/
private theorem summand_nonneg (hf : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f p‖ ≤ 1)
    (hg : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖g p‖ ≤ 1) {p : ℕ}
    (hp : p ∈ {p ∈ Iic ⌊x⌋₊ | p.Prime}) : 0 ≤ (1 - (f p * conj (g p)).re) / p := by
  obtain ⟨hpx, hp⟩ := mem_filter.1 hp
  exact div_nonneg (Complex.one_sub_re_mul_conj_nonneg (hf p hp (mem_Iic.1 hpx))
    (hg p hp (mem_Iic.1 hpx))) (Nat.cast_nonneg p)

/-- If `f` and `g` take values in the closed unit disc at the primes up to `x`, then
`D(f, g; x)² = ∑_{p ≤ x} (1 - Re (f(p) conj(g(p)))) / p`. -/
theorem sq_pretentiousDist (hf : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f p‖ ≤ 1)
    (hg : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖g p‖ ≤ 1) :
    pretentiousDist f g x ^ 2 =
      ∑ p ∈ Iic ⌊x⌋₊ with p.Prime, (1 - (f p * conj (g p)).re) / p := by
  rw [pretentiousDist_def]
  exact Real.sq_sqrt <| sum_nonneg fun p hp ↦ summand_nonneg hf hg hp

/-- The pretentious distance is symmetric. -/
theorem pretentiousDist_comm (f g : ℕ → ℂ) (x : ℝ) :
    pretentiousDist f g x = pretentiousDist g f x := by
  rw [pretentiousDist_def, pretentiousDist_def]
  refine congrArg _ (sum_congr rfl fun p _ ↦ ?_)
  rw [← Complex.conj_re (g p * conj (f p)), map_mul, Complex.conj_conj, mul_comm]

/-- The pretentious distance only depends on the values at the primes up to `x`. -/
theorem pretentiousDist_congr (hf : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → f₁ p = f₂ p)
    (hg : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → g₁ p = g₂ p) :
    pretentiousDist f₁ g₁ x = pretentiousDist f₂ g₂ x := by
  rw [pretentiousDist_def, pretentiousDist_def]
  refine congrArg _ (sum_congr rfl fun p hp ↦ ?_)
  obtain ⟨hpx, hp⟩ := mem_filter.1 hp
  rw [hf p hp (mem_Iic.1 hpx), hg p hp (mem_Iic.1 hpx)]

/-- There are no primes below `2`, so the pretentious distance vanishes for `x < 2`. -/
@[simp]
theorem pretentiousDist_of_lt_two (f g : ℕ → ℂ) (hx : x < 2) : pretentiousDist f g x = 0 := by
  have h : ({p ∈ Iic ⌊x⌋₊ | p.Prime} : Finset ℕ) = ∅ := by
    refine filter_eq_empty_iff.2 fun p hp hprime ↦ ?_
    have := (Nat.floor_lt' two_ne_zero).2 (by simpa using hx)
    exact absurd hprime.two_le (not_le.2 ((mem_Iic.1 hp).trans_lt this))
  rw [pretentiousDist_def, h, sum_empty, Real.sqrt_zero]

/-- For functions with values in the closed unit disc at the primes up to `y`, the pretentious
distance up to `x ≤ y` is at most the distance up to `y`. -/
theorem pretentiousDist_mono (hf : ∀ p : ℕ, p.Prime → p ≤ ⌊y⌋₊ → ‖f p‖ ≤ 1)
    (hg : ∀ p : ℕ, p.Prime → p ≤ ⌊y⌋₊ → ‖g p‖ ≤ 1) (hxy : x ≤ y) :
    pretentiousDist f g x ≤ pretentiousDist f g y := by
  rw [pretentiousDist_def, pretentiousDist_def]
  exact Real.sqrt_le_sqrt (sum_le_sum_of_subset_of_nonneg
    (filter_subset_filter _ (Iic_subset_Iic.2 (Nat.floor_le_floor hxy)))
    fun p hp _ ↦ summand_nonneg hf hg hp)

/-- A function of modulus `1` at the primes up to `x` is at distance `0` from itself. For values
inside the unit disc this fails: `D(0, 0; 2)² = 1 / 2`. -/
@[simp]
theorem pretentiousDist_self (hf : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f p‖ = 1) :
    pretentiousDist f f x = 0 := by
  rw [pretentiousDist_def, sum_eq_zero, Real.sqrt_zero]
  intro p hp
  obtain ⟨hpx, hp⟩ := mem_filter.1 hp
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hf p hp (mem_Iic.1 hpx)]
  simp

/-! ### Triangle inequalities -/

/-- **The triangle inequality for products**: if `f₁`, `f₂`, `g₁`, `g₂` take values in the closed
unit disc at the primes up to `x`, then
`D(f₁ f₂, g₁ g₂; x) ≤ D(f₁, g₁; x) + D(f₂, g₂; x)`. -/
theorem pretentiousDist_mul_le (hf₁ : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f₁ p‖ ≤ 1)
    (hf₂ : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f₂ p‖ ≤ 1)
    (hg₁ : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖g₁ p‖ ≤ 1)
    (hg₂ : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖g₂ p‖ ≤ 1) :
    pretentiousDist (f₁ * f₂) (g₁ * g₂) x ≤ pretentiousDist f₁ g₁ x + pretentiousDist f₂ g₂ x := by
  rw [pretentiousDist_def, pretentiousDist_def, pretentiousDist_def]
  refine Real.sqrt_sum_le_sqrt_sum_add_sqrt_sum (fun p hp ↦ summand_nonneg hf₁ hg₁ hp)
    (fun p hp ↦ summand_nonneg hf₂ hg₂ hp) fun p hp ↦ ?_
  obtain ⟨hpx, hp'⟩ := mem_filter.1 hp
  have hpx' := mem_Iic.1 hpx
  rw [Pi.mul_apply, Pi.mul_apply, map_mul, mul_mul_mul_comm]
  exact Real.sqrt_div_le_sqrt_div_add_sqrt_div (Complex.sqrt_one_sub_re_mul_le
    (Complex.norm_mul_conj_le_one (hf₁ p hp' hpx') (hg₁ p hp' hpx'))
    (Complex.norm_mul_conj_le_one (hf₂ p hp' hpx') (hg₂ p hp' hpx'))) (Nat.cast_nonneg p)

/-- **The triangle inequality** for the pretentious distance: if `f`, `g` and `h` take values in
the closed unit disc at the primes up to `x`, then `D(f, h; x) ≤ D(f, g; x) + D(g, h; x)`. -/
theorem pretentiousDist_triangle (hf : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f p‖ ≤ 1)
    (hg : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖g p‖ ≤ 1)
    (hh : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖h p‖ ≤ 1) :
    pretentiousDist f h x ≤ pretentiousDist f g x + pretentiousDist g h x := by
  rw [pretentiousDist_def, pretentiousDist_def, pretentiousDist_def]
  refine Real.sqrt_sum_le_sqrt_sum_add_sqrt_sum (fun p hp ↦ summand_nonneg hf hg hp)
    (fun p hp ↦ summand_nonneg hg hh hp) fun p hp ↦ ?_
  obtain ⟨hpx, hp'⟩ := mem_filter.1 hp
  have hpx' := mem_Iic.1 hpx
  exact Real.sqrt_div_le_sqrt_div_add_sqrt_div (Complex.sqrt_one_sub_re_mul_conj_le
    (hf p hp' hpx') (hg p hp' hpx') (hh p hp' hpx')) (Nat.cast_nonneg p)

/-! ### Examples -/

example : pretentiousDist 1 1 x = 0 := pretentiousDist_self (by simp)

example : pretentiousDist f g 1 = 0 := pretentiousDist_of_lt_two f g one_lt_two

example : pretentiousDist 1 (-1) x ^ 2 = 2 * ∑ p ∈ Iic ⌊x⌋₊ with p.Prime, (1 / p : ℝ) := by
  rw [sq_pretentiousDist (by simp) (by simp), mul_sum]
  refine sum_congr rfl fun p _ ↦ ?_
  simp
  ring

example : pretentiousDist 0 0 2 ^ 2 = 1 / 2 := by
  have h : ({p ∈ Iic 2 | p.Prime} : Finset ℕ) = {2} := by decide
  rw [sq_pretentiousDist (by simp) (by simp), Nat.floor_ofNat, h]
  simp

end TauCeti
