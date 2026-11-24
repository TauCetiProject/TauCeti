/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import TauCeti.NumberTheory.Padics.IntegerGrid
public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Interpolation
import TauCeti.NumberTheory.Padics.Exp.Disc
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Interpolation of p-adic exponential polynomials on integer grids

The auxiliary function of the p-adic method of linear forms in logarithms is an exponential
polynomial

```text
Φ(z) = ∑ᵢ aᵢ exp(z xᵢ),
```

where, for units `α₁, …, αₙ` close enough to `1` that `exp (log αⱼ) = αⱼ` and integers `λᵢⱼ`,
the frequencies are `xᵢ = ∑ⱼ λᵢⱼ log αⱼ` and `exp(b xᵢ) = ∏ⱼ αⱼ ^ (λᵢⱼ b)` at integers `b`. Over a
complete normed field `K ⊇ ℚ_p`, if every `‖xᵢ‖ c` lies below the radius `p ^ (-1 / (p - 1))` of
the exponential disc for some `c ≥ 1`, then `Φ` is the value of the exponential polynomial
`∑ᵢ aᵢ exp(xᵢX)`, which is restricted at `c` with Gauss norm at most `max ‖aᵢ‖`. Its divided
derivatives are `Φ⁽ᵏ⁾(z) / k! = ∑ᵢ aᵢ (xᵢ ^ k / k!) exp(z xᵢ)`.

Suppose `Φ` vanishes to order `T` on a finite set of `p`-adic integers, that is,
`∑ᵢ aᵢ xᵢ ^ t exp(b xᵢ) = 0` for `t < T` at each grid point `b`. The Schwarz lemma on grids of
`p`-adic integers then bounds every divided derivative at every `p`-adic integer `z`:

```text
‖Φ⁽ᵏ⁾(z) / k!‖ ≤ c⁻ᵏ * max ‖aᵢ‖ * (‖∏_{b} (z - b)‖ / c ^ #grid) ^ (T - k).
```

Here `T - k` is natural-number subtraction, truncated at zero.

On Yu's grid of the integers `0 ≤ j < N` not divisible by an auxiliary positive integer `q`
prime to `p`, the norm `‖∏_{b} (z - b)‖` of the grid product in the numerator is at most
`‖⌊N / q⌋!‖ ^ (q - 1)`; the radius power `c ^ #grid` remains the denominator. These are the
analytic upper bounds that the extrapolation steps of the method compare with Liouville-type lower
bounds for nonzero algebraic values.

For units `αⱼ` with `‖αⱼ - 1‖ c < p ^ (-1 / (p - 1))` and `c ≥ 1`, every frequency
`x_l = ∑ⱼ lⱼ log αⱼ` with integer exponents `lⱼ` satisfies the radius condition, and
`exp(b x_l) = ∏ⱼ αⱼ ^ (lⱼ b)` at integers `b`. The interpolation bounds therefore apply to the
sums of products of integer powers

```text
Φ(z) = ∑_l a_l ∏ⱼ αⱼ ^ (lⱼ z),    Φ⁽ᵏ⁾(z) / k! = ∑_l a_l (x_l ^ k / k!) ∏ⱼ αⱼ ^ (lⱼ z)
```

at integers `z`, with vanishing hypotheses and conclusions stated through the units alone.

## Main results

* `TauCeti.norm_sum_mul_exp_le_mul_norm_prod`: the interpolation bound on a finite set of
  `p`-adic integers.
* `TauCeti.norm_sum_mul_exp_le_mul_norm_factorial_pow`: its explicit form on the integers
  `0 ≤ j < N` not divisible by `q`.
* `TauCeti.norm_sum_mul_prod_zpow_le_mul_norm_prod`,
  `TauCeti.norm_sum_mul_prod_zpow_le_mul_norm_factorial_pow`: the same bounds for sums of
  products of integer powers of units close to `1`, on a finite set of integers and on the
  integers `0 ≤ j < N` not divisible by `q`.

The evaluation of the Hasse derivatives of `∑ᵢ aᵢ exp(xᵢX)` is
`TauCeti.evalAt_hasseDeriv_sum_smul_rescale_exp`, and the bound on a general closed disc, with
arbitrary grid points and multiplicities, is `TauCeti.norm_sum_mul_exp_le_mul_prod_pow`.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
-/

public section

open Finset
open scoped Nat

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
  [NormedAlgebra ℚ_[p] K] [CompleteSpace K] {ι : Type*} {s : Finset ι} {a x : ι → K} {c : ℝ}

open PowerSeries

namespace TauCeti

/-- **Interpolation of a p-adic exponential polynomial on a grid of `p`-adic integers.** Let `K`
be a complete normed field extension of `ℚ_p`, `c ≥ 1` a radius with `‖xᵢ‖ c < p ^ (-1 / (p - 1))`
for every frequency `xᵢ`, and `A ≥ 0` a bound for the coefficients `‖aᵢ‖`. If
`Φ(z) = ∑ᵢ aᵢ exp(z xᵢ)` vanishes to order `T` at every point `b` of a finite set `g` of `p`-adic
integers, `∑ᵢ aᵢ xᵢ ^ t exp(b xᵢ) = 0` for `t < T`, then for every `k` and every `p`-adic integer
`z` the divided derivative `Φ⁽ᵏ⁾(z) / k!` satisfies

```text
‖∑ᵢ aᵢ (xᵢ ^ k / k!) exp(z xᵢ)‖ ≤ c⁻ᵏ * A * (‖∏_{b ∈ g} (z - b)‖ / c ^ #g) ^ (T - k).
```

Here `T - k` is natural-number subtraction, truncated at zero. -/
theorem norm_sum_mul_exp_le_mul_norm_prod (hc : 1 ≤ c)
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ A) {g : Finset ℤ_[p]} {T : ℕ}
    (hzero : ∀ b ∈ g, ∀ t < T,
      ∑ i ∈ s, a i * x i ^ t * NormedSpace.exp (algebraMap ℚ_[p] K b * x i) = 0)
    (k : ℕ) (z : ℤ_[p]) :
    ‖∑ i ∈ s, a i * (x i ^ k / k !) * NormedSpace.exp (algebraMap ℚ_[p] K z * x i)‖ ≤
      c⁻¹ ^ k * A * (‖∏ b ∈ g, (z - b)‖ / c ^ g.card) ^ (T - k) := by
  classical
  have hinj : Function.Injective fun b : ℤ_[p] ↦ algebraMap ℚ_[p] K b := fun y z h ↦
    Subtype.ext ((algebraMap ℚ_[p] K).injective h)
  have hdist (b : ℤ_[p]) :
      ‖algebraMap ℚ_[p] K z - algebraMap ℚ_[p] K b‖ = ‖z - b‖ := by
    rw [← map_sub, ← PadicInt.coe_sub, norm_algebraMap', ← PadicInt.norm_def]
  have h := norm_sum_mul_exp_le_mul_prod_pow (zero_lt_one.trans_le hc) hxc hA ha
    (g := g.image fun b : ℤ_[p] ↦ algebraMap ℚ_[p] K b) (T := fun _ ↦ T)
    (forall_mem_image.mpr fun b _ ↦ (PadicInt.norm_algebraMap_le_one b).trans hc)
    (by simpa using hzero) k ((PadicInt.norm_algebraMap_le_one z).trans hc)
  refine h.trans_eq ?_
  rw [prod_image hinj.injOn]
  simp only [hdist]
  rw [prod_pow, prod_div_distrib, prod_const, ← norm_prod]

/-- **Interpolation of a p-adic exponential polynomial on the integers not divisible by `q`.**
Let `K` be a complete normed field extension of `ℚ_p`, `c ≥ 1` a radius with
`‖xᵢ‖ c < p ^ (-1 / (p - 1))` for every frequency `xᵢ`, `A ≥ 0` a bound for the coefficients
`‖aᵢ‖`, and `q` a positive integer prime to `p`. If `Φ(z) = ∑ᵢ aᵢ exp(z xᵢ)` vanishes to order
`T` at every
integer `0 ≤ j < N` not divisible by `q`, a grid of `S` points, then for every `k` and every
`p`-adic integer `z`

```text
‖∑ᵢ aᵢ (xᵢ ^ k / k!) exp(z xᵢ)‖ ≤ c⁻ᵏ * A * (‖⌊N / q⌋!‖ ^ (q - 1) / c ^ S) ^ (T - k).
```

Here `T - k` is natural-number subtraction, truncated at zero. -/
theorem norm_sum_mul_exp_le_mul_norm_factorial_pow (hc : 1 ≤ c)
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ A) {q : ℕ} (hq : p.Coprime q) {N T : ℕ}
    (hzero : ∀ j < N, ¬q ∣ j → ∀ t < T,
      ∑ i ∈ s, a i * x i ^ t * NormedSpace.exp ((j : K) * x i) = 0)
    (k : ℕ) (z : ℤ_[p]) :
    ‖∑ i ∈ s, a i * (x i ^ k / k !) * NormedSpace.exp (algebraMap ℚ_[p] K z * x i)‖ ≤
      c⁻¹ ^ k * A *
        (‖((N / q)! : ℤ_[p])‖ ^ (q - 1) / c ^ ((range N).filter (¬q ∣ ·)).card) ^ (T - k) := by
  classical
  have hinj : Set.InjOn (Nat.cast : ℕ → ℤ_[p]) ((range N).filter (¬q ∣ ·) : Set ℕ) :=
    Nat.cast_injective.injOn
  have h := norm_sum_mul_exp_le_mul_norm_prod hc hxc hA ha
    (g := ((range N).filter (¬q ∣ ·)).image (Nat.cast : ℕ → ℤ_[p])) (T := T)
    (fun b hb ↦ by
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
      rw [mem_filter, mem_range] at hj
      simpa using hzero j hj.1 hj.2) k z
  rw [prod_image hinj, card_image_of_injOn hinj] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  gcongr
  exact PadicInt.norm_prod_filter_not_dvd_sub_le z hq N


section UnitPowers

variable {κ : Type*} {t : Finset κ} {α : κ → K}

omit [Fact p.Prime] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- A unit with `‖y - 1‖ c < p ^ (-1 / (p - 1))` for a radius `c ≥ 1` lies in the disc about `1`
on which the exponential inverts the logarithm, `exp (log y) = y`. -/
private theorem norm_sub_one_lt_amiceRadius_zero (hc : 1 ≤ c) {y : K}
    (hy : ‖y - 1‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) : ‖y - 1‖ < amiceRadius p 0 := by
  rw [amiceRadius_def]
  simpa using (le_mul_of_one_le_right (norm_nonneg _) hc).trans_lt hy

/-- The frequency `∑ⱼ lⱼ log αⱼ` of units with `‖αⱼ - 1‖ c < p ^ (-1 / (p - 1))` and `c ≥ 1`
satisfies the same radius condition. -/
private theorem norm_sum_intCast_mul_log_mul_lt (hc : 1 ≤ c)
    (hα : ∀ j ∈ t, ‖α j - 1‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) (l : κ → ℤ) :
    ‖∑ j ∈ t, (l j : K) * NormedSpace.log (α j)‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hP : 0 < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _
  rw [← lt_div_iff₀ hc0]
  refine norm_sum_intCast_mul_log_lt (p := p) (div_pos hP hc0) ?_
    (fun j hj ↦ (lt_div_iff₀ hc0).mpr (hα j hj)) l
  rw [amiceRadius_def]
  simpa using div_le_self hP.le hc

/-- At an integer `b`, the exponential of `b` times the frequency `∑ⱼ lⱼ log αⱼ` is the
product of integer powers `∏ⱼ αⱼ ^ (lⱼ b)`. -/
private theorem exp_intCast_mul_sum_intCast_mul_log
    (hα : ∀ j ∈ t, ‖α j - 1‖ < amiceRadius p 0) (l : κ → ℤ) (b : ℤ) :
    NormedSpace.exp ((b : K) * ∑ j ∈ t, (l j : K) * NormedSpace.log (α j)) =
      ∏ j ∈ t, α j ^ (l j * b) := by
  rw [← t.exp_sum_intCast_mul_log hα, mul_sum]
  refine congrArg _ (sum_congr rfl fun j _ ↦ ?_)
  push_cast
  ring

/-- **Interpolation of sums of products of unit powers on a finite set of integers.** Let `K` be
a complete normed field extension of `ℚ_p`, `c ≥ 1` a radius and `αⱼ` (`j ∈ t`) units with
`‖αⱼ - 1‖ c < p ^ (-1 / (p - 1))`. For a finite set `Λ` of integer exponent vectors, `A ≥ 0`
and coefficients with `‖a_l‖ ≤ A`, put `x_l = ∑ⱼ lⱼ log αⱼ`. If

```text
∑_l a_l x_l ^ τ ∏ⱼ αⱼ ^ (lⱼ b) = 0
```

for every `τ < T` and every `b` in a finite set `g` of integers, then for every `k` and every
integer `z`

```text
‖∑_l a_l (x_l ^ k / k!) ∏ⱼ αⱼ ^ (lⱼ z)‖ ≤ c⁻ᵏ * A * (‖∏_{b ∈ g} (z - b)‖ / c ^ #g) ^ (T - k),
```

where `‖∏_{b ∈ g} (z - b)‖` is the `p`-adic norm of the integer product and `T - k` is
natural-number subtraction, truncated at zero. -/
theorem norm_sum_mul_prod_zpow_le_mul_norm_prod (hc : 1 ≤ c)
    (hα : ∀ j ∈ t, ‖α j - 1‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {Λ : Finset (κ → ℤ)}
    {a : (κ → ℤ) → K} {A : ℝ} (hA : 0 ≤ A) (ha : ∀ l ∈ Λ, ‖a l‖ ≤ A) {g : Finset ℤ} {T : ℕ}
    (hzero : ∀ b ∈ g, ∀ τ < T, ∑ l ∈ Λ,
      a l * (∑ j ∈ t, (l j : K) * NormedSpace.log (α j)) ^ τ * ∏ j ∈ t, α j ^ (l j * b) = 0)
    (k : ℕ) (z : ℤ) :
    ‖∑ l ∈ Λ, a l * ((∑ j ∈ t, (l j : K) * NormedSpace.log (α j)) ^ k / k !) *
        ∏ j ∈ t, α j ^ (l j * z)‖ ≤
      c⁻¹ ^ k * A * (‖((∏ b ∈ g, (z - b) : ℤ) : ℤ_[p])‖ / c ^ g.card) ^ (T - k) := by
  classical
  have hα₀ (j : κ) (hj : j ∈ t) := norm_sub_one_lt_amiceRadius_zero hc (hα j hj)
  have hinj : Function.Injective (Int.cast : ℤ → ℤ_[p]) := Int.cast_injective
  have h := norm_sum_mul_exp_le_mul_norm_prod hc
    (fun l _ ↦ norm_sum_intCast_mul_log_mul_lt hc hα l) hA ha
    (g := g.image (Int.cast : ℤ → ℤ_[p])) (T := T)
    (forall_mem_image.mpr fun b hb τ hτ ↦ by
      simpa only [PadicInt.coe_intCast, map_intCast, exp_intCast_mul_sum_intCast_mul_log hα₀]
        using hzero b hb τ hτ)
    k z
  simp only [PadicInt.coe_intCast, map_intCast, exp_intCast_mul_sum_intCast_mul_log hα₀] at h
  rw [prod_image hinj.injOn, card_image_of_injective _ hinj] at h
  push_cast
  exact h

/-- **Interpolation of sums of products of unit powers on the integers not divisible by `q`.**
Let `K` be a complete normed field extension of `ℚ_p`, `c ≥ 1` a radius and `αⱼ` (`j ∈ t`)
units with `‖αⱼ - 1‖ c < p ^ (-1 / (p - 1))`. For a finite set `Λ` of integer exponent vectors,
`A ≥ 0` and coefficients with `‖a_l‖ ≤ A`, put `x_l = ∑ⱼ lⱼ log αⱼ`, and let `q` be a positive
integer prime to `p`. If `∑_l a_l x_l ^ τ ∏ⱼ αⱼ ^ (lⱼ b) = 0` for every `τ < T` and every integer
`0 ≤ b < N` not divisible by `q`, a grid of `S` points, then for every `k` and every integer `z`

```text
‖∑_l a_l (x_l ^ k / k!) ∏ⱼ αⱼ ^ (lⱼ z)‖ ≤ c⁻ᵏ * A * (‖⌊N / q⌋!‖ ^ (q - 1) / c ^ S) ^ (T - k).
```

Here `T - k` is natural-number subtraction, truncated at zero. -/
theorem norm_sum_mul_prod_zpow_le_mul_norm_factorial_pow (hc : 1 ≤ c)
    (hα : ∀ j ∈ t, ‖α j - 1‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {Λ : Finset (κ → ℤ)}
    {a : (κ → ℤ) → K} {A : ℝ} (hA : 0 ≤ A) (ha : ∀ l ∈ Λ, ‖a l‖ ≤ A) {q : ℕ}
    (hq : p.Coprime q) {N T : ℕ}
    (hzero : ∀ b < N, ¬q ∣ b → ∀ τ < T, ∑ l ∈ Λ,
      a l * (∑ j ∈ t, (l j : K) * NormedSpace.log (α j)) ^ τ * ∏ j ∈ t, α j ^ (l j * b) = 0)
    (k : ℕ) (z : ℤ) :
    ‖∑ l ∈ Λ, a l * ((∑ j ∈ t, (l j : K) * NormedSpace.log (α j)) ^ k / k !) *
        ∏ j ∈ t, α j ^ (l j * z)‖ ≤
      c⁻¹ ^ k * A *
        (‖((N / q)! : ℤ_[p])‖ ^ (q - 1) / c ^ ((range N).filter (¬q ∣ ·)).card) ^ (T - k) := by
  have hα₀ (j : κ) (hj : j ∈ t) := norm_sub_one_lt_amiceRadius_zero hc (hα j hj)
  have h := norm_sum_mul_exp_le_mul_norm_factorial_pow hc
    (fun l _ ↦ norm_sum_intCast_mul_log_mul_lt hc hα l) hA ha hq (N := N) (T := T)
    (fun b hb hqb τ hτ ↦ by
      simpa only [← Int.cast_natCast (R := K) b, exp_intCast_mul_sum_intCast_mul_log hα₀]
        using hzero b hb hqb τ hτ)
    k z
  simpa only [PadicInt.coe_intCast, map_intCast, exp_intCast_mul_sum_intCast_mul_log hα₀]
    using h

end UnitPowers

end TauCeti
