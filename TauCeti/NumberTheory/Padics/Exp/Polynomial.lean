/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.IntegerGrid
public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Interpolation
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

## Main results

* `TauCeti.norm_sum_mul_exp_le_mul_norm_prod`: the interpolation bound on a finite set of
  `p`-adic integers.
* `TauCeti.norm_sum_mul_exp_le_mul_norm_factorial_pow`: its explicit form on the integers
  `0 ≤ j < N` not divisible by `q`.

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

end TauCeti
