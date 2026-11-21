/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.IntegerGrid
public import TauCeti.RingTheory.PowerSeries.Exp.Padic
import Mathlib.Analysis.Normed.Algebra.Ultra
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.PowerSeries.HasseDeriv.GaussNorm

/-!
# Interpolation of p-adic exponential polynomials on integer grids

The auxiliary function of the p-adic method of linear forms in logarithms is an exponential
polynomial

```text
Φ(z) = ∑ᵢ aᵢ exp(z xᵢ),
```

where, for units `α₁, …, αₙ` close enough to `1` that `exp (log αⱼ) = αⱼ`, the frequencies are
`xᵢ = ∑ⱼ λⱼ log αⱼ` and `exp(b xᵢ) = ∏ⱼ αⱼ ^ (λⱼ b)` at integers `b`. Over a
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

On Yu's grid of the integers `0 ≤ j < N` not divisible by an auxiliary integer `q` prime to `p`,
the interpolation denominator is at most `‖⌊N / q⌋!‖ ^ (q - 1)`. These are the analytic upper
bounds that the extrapolation steps of the method compare with Liouville-type lower bounds for
nonzero algebraic values.

## Main results

* `PowerSeries.evalAt_hasseDeriv_sum_smul_rescale_exp`: the Hasse derivatives of an exponential
  polynomial, evaluated in the closed disc, are the divided derivatives of `Φ`.
* `TauCeti.norm_sum_mul_exp_le_mul_norm_prod`: the interpolation bound on a finite set of
  `p`-adic integers.
* `TauCeti.norm_sum_mul_exp_le_mul_norm_factorial_pow`: its explicit form on the integers
  `0 ≤ j < N` not divisible by `q`.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
-/

public section

open Finset
open scoped Nat

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K] [Algebra ℚ K]
  [NormedAlgebra ℚ_[p] K] [CompleteSpace K] {ι : Type*} {s : Finset ι} {a x : ι → K} {c : ℝ}

namespace PowerSeries

/-- At a point `y` of the closed disc of radius `c`, the `k`th Hasse derivative of the
exponential polynomial `∑ᵢ aᵢ exp(xᵢX)`, restricted at `c`, takes the value
`∑ᵢ aᵢ (xᵢ ^ k / k!) exp(y xᵢ)`. -/
theorem evalAt_hasseDeriv_sum_smul_rescale_exp (hc : 0 ≤ c)
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) (k : ℕ) {y : K} (hy : ‖y‖ ≤ c) :
    (hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp K))).evalAt y =
      ∑ i ∈ s, a i * (x i ^ k / k !) * NormedSpace.exp (y * x i) := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  have hD : hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp K)) =
      ∑ i ∈ s, (a i * (x i ^ k / k !)) • rescale (x i) (exp K) := by
    simp only [map_sum, map_smul, hasseDeriv_rescale_exp, smul_smul, map_inv₀, map_natCast,
      div_eq_mul_inv, mul_comm (x _ ^ k)]
  rw [hD, IsRestricted.evalAt_sum _ (fun i hi ↦ (isRestricted_rescale_exp hc (hxc i hi)).smul _) hy]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [IsRestricted.evalAt_smul (isRestricted_rescale_exp hc (hxc i hi)) _ hy, evalAt_rescale,
    evalAt_exp, smul_eq_mul, smul_eq_mul, mul_comm (x i) y]

end PowerSeries

open PowerSeries

namespace TauCeti

/-- If `Φ(z) = ∑ᵢ aᵢ exp(z xᵢ)` has vanishing derivatives `Φ⁽ᵗ⁾(y) = ∑ᵢ aᵢ xᵢ ^ t exp(y xᵢ)` for
`t < T` at a point `y` of the closed disc of radius `c`, then so do the Hasse derivatives of the
exponential polynomial `∑ᵢ aᵢ exp(xᵢX)` at `y`. -/
private theorem evalAt_hasseDeriv_sum_smul_rescale_exp_eq_zero (hc : 0 ≤ c)
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {y : K} (hy : ‖y‖ ≤ c) {T : ℕ}
    (hzero : ∀ t < T, ∑ i ∈ s, a i * x i ^ t * NormedSpace.exp (y * x i) = 0) {t : ℕ}
    (ht : t < T) :
    (hasseDeriv t (∑ i ∈ s, a i • rescale (x i) (exp K))).evalAt y = 0 := by
  rw [evalAt_hasseDeriv_sum_smul_rescale_exp hc hxc t hy]
  -- the divided derivative is the derivative divided by the nonzero integer `t!`
  have h : ∑ i ∈ s, a i * (x i ^ t / t !) * NormedSpace.exp (y * x i) =
      (t ! : K)⁻¹ * ∑ i ∈ s, a i * x i ^ t * NormedSpace.exp (y * x i) := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [h, hzero t ht, mul_zero]

/-- **Interpolation of a p-adic exponential polynomial on a grid of `p`-adic integers.** Let `K`
be a complete normed field extension of `ℚ_p`, `c ≥ 1` a radius with `‖xᵢ‖ c < p ^ (-1 / (p - 1))`
for every frequency `xᵢ`, and `A ≥ 0` a bound for the coefficients `‖aᵢ‖`. If
`Φ(z) = ∑ᵢ aᵢ exp(z xᵢ)` vanishes to order `T` at every point `b` of a finite set `g` of `p`-adic
integers, `∑ᵢ aᵢ xᵢ ^ t exp(b xᵢ) = 0` for `t < T`, then for every `k` and every `p`-adic integer
`z` the divided derivative `Φ⁽ᵏ⁾(z) / k!` satisfies

```text
‖∑ᵢ aᵢ (xᵢ ^ k / k!) exp(z xᵢ)‖ ≤ c⁻ᵏ * A * (‖∏_{b ∈ g} (z - b)‖ / c ^ #g) ^ (T - k).
``` -/
theorem norm_sum_mul_exp_le_mul_norm_prod (hc : 1 ≤ c)
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ A) {g : Finset ℤ_[p]} {T : ℕ}
    (hzero : ∀ b ∈ g, ∀ t < T,
      ∑ i ∈ s, a i * x i ^ t * NormedSpace.exp (algebraMap ℚ_[p] K b * x i) = 0)
    (k : ℕ) (z : ℤ_[p]) :
    ‖∑ i ∈ s, a i * (x i ^ k / k !) * NormedSpace.exp (algebraMap ℚ_[p] K z * x i)‖ ≤
      c⁻¹ ^ k * A * (‖∏ b ∈ g, (z - b)‖ / c ^ g.card) ^ (T - k) := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hb (b : ℤ_[p]) : ‖algebraMap ℚ_[p] K b‖ ≤ c := (PadicInt.norm_algebraMap_le_one b).trans hc
  have hF := isRestricted_sum_smul_rescale_exp s a x hc0 hxc
  have h := hF.norm_evalAt_hasseDeriv_le_gaussNorm_mul_norm_prod hc (s := g) (T := T)
    (fun b hb' _ ht ↦
      evalAt_hasseDeriv_sum_smul_rescale_exp_eq_zero hc0 hxc (hb b) (hzero b hb') ht) k z
  rw [evalAt_hasseDeriv_sum_smul_rescale_exp hc0 hxc k (hb z)] at h
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
    (by positivity))
  exact gaussNorm_sum_smul_rescale_exp_le s a x hc0 (fun i hi ↦ (hxc i hi).le) hA ha

/-- **Interpolation of a p-adic exponential polynomial on the integers not divisible by `q`.**
Let `K` be a complete normed field extension of `ℚ_p`, `c ≥ 1` a radius with
`‖xᵢ‖ c < p ^ (-1 / (p - 1))` for every frequency `xᵢ`, `A ≥ 0` a bound for the coefficients
`‖aᵢ‖`, and `q` an integer prime to `p`. If `Φ(z) = ∑ᵢ aᵢ exp(z xᵢ)` vanishes to order `T` at every
integer `0 ≤ j < N` not divisible by `q`, a grid of `S` points, then for every `k` and every
`p`-adic integer `z`

```text
‖∑ᵢ aᵢ (xᵢ ^ k / k!) exp(z xᵢ)‖ ≤ c⁻ᵏ * A * (‖⌊N / q⌋!‖ ^ (q - 1) / c ^ S) ^ (T - k).
``` -/
theorem norm_sum_mul_exp_le_mul_norm_factorial_pow (hc : 1 ≤ c)
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ A) {q : ℕ} (hq : p.Coprime q) {N T : ℕ}
    (hzero : ∀ j < N, ¬q ∣ j → ∀ t < T,
      ∑ i ∈ s, a i * x i ^ t * NormedSpace.exp ((j : K) * x i) = 0)
    (k : ℕ) (z : ℤ_[p]) :
    ‖∑ i ∈ s, a i * (x i ^ k / k !) * NormedSpace.exp (algebraMap ℚ_[p] K z * x i)‖ ≤
      c⁻¹ ^ k * A *
        (‖((N / q)! : ℤ_[p])‖ ^ (q - 1) / c ^ ((range N).filter (¬q ∣ ·)).card) ^ (T - k) := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hF := isRestricted_sum_smul_rescale_exp s a x hc0 hxc
  have h := hF.norm_evalAt_hasseDeriv_le_gaussNorm_mul_norm_factorial_pow hc hq (N := N) (T := T)
    (fun j _ hqj _ ht ↦ evalAt_hasseDeriv_sum_smul_rescale_exp_eq_zero hc0 hxc
      ((IsUltrametricDist.norm_natCast_le_one K j).trans hc) (hzero j ‹_› hqj) ht)
    k z
  rw [evalAt_hasseDeriv_sum_smul_rescale_exp hc0 hxc k
    ((PadicInt.norm_algebraMap_le_one z).trans hc)] at h
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
    (by positivity))
  exact gaussNorm_sum_smul_rescale_exp_le s a x hc0 (fun i hi ↦ (hxc i hi).le) hA ha

end TauCeti
