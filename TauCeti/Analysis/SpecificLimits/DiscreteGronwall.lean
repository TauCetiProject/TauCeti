/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
import TauCeti.Algebra.Order.Floor.Semifield

/-!
# Discrete Grönwall estimates for implicit time stepping

A discrete Grönwall argument shows that a quantity growing at most by the factor `1 + aτ` per
time step of length `τ` grows at most like `exp (a t)` up to time `t`. This file records the
growth factor estimate `(1 + aτ) ^ ⌈t / τ⌉₊ ≤ exp (a (t + τ))`, valid uniformly in the time
step (`TauCeti.one_add_mul_pow_ceil_div_le_exp`), its sharp form as the time step tends to `0`,
`(1 + aτ) ^ L → exp (a T)` and `τ ∑_{n < L} (1 + aτ) ^ n → ∫₀ᵀ exp (a r) dr` whenever `L τ → T`
(`TauCeti.tendsto_one_add_mul_pow` and `TauCeti.tendsto_mul_sum_one_add_mul_pow`), the
ceiling-step limits `⌈r / τ j⌉₊ * τ j → r` (`TauCeti.tendsto_ceil_div_mul`),
`⌈s / τ j⌉₊ < ⌈t / τ j⌉₊` eventually (`TauCeti.eventually_ceil_div_lt_ceil_div`), and
`(⌈t / τ j⌉₊ - ⌈s / τ j⌉₊) * τ j → t - s` (`TauCeti.tendsto_ceil_div_sub_ceil_div_mul`), and a
discrete Grönwall bound for sequences that move in steps paid for by an energy which is bounded
below in terms of the distance travelled (`TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub`).

Conversely, a nonincreasing quantity which drops at least by a factor `q < 1` over every time
interval of length `T` decays exponentially, at the rate `-log q / T`
(`TauCeti.le_div_mul_exp_of_antitoneOn`), and likewise on a bounded interval
(`TauCeti.le_div_mul_exp_of_antitoneOn_Icc`). This is how a differential inequality `E ≤ K (-E')`
is integrated without differentiating `E`: when `E (s) - E (s + T) = ∫ₛ^{s + T} g` with `E ≤ K g`,
monotonicity gives `T E (s + T) ≤ K (E s - E (s + T))`, a drop by the factor `K / (K + T)`. On an
interval `[a, b]` a nondecreasing `g` with `|g| ≤ T g'` decays exponentially away from both ends:
its positive part doubles forwards and its negative part doubles backwards over every step of
length `T`, so its increase over `[s₁, s₂]` is at most `4 (g b - g a)` times
`exp (-κ (b - s₂)) + exp (-κ (s₁ - a))`, `κ = log 2 / T`
(`TauCeti.sub_le_mul_exp_add_exp_of_two_mul_le`).

The bound `TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub` is the shape of the a priori bound
for implicit Euler schemes of gradient flows whose energy is not bounded below. A sequence `D n ≥ 0`
with `D 0 = 0` grows by steps `D (n + 1) ≤ D n + d n` whose squared lengths are bounded by the
energy dissipated, `d n ² ≤ 2τ (e n - e (n + 1))`, and the energy obeys the coercivity bound
`2τ' (A - e n) ≤ D n ²`. Then `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ` whenever `4τ ≤ τ'`.

## Main declarations

* `TauCeti.one_add_mul_pow_ceil_div_le_exp`: `(1 + aτ) ^ ⌈t / τ⌉₊ ≤ exp (a (t + τ))`.
* `TauCeti.tendsto_one_add_mul_pow` and `TauCeti.tendsto_mul_sum_one_add_mul_pow`: the growth
  factors `(1 + aτ) ^ L` and their sums `τ ∑_{n < L} (1 + aτ) ^ n` converge to `exp (a T)` and
  `∫₀ᵀ exp (a r) dr` as `τ → 0` with `L τ → T`.
* `TauCeti.inv_one_add_mul_pow_ceil_div_le_exp`: `(1 + mτ)⁻¹ ^ ⌈t / τ⌉₊ ≤ exp (|m| / c * (t + τ))`
  when `0 < c ≤ 1 + mτ`.
* `TauCeti.tendsto_ceil_div_mul`: `⌈r / τ j⌉₊ * τ j → r` when `0 ≤ r`, `0 < τ j` eventually, and
  `τ j → 0`.
* `TauCeti.eventually_ceil_div_lt_ceil_div`: `⌈s / τ j⌉₊ < ⌈t / τ j⌉₊` eventually when `0 < t`,
  `s < t`, `0 < τ j` eventually, and `τ j → 0`.
* `TauCeti.tendsto_ceil_div_sub_ceil_div_mul`: `(⌈t / τ j⌉₊ - ⌈s / τ j⌉₊) * τ j → t - s` when
  `0 ≤ s ≤ t`, `0 < τ j` eventually, and `τ j → 0`.
* `TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub`: the discrete Grönwall bound
  `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ` under coercivity.
* `TauCeti.le_div_mul_exp_of_antitoneOn_Icc`, `TauCeti.le_div_mul_exp_of_antitoneOn`: exponential
  decay of a nonincreasing function which drops by a fixed factor over every interval of a fixed
  length, on a bounded interval and on a half-line.
* `TauCeti.max_le_two_mul_max_mul_exp_of_two_mul_le`,
  `TauCeti.sub_le_mul_exp_add_exp_of_two_mul_le`: exponential decay on an interval of a
  nondecreasing function whose positive part doubles forwards, and whose negative part also
  doubles backwards, over steps of a fixed length.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 3, Section 3.2.
-/

public section

namespace TauCeti

/-- After `⌈t / τ⌉₊` time steps of length `τ`, a growth factor `1 + aτ` per step accumulates to at
most `exp (a (t + τ))`, since less than `t + τ` time has passed. The bound is uniform in the time
step `τ`. Only `0 ≤ t + τ` is needed: when `t ≤ 0` or `τ ≤ 0` no step is taken and the bound
reads `1 ≤ exp (a (t + τ))`. -/
theorem one_add_mul_pow_ceil_div_le_exp {a τ t : ℝ} (ha : 0 ≤ a) (htτ : 0 ≤ t + τ) :
    (1 + a * τ) ^ ⌈t / τ⌉₊ ≤ Real.exp (a * (t + τ)) := by
  rcases le_or_gt (t / τ) 0 with h | h
  · rw [Nat.ceil_eq_zero.2 h, pow_zero]
    exact Real.one_le_exp (mul_nonneg ha htτ)
  have hτ : 0 < τ := by rcases div_pos_iff.1 h with h | h <;> linarith [h.1, h.2]
  have h1 : (⌈t / τ⌉₊ : ℝ) * τ ≤ t + τ := by
    have := Nat.ceil_lt_add_one h.le
    rw [div_add_one hτ.ne', lt_div_iff₀ hτ] at this
    exact this.le
  calc (1 + a * τ) ^ ⌈t / τ⌉₊ ≤ Real.exp (a * τ) ^ ⌈t / τ⌉₊ := by
        gcongr
        linarith [Real.add_one_le_exp (a * τ)]
    _ = Real.exp (a * (⌈t / τ⌉₊ * τ)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (a * (t + τ)) := by gcongr

/-- **Convergence of the discrete growth factors.** If `L i` time steps of length `τ i → 0` take
the total time `L i τ i → T`, the accumulated growth factors `(1 + a τ i) ^ L i` converge to
`exp (a T)`. For `τ i = T / i` and `L i = i` this is `(1 + a T / i) ^ i → exp (a T)`. -/
theorem tendsto_one_add_mul_pow {ι : Type*} {l : Filter ι} {τ : ι → ℝ} {L : ι → ℕ} {a T : ℝ}
    (hτ : Filter.Tendsto τ l (nhds 0)) (hL : Filter.Tendsto (fun i ↦ L i * τ i) l (nhds T)) :
    Filter.Tendsto (fun i ↦ (1 + a * τ i) ^ L i) l (nhds (Real.exp (a * T))) := by
  have h1 : Filter.Tendsto (fun i ↦ 1 + a * τ i) l (nhds 1) := by
    simpa using (hτ.const_mul a).const_add 1
  have hpos : ∀ᶠ i in l, 0 < 1 + a * τ i := h1.eventually (lt_mem_nhds one_pos)
  -- `L log (1 + a τ)` lies between `a L τ / (1 + a τ)` and `a L τ`, which both tend to `a T`.
  have hup : Filter.Tendsto (fun i ↦ a * (L i * τ i)) l (nhds (a * T)) := hL.const_mul a
  have hlow : Filter.Tendsto (fun i ↦ a * (L i * τ i) * (1 + a * τ i)⁻¹) l (nhds (a * T)) := by
    simpa using hup.mul (h1.inv₀ one_ne_zero)
  have hlog : Filter.Tendsto (fun i ↦ L i * Real.log (1 + a * τ i)) l (nhds (a * T)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hpos] with i hi
      calc a * (L i * τ i) * (1 + a * τ i)⁻¹ = L i * (1 - (1 + a * τ i)⁻¹) := by
            field_simp
            ring
        _ ≤ L i * Real.log (1 + a * τ i) := by gcongr; exact Real.one_sub_inv_le_log_of_pos hi
    · filter_upwards [hpos] with i hi
      calc (L i : ℝ) * Real.log (1 + a * τ i) ≤ L i * (1 + a * τ i - 1) := by
            gcongr; exact Real.log_le_sub_one_of_pos hi
        _ = a * (L i * τ i) := by ring
  refine ((Real.continuous_exp.tendsto _).comp hlog).congr' ?_
  filter_upwards [hpos] with i hi
  rw [Function.comp_apply, Real.exp_nat_mul, Real.exp_log hi]

/-- **Convergence of the discrete exponential integrals.** If `L i` time steps of length `τ i → 0`
take the total time `L i τ i → T`, then `τ i ∑_{n < L i} (1 + a τ i) ^ n`, the discrete
counterpart of `∫₀ᵀ exp (a r) dr` for the growth factor `1 + a τ i` per step, converges to it. -/
theorem tendsto_mul_sum_one_add_mul_pow {ι : Type*} {l : Filter ι} {τ : ι → ℝ} {L : ι → ℕ}
    {a T : ℝ} (hτ : Filter.Tendsto τ l (nhds 0))
    (hL : Filter.Tendsto (fun i ↦ L i * τ i) l (nhds T)) :
    Filter.Tendsto (fun i ↦ τ i * ∑ n ∈ Finset.range (L i), (1 + a * τ i) ^ n) l
      (nhds (∫ r in 0..T, Real.exp (a * r))) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simpa [mul_comm] using hL
  -- For `a ≠ 0` both sides are the corresponding increments of the exponential, divided by `a`.
  have hint : ∫ r in 0..T, Real.exp (a * r) = (Real.exp (a * T) - 1) / a := by
    rw [intervalIntegral.integral_comp_mul_left (fun r ↦ Real.exp r) ha, integral_exp, mul_zero,
      Real.exp_zero, smul_eq_mul, inv_mul_eq_div]
  rw [hint]
  refine (((tendsto_one_add_mul_pow hτ hL).sub_const 1).div_const a).congr fun i ↦ ?_
  rw [← geom_sum_mul]
  field_simp
  ring

/-- After `⌈t / τ⌉₊` time steps of length `τ`, if the per-step factor satisfies `c ≤ 1 + m * τ`
with `0 < c`, then its inverse accumulates to at most `exp (|m| / c * (t + τ))`. Only
`0 ≤ t + τ` is needed: when `t ≤ 0` or `τ ≤ 0` no step is taken and the bound reads
`1 ≤ exp (|m| / c * (t + τ))`. -/
theorem inv_one_add_mul_pow_ceil_div_le_exp {m c τ t : ℝ} (hc : 0 < c) (hmτ : c ≤ 1 + m * τ)
    (htτ : 0 ≤ t + τ) :
    (1 + m * τ)⁻¹ ^ ⌈t / τ⌉₊ ≤ Real.exp (|m| / c * (t + τ)) := by
  rcases le_or_gt (t / τ) 0 with h | h
  · rw [Nat.ceil_eq_zero.2 h, pow_zero]
    exact Real.one_le_exp (by positivity)
  have hτ : 0 < τ := by rcases div_pos_iff.1 h with h | h <;> linarith [h.1, h.2]
  have hr_inv_le : (1 + m * τ)⁻¹ ≤ 1 + |m| / c * τ := by
    rw [inv_le_iff_one_le_mul₀ (hc.trans_le hmτ)]
    have h1 : |m| * τ ≤ |m| / c * τ * (1 + m * τ) := by
      calc |m| * τ = |m| / c * τ * c := by field_simp
        _ ≤ |m| / c * τ * (1 + m * τ) := by gcongr
    nlinarith [neg_abs_le m]
  calc (1 + m * τ)⁻¹ ^ ⌈t / τ⌉₊
      ≤ (1 + |m| / c * τ) ^ ⌈t / τ⌉₊ :=
        pow_le_pow_left₀ (inv_nonneg.2 (hc.trans_le hmτ).le) hr_inv_le _
    _ ≤ Real.exp (|m| / c * (t + τ)) :=
        one_add_mul_pow_ceil_div_le_exp (by positivity) htτ

/-- **Discrete Grönwall bound under coercivity.** Let `D n ≥ 0` with `D 0 = 0` grow by steps
`D (n + 1) ≤ D n + d n` whose squared lengths are paid for by an energy `e`,
`d n ² ≤ 2τ (e n - e (n + 1))`, and let the energy satisfy the coercivity bound
`2τ' (A - e n) ≤ D n ²`, where `0 ≤ τ` and `4τ ≤ τ'`. Then
`D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ`. -/
theorem sq_le_mul_one_add_div_pow_of_sq_le_mul_sub {D d e : ℕ → ℝ} {τ τ' A : ℝ} (hτ : 0 ≤ τ)
    (hττ' : 4 * τ ≤ τ') (hD0 : D 0 = 0) (hD : ∀ n, 0 ≤ D n) (htri : ∀ n, D (n + 1) ≤ D n + d n)
    (hstep : ∀ n, d n ^ 2 ≤ 2 * τ * (e n - e (n + 1)))
    (hcoer : ∀ n, 2 * τ' * (A - e n) ≤ D n ^ 2) (n : ℕ) :
    D n ^ 2 ≤ 2 * τ' * (e 0 - A) * (1 + 8 * τ / τ') ^ n := by
  have hA0 := hcoer 0
  rw [hD0] at hA0
  rcases hτ.eq_or_lt with rfl | hτ
  · -- With step size `0` every step vanishes, so `D` stays at `0`.
    have hDn : D n = 0 := by
      induction n with
      | zero => exact hD0
      | succ n ih => nlinarith [hD (n + 1), htri n, hstep n]
    simp only [hDn, mul_zero, zero_div, add_zero, one_pow, mul_one]
    linarith
  -- With `c = τ + τ' / 4`, the quantity `N n = D n ² + 2c (e n - A)` dominates `D n ² / 2` by the
  -- coercivity bound, and grows at most by the factor `1 + 8τ / τ'` per step by the triangle
  -- inequality, Young's inequality and the energy decrease along a step.
  have hτ' : 0 < τ' := by linarith
  set c := τ + τ' / 4 with hc
  set N : ℕ → ℝ := fun n ↦ D n ^ 2 + 2 * c * (e n - A) with hN
  -- `N` dominates `D ² / 2`.
  have hQ n : D n ^ 2 ≤ 2 * N n := by
    nlinarith [mul_le_mul_of_nonneg_left (hcoer n) (by positivity : (0 : ℝ) ≤ 2 * c),
      mul_nonneg (sq_nonneg (D n)) (by linarith : (0 : ℝ) ≤ τ' - 2 * c)]
  -- One step multiplies `N` by at most `1 + 8τ / τ'`.
  have hNstep n : N (n + 1) ≤ (1 + 8 * τ / τ') * N n := by
    have h1 : D (n + 1) ^ 2 ≤ (D n + d n) ^ 2 := pow_le_pow_left₀ (hD _) (htri n) 2
    have hY : (D n + d n) ^ 2 ≤ (1 + 4 * τ / τ') * D n ^ 2 + c / τ * d n ^ 2 := by
      rw [hc]
      field_simp
      nlinarith [sq_nonneg (4 * τ * D n - τ' * d n)]
    have hd' : c / τ * d n ^ 2 ≤ 2 * c * (e n - e (n + 1)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hτ]
      nlinarith [hstep n, (by positivity : (0 : ℝ) ≤ c)]
    have hQ' : 4 * τ / τ' * D n ^ 2 ≤ 8 * τ / τ' * N n :=
      (mul_le_mul_of_nonneg_left (hQ n) (by positivity)).trans_eq (by ring)
    simp only [hN] at hQ' ⊢
    linarith
  -- Iterating from `N 0 = 2c (e 0 - A) ≤ τ' (e 0 - A)`.
  have hNn : N n ≤ (1 + 8 * τ / τ') ^ n * (τ' * (e 0 - A)) := by
    induction n with
    | zero =>
      simp only [hN, hD0, pow_zero, one_mul]
      nlinarith
    | succ n ih =>
      rw [pow_succ', mul_assoc]
      exact (hNstep n).trans (by gcongr)
  linarith [hQ n]

/-- **Exponential decay from a fixed-step contraction on an interval.** Let `E` be nonincreasing
on `[s₀, s₁]`, with `E s₀ ≥ 0`, and suppose that `E (s + T) ≤ q E s` whenever `s₀ ≤ s` and
`s + T ≤ s₁`, where `0 < q ≤ 1`. Then `E s ≤ (E s₀ / q) exp ((log q / T) (s - s₀))` for every
`s ∈ [s₀, s₁]`. -/
theorem le_div_mul_exp_of_antitoneOn_Icc {E : ℝ → ℝ} {s₀ s₁ T q : ℝ} (hq : 0 < q)
    (hq1 : q ≤ 1) (hE : AntitoneOn E (Set.Icc s₀ s₁)) (h0 : 0 ≤ E s₀)
    (hstep : ∀ s, s₀ ≤ s → s + T ≤ s₁ → E (s + T) ≤ q * E s) {s : ℝ} (hs : s₀ ≤ s)
    (hs₁ : s ≤ s₁) : E s ≤ E s₀ / q * Real.exp (Real.log q / T * (s - s₀)) := by
  have hmem : s ∈ Set.Icc s₀ s₁ := ⟨hs, hs₁⟩
  rcases le_or_gt T 0 with hT | hT
  · -- For `T ≤ 0` the exponent is nonnegative and monotonicity alone suffices.
    have h1 : 1 ≤ Real.exp (Real.log q / T * (s - s₀)) :=
      Real.one_le_exp (mul_nonneg (div_nonneg_of_nonpos (Real.log_nonpos hq.le hq1) hT)
        (sub_nonneg.2 hs))
    calc E s ≤ E s₀ := hE ⟨le_rfl, hs.trans hs₁⟩ hmem hs
      _ ≤ E s₀ / q := le_div_self h0 hq hq1
      _ = E s₀ / q * 1 := (mul_one _).symm
      _ ≤ E s₀ / q * Real.exp (Real.log q / T * (s - s₀)) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg h0 hq.le)
  set n := ⌊(s - s₀) / T⌋₊
  have hy : 0 ≤ (s - s₀) / T := div_nonneg (sub_nonneg.2 hs) hT.le
  have hnT : n * T ≤ s - s₀ := (le_div_iff₀ hT).1 (Nat.floor_le hy)
  have hn1 : (s - s₀) / T < n + 1 := Nat.lt_floor_add_one _
  -- The steps up to the `n`-th one stay inside `[s₀, s₁]`.
  have hk (k : ℕ) (hkn : k ≤ n) : E (s₀ + k * T) ≤ q ^ k * E s₀ := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hkT : (k + 1 : ℝ) * T ≤ n * T :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hT.le
      calc E (s₀ + ↑(k + 1) * T) = E (s₀ + k * T + T) := by push_cast; ring_nf
        _ ≤ q * E (s₀ + k * T) :=
          hstep _ (by nlinarith [k.cast_nonneg (α := ℝ)]) (by linarith)
        _ ≤ q * (q ^ k * E s₀) := mul_le_mul_of_nonneg_left (ih (by omega)) hq.le
        _ = q ^ (k + 1) * E s₀ := by ring
  -- The time `s` lies in the `n`-th step, so `E s ≤ qⁿ E s₀ ≤ q ^ ((s - s₀) / T - 1) E s₀`.
  have hexp : q ^ (n + 1) ≤ Real.exp (Real.log q / T * (s - s₀)) := by
    rw [← Real.exp_log (pow_pos hq _), Real.exp_le_exp, Real.log_pow, div_mul_eq_mul_div,
      mul_div_assoc]
    push_cast
    nlinarith [Real.log_nonpos hq.le hq1]
  calc E s ≤ E (s₀ + n * T) := hE ⟨le_add_of_nonneg_right (by positivity), by linarith⟩ hmem
        (by linarith)
    _ ≤ q ^ n * E s₀ := hk n le_rfl
    _ = E s₀ / q * q ^ (n + 1) := by field_simp; ring
    _ ≤ E s₀ / q * Real.exp (Real.log q / T * (s - s₀)) :=
        mul_le_mul_of_nonneg_left hexp (div_nonneg h0 hq.le)

/-- **Exponential decay from a fixed-step contraction.** Let `E` be nonincreasing on `[s₀, ∞)`,
with `E s₀ ≥ 0`, and suppose that `E (s + T) ≤ q E s` for every `s ≥ s₀`, where `0 < q ≤ 1`. Then
`E s ≤ (E s₀ / q) exp ((log q / T) (s - s₀))` for every `s ≥ s₀`. -/
theorem le_div_mul_exp_of_antitoneOn {E : ℝ → ℝ} {s₀ T q : ℝ} (hq : 0 < q)
    (hq1 : q ≤ 1) (hE : AntitoneOn E (Set.Ici s₀)) (h0 : 0 ≤ E s₀)
    (hstep : ∀ s, s₀ ≤ s → E (s + T) ≤ q * E s) {s : ℝ} (hs : s₀ ≤ s) :
    E s ≤ E s₀ / q * Real.exp (Real.log q / T * (s - s₀)) :=
  le_div_mul_exp_of_antitoneOn_Icc hq hq1 (hE.mono Set.Icc_subset_Ici_self) h0
    (fun s hs _ ↦ hstep s hs) hs le_rfl

/-- **Decay away from the right end from forward doubling.** Let `g` be nondecreasing on `[a, b]`,
and suppose that `2 g s ≤ g (s + T)` whenever `a ≤ s` and `s + T ≤ b`. Then the positive part of `g`
decays exponentially away from `b`: for `s ∈ [a, b]`,
`max (g s) 0 ≤ 2 max (g b) 0 exp (-(log 2 / T) (b - s))`. -/
theorem max_le_two_mul_max_mul_exp_of_two_mul_le {g : ℝ → ℝ} {a b T : ℝ}
    (hg : MonotoneOn g (Set.Icc a b)) (hstep : ∀ s, a ≤ s → s + T ≤ b → 2 * g s ≤ g (s + T))
    {s : ℝ} (hs : a ≤ s) (hsb : s ≤ b) :
    max (g s) 0 ≤ 2 * max (g b) 0 * Real.exp (-(Real.log 2 / T * (b - s))) := by
  -- The positive part, read backwards from `b`, halves over every step of length `T`.
  have h := le_div_mul_exp_of_antitoneOn_Icc (E := fun r ↦ max (g (b - r)) 0) (s₀ := 0)
    (s₁ := b - a) (T := T) (s := b - s) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (fun r hr r' hr' hrr' ↦ max_le_max_right 0
      (hg ⟨by linarith [hr'.2], by linarith [hr'.1]⟩ ⟨by linarith [hr.2], by linarith [hr.1]⟩
        (by linarith)))
    (le_max_right _ _)
    (fun r hr hrT ↦ by
      have h := hstep (b - (r + T)) (by linarith) (by linarith)
      rw [show b - (r + T) + T = b - r by ring] at h
      exact max_le (by linarith [le_max_left (g (b - r)) 0])
        (mul_nonneg (by norm_num) (le_max_right _ _)))
    (sub_nonneg.2 hsb) (by linarith)
  have hlog : Real.log (1 / 2) = -Real.log 2 := by simp
  calc max (g s) 0 = max (g (b - (b - s))) 0 := by rw [sub_sub_cancel]
    _ ≤ _ := h
    _ = _ := by rw [hlog, sub_zero, sub_zero]; ring_nf

/-- On an interval `[a, b]` of length at least `T > 0`, if a nondecreasing `g` satisfies
`2 g s ≤ g (s + T)` and `g s ≤ 2 g (s + T)` over every step of length `T`, then the positive part of
`g` at `b` and its negative part at `a` together are at most twice the increase `g b - g a`. -/
private theorem max_add_max_neg_le_two_mul_sub {g : ℝ → ℝ} {a b T : ℝ}
    (hg : MonotoneOn g (Set.Icc a b))
    (hstep : ∀ s, a ≤ s → s + T ≤ b → 2 * g s ≤ g (s + T) ∧ g s ≤ 2 * g (s + T)) (hT : 0 < T)
    (hlong : T ≤ b - a) : max (g b) 0 + max (-g a) 0 ≤ 2 * (g b - g a) := by
  have hdbl := hstep a le_rfl (by linarith)
  have hmono := hg ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : a + T ≤ b)
  have hmono' := hg ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith : a ≤ b - T)
  have hdbl' := hstep (b - T) (by linarith) (sub_add_cancel b T).le
  rw [sub_add_cancel] at hdbl'
  rcases le_total 0 (g a) with ha | ha <;> rcases le_total 0 (g b) with hb | hb
  · rw [max_eq_left hb, max_eq_right (by linarith)]
    linarith [hdbl.1, hmono]
  · rw [max_eq_right hb, max_eq_right (by linarith)]
    linarith [hg ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : a ≤ b)]
  · rw [max_eq_left hb, max_eq_left (by linarith)]
    linarith
  · rw [max_eq_right hb, max_eq_left (by linarith)]
    linarith [hdbl'.2, hmono']

/-- **Two-sided exponential decay on an interval from doubling.** Let `g` be nondecreasing on
`[a, b]`, and suppose that over every step of length `T` inside `[a, b]` its positive part at
least doubles forwards and its negative part at least doubles backwards: `2 g s ≤ g (s + T)` and
`g s ≤ 2 g (s + T)` whenever `a ≤ s` and `s + T ≤ b`. Then the increase of `g` over
`[s₁, s₂] ⊆ [a, b]` is exponentially small in the distances of `s₂` from `b` and of `s₁` from `a`,
relative to its total increase over `[a, b]`:
`g s₂ - g s₁ ≤ 4 (g b - g a) (exp (-κ (b - s₂)) + exp (-κ (s₁ - a)))` with `κ = log 2 / T`.

For a function with `|g| ≤ T g'` the doubling conditions hold, so this integrates the
differential inequality on an interval. It describes a quantity such as the action along a long
neck near a nondegenerate critical point, which is positive only near the right end and negative
only near the left end. -/
theorem sub_le_mul_exp_add_exp_of_two_mul_le {g : ℝ → ℝ} {a b T : ℝ}
    (hg : MonotoneOn g (Set.Icc a b))
    (hstep : ∀ s, a ≤ s → s + T ≤ b → 2 * g s ≤ g (s + T) ∧ g s ≤ 2 * g (s + T))
    {s₁ s₂ : ℝ} (h₁ : a ≤ s₁) (h₁₂ : s₁ ≤ s₂) (h₂ : s₂ ≤ b) :
    g s₂ - g s₁ ≤ 4 * (g b - g a) *
      (Real.exp (-(Real.log 2 / T * (b - s₂))) + Real.exp (-(Real.log 2 / T * (s₁ - a)))) := by
  set κ := Real.log 2 / T
  have hab : a ≤ b := h₁.trans (h₁₂.trans h₂)
  have hmem {s : ℝ} (h : a ≤ s) (h' : s ≤ b) : s ∈ Set.Icc a b := ⟨h, h'⟩
  have hD : 0 ≤ g b - g a := sub_nonneg.2 (hg (hmem le_rfl hab) (hmem hab le_rfl) hab)
  have hE₁ := (Real.exp_pos (-(κ * (b - s₂)))).le
  have hE₂ := (Real.exp_pos (-(κ * (s₁ - a)))).le
  have hinc : g s₂ - g s₁ ≤ g b - g a := by
    have := hg (hmem h₁ (h₁₂.trans h₂)) (hmem (h₁.trans h₁₂) h₂) h₁₂
    have := hg (hmem (h₁.trans h₁₂) h₂) (hmem hab le_rfl) h₂
    have := hg (hmem le_rfl hab) (hmem h₁ (h₁₂.trans h₂)) h₁
    linarith
  rcases le_or_gt T 0 with hT | hT
  · -- For `T ≤ 0` the exponents are nonnegative and the total increase suffices.
    have h1 : 1 ≤ Real.exp (-(κ * (b - s₂))) := Real.one_le_exp (by
      nlinarith [div_nonpos_of_nonneg_of_nonpos (Real.log_nonneg one_le_two) hT])
    nlinarith
  rcases lt_or_ge (b - a) T with hshort | hlong
  · -- On a short interval `exp (-κ (b - s₂)) ≥ 1 / 2` and the total increase suffices.
    have hκ : κ * (b - s₂) ≤ Real.log 2 := calc
      κ * (b - s₂) ≤ κ * T :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (Real.log_nonneg one_le_two) hT.le)
      _ = Real.log 2 := div_mul_cancel₀ _ hT.ne'
    have hhalf : 1 / 2 ≤ Real.exp (-(κ * (b - s₂))) := calc
      (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log two_pos, one_div]
      _ ≤ _ := Real.exp_le_exp.2 (neg_le_neg hκ)
    nlinarith
  -- The positive part of `g` decays away from `b`, and its negative part, the positive part of
  -- the reflection `r ↦ -g (a + b - r)`, decays away from `a`.
  have hp := max_le_two_mul_max_mul_exp_of_two_mul_le hg (fun s hs hsT ↦ (hstep s hs hsT).1)
    (h₁.trans h₁₂) h₂
  have hm := max_le_two_mul_max_mul_exp_of_two_mul_le (g := fun r ↦ -g (a + b - r)) (a := a)
    (b := b) (T := T)
    (fun r hr r' hr' hrr' ↦ neg_le_neg (hg ⟨by linarith [hr'.2], by linarith [hr'.1]⟩
      ⟨by linarith [hr.2], by linarith [hr.1]⟩ (by linarith)))
    (fun r hr hrT ↦ by
      have h := (hstep (a + b - (r + T)) (by linarith) (by linarith)).2
      rw [show a + b - (r + T) + T = a + b - r by ring] at h
      linarith)
    (s := a + b - s₁) (by linarith) (by linarith)
  simp only [show a + b - (a + b - s₁) = s₁ by ring, add_sub_cancel_right,
    show b - (a + b - s₁) = s₁ - a by ring] at hm
  -- On a long interval the two parts at the ends are bounded by twice the total increase.
  have hpm := max_add_max_neg_le_two_mul_sub hg hstep hT hlong
  have hp0 : 0 ≤ max (g b) 0 := le_max_right _ _
  have hm0 : 0 ≤ max (-g a) 0 := le_max_right _ _
  have := le_max_left (g s₂) 0
  have := le_max_left (-g s₁) 0
  nlinarith

open Filter Topology in
/-- Along any filter `l`, if `0 ≤ r`, `0 < τ j` eventually, and `τ j → 0`, then
`⌈r / τ j⌉₊ * τ j → r`. -/
theorem tendsto_ceil_div_mul {ι : Type*} {l : Filter ι} {r : ℝ} {τ : ι → ℝ} (hr : 0 ≤ r)
    (hτ_pos : ∀ᶠ j in l, 0 < τ j) (hτ0 : Tendsto τ l (𝓝 0)) :
    Tendsto (fun j ↦ (⌈r / τ j⌉₊ : ℝ) * τ j) l (𝓝 r) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using tendsto_const_nhds.add hτ0)
    (hτ_pos.mono fun _ hj ↦ le_ceil_div_mul hj)
    (hτ_pos.mono fun _ hj ↦ (ceil_div_mul_lt_add hr hj).le)

open Filter Topology in
/-- Along any filter `l`, if `0 < t`, `s < t`, `0 < τ j` eventually, and `τ j → 0`, then
`⌈s / τ j⌉₊ < ⌈t / τ j⌉₊` eventually. -/
theorem eventually_ceil_div_lt_ceil_div {ι : Type*} {l : Filter ι} {s t : ℝ} {τ : ι → ℝ}
    (ht : 0 < t) (hst : s < t) (hτ_pos : ∀ᶠ j in l, 0 < τ j) (hτ0 : Tendsto τ l (𝓝 0)) :
    ∀ᶠ j in l, ⌈s / τ j⌉₊ < ⌈t / τ j⌉₊ := by
  rcases lt_or_ge s 0 with hs | hs
  · refine hτ_pos.mono fun j hj ↦ ?_
    rw [Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg hs.le hj.le)]
    exact Nat.ceil_pos.2 (div_pos ht hj)
  · filter_upwards [hτ_pos, hτ0.eventually (gt_mem_nhds (sub_pos.2 hst))] with j hj hlt
    exact Nat.cast_lt.1 <| lt_of_mul_lt_mul_right
      ((ceil_div_mul_lt_add hs hj).trans_le
        ((by linarith : s + τ j ≤ t).trans (le_ceil_div_mul hj)))
      hj.le

open Filter Topology in
/-- Along any filter `l`, if `0 ≤ s ≤ t`, `0 < τ j` eventually, and `τ j → 0`, then
`((⌈t / τ j⌉₊ - ⌈s / τ j⌉₊ : ℕ) : ℝ) * τ j → t - s`. -/
theorem tendsto_ceil_div_sub_ceil_div_mul {ι : Type*} {l : Filter ι} {s t : ℝ} {τ : ι → ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hτ_pos : ∀ᶠ j in l, 0 < τ j) (hτ0 : Tendsto τ l (𝓝 0)) :
    Tendsto (fun j ↦ ((⌈t / τ j⌉₊ - ⌈s / τ j⌉₊ : ℕ) : ℝ) * τ j) l (𝓝 (t - s)) := by
  refine ((tendsto_ceil_div_mul (hs.trans hst) hτ_pos hτ0).sub
    (tendsto_ceil_div_mul hs hτ_pos hτ0)).congr' (hτ_pos.mono fun j hj ↦ ?_)
  have hle : ⌈s / τ j⌉₊ ≤ ⌈t / τ j⌉₊ :=
    Nat.ceil_mono (div_le_div_of_nonneg_right hst hj.le)
  dsimp only
  rw [← sub_mul, Nat.cast_sub hle]

end TauCeti
