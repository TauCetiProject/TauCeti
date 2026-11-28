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
monotonicity gives `T E (s + T) ≤ K (E s - E (s + T))`, a drop by the factor `K / (K + T)`.

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
    _ = Real.exp (a * (⌈t / τ⌉₊ * τ)) := by rw [← Real.exp_natCast_mul]; ring_nf
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
  rw [Function.comp_apply, Real.exp_natCast_mul, Real.exp_log hi]

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
