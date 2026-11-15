/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Discrete Grönwall estimates for implicit time stepping

A discrete Grönwall argument shows that a quantity growing at most by the factor `1 + aτ` per
time step of length `τ` grows at most like `exp (a t)` up to time `t`. This file records the
growth factor estimate `(1 + aτ) ^ ⌈t / τ⌉₊ ≤ exp (a (t + τ))`, valid uniformly in the time
step (`TauCeti.one_add_mul_pow_ceil_div_le_exp`), the matching discrete-to-continuous exponential
limit `(1 + m * τ j) ^ N j → exp (m * d)` when `τ j → 0` and `N j * τ j → d`
(`TauCeti.tendsto_one_add_mul_pow`), and a discrete Grönwall bound for sequences
that move in steps paid for by an energy which is bounded below in terms of the distance
travelled (`TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub`).

Conversely, a nonincreasing quantity which drops at least by a factor `q < 1` over every time
interval of length `T` decays exponentially, at the rate `-log q / T`
(`TauCeti.le_div_mul_exp_of_antitoneOn`). This is how a differential inequality `E ≤ K (-E')` is
integrated without differentiating `E`: when `E (s) - E (s + T) = ∫ₛ^{s + T} g` with `E ≤ K g`,
monotonicity gives `T E (s + T) ≤ K (E s - E (s + T))`, a drop by the factor `K / (K + T)`.

The second estimate is the shape of the a priori bound for implicit Euler schemes of gradient
flows whose energy is not bounded below. A sequence `D n ≥ 0` with `D 0 = 0` grows by steps
`D (n + 1) ≤ D n + d n` whose squared lengths are bounded by the energy dissipated,
`d n ² ≤ 2τ (e n - e (n + 1))`, and the energy obeys the coercivity bound
`2τ' (A - e n) ≤ D n ²`. Then `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ` whenever `4τ ≤ τ'`.

## Main declarations

* `TauCeti.one_add_mul_pow_ceil_div_le_exp`: `(1 + aτ) ^ ⌈t / τ⌉₊ ≤ exp (a (t + τ))`.
* `TauCeti.tendsto_one_add_mul_pow`: `(1 + m * τ j) ^ N j → exp (m * d)` when `τ j → 0` and
  `N j * τ j → d`.
* `TauCeti.tendsto_ceil_div_mul`: `⌈r / τ j⌉₊ * τ j → r` when `0 ≤ r`, `0 < τ j` eventually, and
  `τ j → 0`.
* `TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub`: the discrete Grönwall bound
  `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ` under coercivity.
* `TauCeti.le_div_mul_exp_of_antitoneOn`: exponential decay of a nonincreasing function which
  drops by a fixed factor over every interval of a fixed length.

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

/-- **Exponential decay from a fixed-step contraction.** Let `E` be nonincreasing on `[s₀, ∞)`,
with `E s₀ ≥ 0`, and suppose that `E (s + T) ≤ q E s` for every `s ≥ s₀`, where `0 < q ≤ 1`. Then
`E s ≤ (E s₀ / q) exp ((log q / T) (s - s₀))` for every `s ≥ s₀`. -/
theorem le_div_mul_exp_of_antitoneOn {E : ℝ → ℝ} {s₀ T q : ℝ} (hq : 0 < q)
    (hq1 : q ≤ 1) (hE : AntitoneOn E (Set.Ici s₀)) (h0 : 0 ≤ E s₀)
    (hstep : ∀ s, s₀ ≤ s → E (s + T) ≤ q * E s) {s : ℝ} (hs : s₀ ≤ s) :
    E s ≤ E s₀ / q * Real.exp (Real.log q / T * (s - s₀)) := by
  rcases le_or_gt T 0 with hT | hT
  · -- For `T ≤ 0` the exponent is nonnegative and monotonicity alone suffices.
    have h1 : 1 ≤ Real.exp (Real.log q / T * (s - s₀)) :=
      Real.one_le_exp (mul_nonneg (div_nonneg_of_nonpos (Real.log_nonpos hq.le hq1) hT)
        (sub_nonneg.2 hs))
    calc E s ≤ E s₀ := hE (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
      _ ≤ E s₀ / q := le_div_self h0 hq hq1
      _ = E s₀ / q * 1 := (mul_one _).symm
      _ ≤ E s₀ / q * Real.exp (Real.log q / T * (s - s₀)) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg h0 hq.le)
  have hk (k : ℕ) : E (s₀ + k * T) ≤ q ^ k * E s₀ := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc E (s₀ + ↑(k + 1) * T) = E (s₀ + k * T + T) := by push_cast; ring_nf
        _ ≤ q * E (s₀ + k * T) := hstep _ (by nlinarith [k.cast_nonneg (α := ℝ)])
        _ ≤ q * (q ^ k * E s₀) := mul_le_mul_of_nonneg_left ih hq.le
        _ = q ^ (k + 1) * E s₀ := by ring
  set n := ⌊(s - s₀) / T⌋₊
  have hy : 0 ≤ (s - s₀) / T := div_nonneg (sub_nonneg.2 hs) hT.le
  have hnT : n * T ≤ s - s₀ := (le_div_iff₀ hT).1 (Nat.floor_le hy)
  have hn1 : (s - s₀) / T < n + 1 := Nat.lt_floor_add_one _
  -- The time `s` lies in the `n`-th step, so `E s ≤ qⁿ E s₀ ≤ q ^ ((s - s₀) / T - 1) E s₀`.
  have hexp : q ^ (n + 1) ≤ Real.exp (Real.log q / T * (s - s₀)) := by
    rw [← Real.exp_log (pow_pos hq _), Real.exp_le_exp, Real.log_pow, div_mul_eq_mul_div,
      mul_div_assoc]
    push_cast
    nlinarith [Real.log_nonpos hq.le hq1]
  calc E s ≤ E (s₀ + n * T) := hE (Set.mem_Ici.2 (le_add_of_nonneg_right (by positivity)))
        (Set.mem_Ici.2 hs) (by linarith)
    _ ≤ q ^ n * E s₀ := hk n
    _ = E s₀ / q * q ^ (n + 1) := by field_simp; ring
    _ ≤ E s₀ / q * Real.exp (Real.log q / T * (s - s₀)) :=
        mul_le_mul_of_nonneg_left hexp (div_nonneg h0 hq.le)

open Filter Topology in
/-- **Discrete-to-continuous exponential limit.** Along any filter `l`, if the step sizes `τ j`
tend to `0` and the accumulated times `N j * τ j` tend to `d`, then `(1 + m * τ j) ^ N j` tends to
`exp (m * d)`. -/
theorem tendsto_one_add_mul_pow {ι : Type*} {l : Filter ι} {m d : ℝ} {τ : ι → ℝ} {N : ι → ℕ}
    (hτ0 : Tendsto τ l (𝓝 0)) (hN : Tendsto (fun j ↦ (N j : ℝ) * τ j) l (𝓝 d)) :
    Tendsto (fun j ↦ (1 + m * τ j) ^ N j) l (𝓝 (Real.exp (m * d))) := by
  have h1 : ∀ᶠ j in l, 0 < 1 + m * τ j := by
    have htend : Tendsto (fun j ↦ 1 + m * τ j) l (𝓝 1) := by
      simpa using tendsto_const_nhds.add (hτ0.const_mul m)
    exact htend.eventually (lt_mem_nhds one_pos)
  -- Extend the difference quotient `x ↦ log (1 + x) / x` continuously across `x = 0` by `1`.
  let g : ℝ → ℝ := fun x ↦ if x = 0 then 1 else slope (fun y : ℝ ↦ Real.log (1 + y)) 0 x
  have hg : Tendsto g (𝓝 0) (𝓝 1) := by
    have hd : HasDerivAt (fun y : ℝ ↦ Real.log (1 + y)) 1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num)
    refine tendsto_def.2 fun s hs ↦ ?_
    have hne : ∀ᶠ x in 𝓝[≠] 0, slope (fun y ↦ Real.log (1 + y)) 0 x ∈ s :=
      (hasDerivAt_iff_tendsto_slope.1 hd).eventually hs
    rw [eventually_nhdsWithin_iff] at hne
    exact hne.mono fun x hx ↦ by
      by_cases hx0 : x = 0 <;> simp [g, hx0, mem_of_mem_nhds hs, hx]
  have hexp_arg : Tendsto (fun j ↦ (N j : ℝ) * Real.log (1 + m * τ j)) l (𝓝 (m * d)) := by
    have hmτ : Tendsto (fun j ↦ m * τ j) l (𝓝 0) := by simpa using hτ0.const_mul m
    have hprod : Tendsto (fun j ↦ ((N j : ℝ) * τ j * m) * g (m * τ j)) l (𝓝 (d * m * 1)) :=
      (hN.mul_const m).mul (hg.comp hmτ)
    rw [show d * m * 1 = m * d by ring] at hprod
    refine hprod.congr fun j ↦ ?_
    by_cases h0 : m * τ j = 0
    · calc (N j : ℝ) * τ j * m * g (m * τ j)
          = (N j : ℝ) * (m * τ j) * g (m * τ j) := by ring
        _ = 0 := by simp [h0]
        _ = (N j : ℝ) * Real.log (1 + m * τ j) := by simp [h0]
    · have hm : m ≠ 0 := left_ne_zero_of_mul h0
      have hτj : τ j ≠ 0 := right_ne_zero_of_mul h0
      simp only [g, h0, ↓reduceIte, slope_def_field, sub_zero, add_zero, Real.log_one]
      field_simp
  refine ((Real.continuous_exp.tendsto _).comp hexp_arg).congr' (h1.mono fun j hj ↦ ?_)
  simp only [Function.comp_apply]
  rw [Real.exp_nat_mul, Real.exp_log hj]

/-- If `0 ≤ τ` and `|m| * τ ≤ c`, then the implicit Euler factor `1 + m * τ` lies in
`[1 - c, 1 + c]`. -/
theorem one_add_mul_mem_Icc_of_abs_mul_le {m τ c : ℝ} (hτ : 0 ≤ τ) (h : |m| * τ ≤ c) :
    1 + m * τ ∈ Set.Icc (1 - c) (1 + c) := by
  have hmτ : |m * τ| ≤ c := by rwa [abs_mul, abs_of_nonneg hτ]
  exact ⟨by linarith [neg_abs_le (m * τ)], by linarith [le_abs_self (m * τ)]⟩

/-- If `0 < k` and `τ ≤ (k * (|m| + 1))⁻¹`, then `|m| * τ ≤ k⁻¹`. -/
theorem abs_mul_le_inv_of_le_inv {m τ k : ℝ} (hk : 0 < k) (hτ : τ ≤ (k * (|m| + 1))⁻¹) :
    |m| * τ ≤ k⁻¹ := by
  calc |m| * τ ≤ |m| * (k * (|m| + 1))⁻¹ := by gcongr
    _ ≤ (|m| + 1) * (k * (|m| + 1))⁻¹ := by gcongr; linarith
    _ = k⁻¹ := by field_simp [show |m| + 1 ≠ 0 by positivity]

/-- For `0 < τ`, `t ≤ ⌈t / τ⌉₊ * τ`. -/
theorem le_ceil_div_mul {t τ : ℝ} (hτ : 0 < τ) : t ≤ (⌈t / τ⌉₊ : ℝ) * τ :=
  (div_le_iff₀ hτ).1 (Nat.le_ceil _)

/-- For `0 ≤ t` and `0 < τ`, `⌈t / τ⌉₊ * τ < t + τ`. -/
theorem ceil_div_mul_lt_add {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ) :
    (⌈t / τ⌉₊ : ℝ) * τ < t + τ := by
  simpa [add_mul, div_mul_cancel₀ t hτ.ne'] using
    mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg ht hτ.le)) hτ

/-- If `0 < δ` and `i + 1 ≤ ⌈T / δ⌉₊`, then `(i + 1) * δ < T + δ`. -/
theorem add_one_mul_lt_add_of_add_one_le_ceil_div {i : ℕ} {T δ : ℝ} (hδ : 0 < δ)
    (hi : i + 1 ≤ ⌈T / δ⌉₊) : ((i + 1 : ℕ) : ℝ) * δ < T + δ := by
  have hlt : (i : ℝ) < T / δ := by
    by_contra h
    exact absurd (Nat.ceil_le.2 (not_lt.1 h)) (by omega)
  have : (i : ℝ) * δ < T := (lt_div_iff₀ hδ).1 hlt
  push_cast
  linarith

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

end TauCeti
