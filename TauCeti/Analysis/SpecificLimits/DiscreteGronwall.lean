/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Discrete Grönwall estimates for implicit time stepping

A discrete Grönwall argument shows that a quantity growing at most by the factor `1 + aτ` per
time step of length `τ` grows at most like `exp (a t)` up to time `t`. This file records the
growth factor estimate `(1 + aτ) ^ ⌈t / τ⌉₊ ≤ exp (a (t + τ))`, valid uniformly in the time
step (`TauCeti.one_add_mul_pow_ceil_div_le_exp`), and a discrete Grönwall bound for sequences
that move in steps paid for by an energy which is bounded below in terms of the distance
travelled (`TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub`).

Conversely, a nonincreasing quantity which drops at least by a factor `q < 1` over every time
interval of length `T` decays exponentially, at the rate `-log q / T`
(`TauCeti.le_div_mul_exp_of_antitoneOn`). This is how a differential inequality `E ≤ K (-E')` is
integrated without differentiating `E`: when `E (s) - E (s + T) = ∫ₛ^{s + T} g` with `E ≤ K g`,
monotonicity gives `T E (s + T) ≤ K (E s - E (s + T))`, a drop by the factor `K / (K + T)`.

The two-sided version concerns a nondecreasing `g` with `|g| ≤ K g'`, again in integrated form:
over every step of length `K`, `g` at least doubles where it is nonnegative and `-g` at least
halves where `g` is nonpositive. Then the increase of `g` over `[a + T, b - T]` is at most
`2 exp (-(log 2 / K) T)` times its increase over `[a, b]`, whatever the sign of `g` in between
(`TauCeti.sub_le_two_mul_exp_mul_sub`): the increase concentrates exponentially at the two ends
of the interval.

The discrete Grönwall bound `TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub` is the shape of
the a priori bound for implicit Euler schemes of gradient flows whose energy is not bounded
below. A sequence `D n ≥ 0` with `D 0 = 0` grows by steps `D (n + 1) ≤ D n + d n` whose squared
lengths are bounded by the energy dissipated,
`d n ² ≤ 2τ (e n - e (n + 1))`, and the energy obeys the coercivity bound
`2τ' (A - e n) ≤ D n ²`. Then `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ` whenever `4τ ≤ τ'`.

## Main declarations

* `TauCeti.one_add_mul_pow_ceil_div_le_exp`: `(1 + aτ) ^ ⌈t / τ⌉₊ ≤ exp (a (t + τ))`.
* `TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub`: the discrete Grönwall bound
  `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ` under coercivity.
* `TauCeti.le_div_mul_exp_of_antitoneOn`: exponential decay of a nonincreasing function which
  drops by a fixed factor over every interval of a fixed length.
* `TauCeti.sub_le_two_mul_exp_mul_sub`: the increase of a nondecreasing function which grows
  geometrically away from its zero concentrates exponentially at the ends of the interval.

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

/-- Iterating `2 g(s) ≤ g(s + K)` where `g ≥ 0`: above a level `m ≥ 0`, `g - m` at least
doubles over every step of length `K`. -/
private theorem two_pow_mul_sub_le_sub_of_two_mul_le {g : ℝ → ℝ} {a b K : ℝ} (hK : 0 ≤ K)
    (hpos : ∀ s, a ≤ s → s + K ≤ b → 0 ≤ g s → 2 * g s ≤ g (s + K)) (n : ℕ) :
    ∀ s, a ≤ s → s + n * K ≤ b → ∀ m, 0 ≤ m → m ≤ g s →
      2 ^ n * (g s - m) ≤ g (s + n * K) - m := by
  induction n with
  | zero => intro s _ _ m _ _; simp
  | succ n ih =>
    intro s hs hsb m hm hms
    push_cast at hsb ⊢
    have hnK : 0 ≤ (n : ℝ) * K := by positivity
    have h1 := hpos s hs (by linarith) (hm.trans hms)
    have h2 := ih (s + K) (by linarith) (by linarith) m hm (by linarith)
    rw [show s + K + n * K = s + (n + 1) * K by ring] at h2
    calc (2 : ℝ) ^ (n + 1) * (g s - m) = 2 ^ n * (2 * (g s - m)) := by ring
      _ ≤ 2 ^ n * (g (s + K) - m) := by gcongr; linarith
      _ ≤ _ := h2

/-- Iterating `g(s) ≤ 2 g(s + K)` where `g(s + K) ≤ 0`: below a level `m ≤ 0`, `m - g` at least
halves over every step of length `K`. -/
private theorem two_pow_mul_sub_le_sub_of_le_two_mul {g : ℝ → ℝ} {a b K : ℝ} (hK : 0 ≤ K)
    (hg : MonotoneOn g (Set.Icc a b))
    (hneg : ∀ s, a ≤ s → s + K ≤ b → g (s + K) ≤ 0 → g s ≤ 2 * g (s + K)) (n : ℕ) :
    ∀ s, a ≤ s → s + n * K ≤ b → ∀ m ≤ 0, g (s + n * K) ≤ m →
      2 ^ n * (m - g (s + n * K)) ≤ m - g s := by
  induction n with
  | zero => intro s _ _ m _ _; simp
  | succ n ih =>
    intro s hs hsb m hm hgm
    push_cast at hsb hgm ⊢
    have hnK : 0 ≤ (n : ℝ) * K := by positivity
    have hK' : s + K + n * K = s + (n + 1) * K := by ring
    have h2 := ih (s + K) (by linarith) (by linarith) m hm (by rwa [hK'])
    rw [hK'] at h2
    have hle : g (s + K) ≤ g (s + (n + 1) * K) :=
      hg ⟨by linarith, by linarith⟩ ⟨by linarith, hsb⟩ (by linarith)
    have h1 := hneg s hs (by linarith) (by linarith)
    calc (2 : ℝ) ^ (n + 1) * (m - g (s + (n + 1) * K)) =
          2 * (2 ^ n * (m - g (s + (n + 1) * K))) := by ring
      _ ≤ 2 * (m - g (s + K)) := by gcongr
      _ ≤ m - g s := by linarith

/-- **Two-sided growth away from the zero of a monotone function.** Let `g` be nondecreasing on
`[a, b]`, and suppose that over every step `[s, s + K] ⊆ [a, b]` of length `K > 0`, `g` at least
doubles where it is nonnegative, `2 g(s) ≤ g(s + K)`, and `-g` at least halves where `g` is
nonpositive, `g(s) ≤ 2 g(s + K)`. Then the increase of `g` over `[a + T, b - T]` is at most
`2 exp (-(log 2 / K) T)` times its increase over `[a, b]`. This is how the two-sided
differential inequality `|g| ≤ K g'` is integrated without differentiating `g`. -/
theorem sub_le_two_mul_exp_mul_sub {g : ℝ → ℝ} {a b K T : ℝ} (hK : 0 < K)
    (hg : MonotoneOn g (Set.Icc a b))
    (hpos : ∀ s, a ≤ s → s + K ≤ b → 0 ≤ g s → 2 * g s ≤ g (s + K))
    (hneg : ∀ s, a ≤ s → s + K ≤ b → g (s + K) ≤ 0 → g s ≤ 2 * g (s + K))
    (hT : 0 ≤ T) (hab : a + T ≤ b - T) :
    g (b - T) - g (a + T) ≤ 2 * Real.exp (-(Real.log 2 / K * T)) * (g b - g a) := by
  set n := ⌊T / K⌋₊
  have hnK : (n : ℝ) * K ≤ T := (le_div_iff₀ hK).1 (Nat.floor_le (div_nonneg hT hK.le))
  have hn0 : 0 ≤ (n : ℝ) * K := by positivity
  have hP := two_pow_mul_sub_le_sub_of_two_mul_le hK.le hpos n
  have hN := two_pow_mul_sub_le_sub_of_le_two_mul hK.le hg hneg n
  have hmem {s : ℝ} (h₁ : a ≤ s) (h₂ : s ≤ b) : s ∈ Set.Icc a b := ⟨h₁, h₂⟩
  have hgab : g (a + T) ≤ g (b - T) := hg (hmem (by linarith) (by linarith))
    (hmem (by linarith) (by linarith)) hab
  have hga : g a ≤ g (a + T) := hg (hmem le_rfl (by linarith)) (hmem (by linarith) (by linarith))
    (by linarith)
  have hgb : g (b - T) ≤ g b := hg (hmem (by linarith) (by linarith)) (hmem (by linarith) le_rfl)
    (by linarith)
  -- The points `b - T + n K` and `a + T - n K` stay in `[a, b]`.
  have hgr : g (b - T + n * K) ≤ g b :=
    hg (hmem (by linarith) (by linarith)) (hmem (by linarith) le_rfl) (by linarith)
  have hgl : g a ≤ g (a + T - n * K) :=
    hg (hmem le_rfl (by linarith)) (hmem (by linarith) (by linarith)) (by linarith)
  have hl : a + T - n * K + n * K = a + T := by ring
  -- First the estimate `2 ^ n (g(b - T) - g(a + T)) ≤ g b - g a`, according to the sign of `g`.
  have hmain : 2 ^ n * (g (b - T) - g (a + T)) ≤ g b - g a := by
    by_cases h₁ : 0 ≤ g (a + T)
    · have := hP (b - T) (by linarith) (by linarith) (g (a + T)) h₁ hgab
      linarith
    by_cases h₂ : g (b - T) ≤ 0
    · have := hN (a + T - n * K) (by linarith) (by rw [hl]; linarith) (g (b - T)) h₂
        (by rwa [hl])
      rw [hl] at this
      linarith
    push Not at h₁ h₂
    have hp := hP (b - T) (by linarith) (by linarith) 0 le_rfl h₂.le
    have hq := hN (a + T - n * K) (by linarith) (by rw [hl]; linarith) 0 le_rfl
      (by rw [hl]; exact h₁.le)
    rw [hl] at hq
    linarith
  -- Then `exp ((log 2 / K) T) ≤ 2 ^ (n + 1)`, since `T / K < n + 1`.
  have hexp : Real.exp (Real.log 2 / K * T) ≤ 2 * 2 ^ n := by
    have hlt : T / K < n + 1 := Nat.lt_floor_add_one (T / K)
    calc Real.exp (Real.log 2 / K * T) = Real.exp ((T / K) * Real.log 2) := by
          congr 1
          ring
      _ ≤ Real.exp (((n + 1 : ℕ) : ℝ) * Real.log 2) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by push_cast; exact hlt.le)
            (Real.log_pos one_lt_two).le)
      _ = 2 * 2 ^ n := by rw [Real.exp_nat_mul, Real.exp_log two_pos, pow_succ, mul_comm]
  have hD : 0 ≤ g (b - T) - g (a + T) := sub_nonneg.2 hgab
  have hmul : Real.exp (Real.log 2 / K * T) * (g (b - T) - g (a + T)) ≤ 2 * (g b - g a) :=
    calc _ ≤ 2 * 2 ^ n * (g (b - T) - g (a + T)) := mul_le_mul_of_nonneg_right hexp hD
      _ = 2 * (2 ^ n * (g (b - T) - g (a + T))) := by ring
      _ ≤ 2 * (g b - g a) := by gcongr
  rw [Real.exp_neg]
  have hpos' := Real.exp_pos (Real.log 2 / K * T)
  rw [mul_comm 2, mul_assoc, inv_mul_eq_div, le_div_iff₀ hpos']
  linarith

end TauCeti
