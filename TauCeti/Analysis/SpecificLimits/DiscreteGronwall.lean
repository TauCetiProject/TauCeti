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
import TauCeti.Algebra.Order.Floor.Semifield

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

The second estimate is the shape of the a priori bound for implicit Euler schemes of gradient
flows whose energy is not bounded below. A sequence `D n ≥ 0` with `D 0 = 0` grows by steps
`D (n + 1) ≤ D n + d n` whose squared lengths are bounded by the energy dissipated,
`d n ² ≤ 2τ (e n - e (n + 1))`, and the energy obeys the coercivity bound
`2τ' (A - e n) ≤ D n ²`. Then `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ` whenever `4τ ≤ τ'`.

Finally, as the time step `τ` tends to `0`, small steps satisfy `1 + λ τ > 0`
(`TauCeti.one_add_mul_pos_of_abs_mul_lt_one`, `TauCeti.eventually_one_add_mul_pos`,
`TauCeti.exists_pos_one_add_mul_pos`), the discrete elapsed time `(⌈t / τ⌉₊ - ⌈s / τ⌉₊) τ` tends
to `t - s` (`TauCeti.tendsto_natCast_sub_ceil_mul`), and `(1 + λ τ) ^ N` tends to `exp (λ T)`
whenever `N τ → T` (`TauCeti.tendsto_one_add_mul_pow_exp`).

## Main declarations

* `TauCeti.one_add_mul_pow_ceil_div_le_exp`: `(1 + aτ) ^ ⌈t / τ⌉₊ ≤ exp (a (t + τ))`.
* `TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub`: the discrete Grönwall bound
  `D n ² ≤ 2τ' (e 0 - A) (1 + 8τ / τ')ⁿ` under coercivity.
* `TauCeti.le_div_mul_exp_of_antitoneOn`: exponential decay of a nonincreasing function which
  drops by a fixed factor over every interval of a fixed length.
* `TauCeti.one_add_mul_pos_of_abs_mul_lt_one`, `TauCeti.eventually_one_add_mul_pos`,
  `TauCeti.exists_pos_one_add_mul_pos`: positivity of `1 + λ τ` for small time steps.
* `TauCeti.tendsto_natCast_sub_ceil_mul`: `(⌈t / τ⌉₊ - ⌈s / τ⌉₊) τ → t - s` as `τ → 0⁺`.
* `TauCeti.tendsto_one_add_mul_pow_exp`: `(1 + λ τ) ^ N → exp (λ T)` when `τ → 0` and `N τ → T`.

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

section StepLimits

open Filter Topology
open scoped NNReal

/-- For a nonnegative time step `τ` with `|lam| * τ < 1`, the Euler factor `1 + lam * τ` is
strictly positive. -/
theorem one_add_mul_pos_of_abs_mul_lt_one {lam τ : ℝ} (hτ : 0 ≤ τ) (h : |lam| * τ < 1) :
    0 < 1 + lam * τ := by
  have habs : -(lam * τ) ≤ |lam| * τ := by
    simpa [abs_mul, abs_of_nonneg hτ] using neg_le_abs (lam * τ)
  linarith

/-- For every `lam : ℝ`, `1 + lam * τ > 0` holds for all `τ : ℝ` sufficiently close to `0`. -/
theorem eventually_one_add_mul_pos (lam : ℝ) : ∀ᶠ τ : ℝ in 𝓝 0, 0 < 1 + lam * τ := by
  have hcont : Continuous (fun τ : ℝ ↦ 1 + lam * τ) := by fun_prop
  exact (hcont.tendsto' 0 1 (by simp)).eventually (lt_mem_nhds zero_lt_one)

/-- For every `lam : ℝ` there exists a positive time step `τ₀ : ℝ≥0` with `1 + lam * τ₀ > 0`. -/
theorem exists_pos_one_add_mul_pos (lam : ℝ) :
    ∃ τ₀ : ℝ≥0, 0 < τ₀ ∧ 0 < 1 + lam * (τ₀ : ℝ) := by
  refine ⟨(2 * (‖lam‖₊ + 1))⁻¹, by positivity,
    one_add_mul_pos_of_abs_mul_lt_one (NNReal.coe_nonneg _) ?_⟩
  rw [NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add, NNReal.coe_one,
    coe_nnNorm, Real.norm_eq_abs, mul_inv_lt_iff₀ (by positivity)]
  linarith [abs_nonneg lam]

/-- For `0 ≤ s ≤ t` and eventually positive time steps `τ j → 0`, the discrete elapsed time
`(⌈t / τ j⌉₊ - ⌈s / τ j⌉₊) * τ j` tends to `t - s`. -/
theorem tendsto_natCast_sub_ceil_mul {ι : Type*} {l : Filter ι} {τ : ι → ℝ}
    (hτ : ∀ᶠ j in l, 0 < τ j) (hτ0 : Tendsto τ l (𝓝 0)) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    Tendsto (fun j ↦ ((⌈t / τ j⌉₊ - ⌈s / τ j⌉₊ : ℕ) : ℝ) * τ j) l (𝓝 (t - s)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub hτ0) (by simpa using tendsto_const_nhds.add hτ0)
    (hτ.mono fun j hτj ↦ ?_) (hτ.mono fun j hτj ↦ ?_)
  · have hle : ⌈s / τ j⌉₊ ≤ ⌈t / τ j⌉₊ :=
      Nat.ceil_mono (div_le_div_of_nonneg_right hst hτj.le)
    have ht_le : t ≤ (⌈t / τ j⌉₊ : ℝ) * τ j := (div_le_iff₀ hτj).1 (Nat.le_ceil _)
    have hs_lt : (⌈s / τ j⌉₊ : ℝ) * τ j < s + τ j := by
      have := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hs hτj.le)) hτj
      linarith [show (s / τ j + 1) * τ j = s + τ j by field_simp]
    linarith [show ((⌈t / τ j⌉₊ - ⌈s / τ j⌉₊ : ℕ) : ℝ) * τ j =
      (⌈t / τ j⌉₊ : ℝ) * τ j - (⌈s / τ j⌉₊ : ℝ) * τ j by rw [Nat.cast_sub hle, sub_mul]]
  · have hlt := (natCast_ceil_div_sub_ceil_div_lt hτj.le hst).le
    rwa [div_add_one hτj.ne', le_div_iff₀ hτj] at hlt

/-- **Euler-step exponential limit.** If `τ j → 0` and `N j * τ j → T` along a filter `l`, then
`(1 + lam * τ j) ^ N j → exp (lam * T)`. -/
theorem tendsto_one_add_mul_pow_exp {ι : Type*} {l : Filter ι} (lam T : ℝ) {τ : ι → ℝ}
    (hτ0 : Tendsto τ l (𝓝 0)) {N : ι → ℕ}
    (hN : Tendsto (fun j ↦ (N j : ℝ) * τ j) l (𝓝 T)) :
    Tendsto (fun j ↦ (1 + lam * τ j) ^ N j) l (𝓝 (Real.exp (lam * T))) := by
  set g : ℝ → ℝ := fun u ↦ if u = 0 then 1 else u⁻¹ * Real.log (1 + u)
  have hg0 : Tendsto g (𝓝 0) (𝓝 1) := by
    have hg0_eq : g 0 = 1 := by simp [g]
    rw [← hg0_eq, ← ContinuousAt, continuousAt_iff_punctured_nhds, hg0_eq]
    have hslope : Tendsto (fun u ↦ u⁻¹ * Real.log (1 + u)) (𝓝[≠] 0) (𝓝 1) := by
      simpa only [Function.comp_def, Real.log_one, sub_zero, smul_eq_mul, inv_one] using
        (Real.hasDerivAt_log one_ne_zero).tendsto_slope_zero
    exact hslope.congr' (eventually_nhdsWithin_of_forall fun u (hu : u ≠ 0) ↦ by simp [g, hu])
  have hu0 : Tendsto (fun j ↦ lam * τ j) l (𝓝 0) := by simpa using hτ0.const_mul lam
  have hprod : Tendsto (fun j ↦ Real.exp (((N j : ℝ) * τ j) * lam * g (lam * τ j))) l
      (𝓝 (Real.exp (lam * T))) := by
    have := (hN.mul_const lam).mul (hg0.comp hu0)
    rw [mul_one, mul_comm T lam] at this
    exact (Real.continuous_exp.tendsto _).comp this
  refine hprod.congr' ?_
  filter_upwards [hτ0.eventually (eventually_one_add_mul_pos lam)] with j hpos
  rcases eq_or_ne (lam * τ j) 0 with h0 | hne
  · have hmul0 : ((N j : ℝ) * τ j) * lam = 0 := by
      linarith [show (N j : ℝ) * (lam * τ j) = ((N j : ℝ) * τ j) * lam by ring,
        congrArg ((N j : ℝ) * ·) h0]
    simp [g, h0, hmul0]
  · have hmul : ((N j : ℝ) * τ j) * lam * ((lam * τ j)⁻¹ * Real.log (1 + lam * τ j)) =
        (N j : ℝ) * (lam * τ j * (lam * τ j)⁻¹) * Real.log (1 + lam * τ j) := by ring
    simp only [g, hne, ↓reduceIte, hmul, mul_inv_cancel₀ hne, mul_one, Real.exp_nat_mul,
      Real.exp_log hpos]

end StepLimits

end TauCeti
