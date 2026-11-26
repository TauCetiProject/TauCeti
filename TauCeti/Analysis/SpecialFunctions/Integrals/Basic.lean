/-
Copyright (c) 2026 The Tau Ceti contributors and Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# Elementary interval integrals

Interval integrals of elementary functions in closed form or as series, continuing Mathlib's
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`.

## Main declarations

* `TauCeti.integral_div_pow`: `∫ s in 0..c, (s / c)^m = c / (m + 1)` for every real `c`.

* `TauCeti.intervalIntegrable_sub_const_rpow`: the weight `(x - c)^r` is interval integrable on
  every interval, for `r > -1`;
* `TauCeti.integral_sub_const_rpow`: `∫ x in a..b, (x - a)^r = (b - a)^(r + 1) / (r + 1)` for
  `r > -1`;
* `TauCeti.intervalIntegrable_sub_rpow`, `TauCeti.integral_sub_rpow`:
  `∫ x in a..b, (b - x)^r = (b - a)^(r + 1) / (r + 1)` for `r > -1`.
* `TauCeti.integral_abs_sub_rpow_of_le`: for `r > -1` and `a ≤ c ≤ b`,
  `∫ x in a..b, |x - c|^r = ((c - a)^(r + 1) + (b - c)^(r + 1)) / (r + 1)`.
* `TauCeti.integral_sub_rpow_le_of_lt_neg_one`: `∫ x in a..b - c, (b - x)^r ≤ c^(r + 1) / -(r + 1)`
  for `r < -1`.
* `TauCeti.integral_const_mul_rpow_le`: `∫ t in δ..1, c * t ^ T ≤ c / (T + 1)` for `T > -1`,
  `c ≥ 0` and `δ ≥ 0`.
* `TauCeti.integral_add_rpow_le_of_lt_neg_one`: `∫ s in 0..β, (r + s) ^ S ≤ r ^ (S + 1) / -(S + 1)`
  for `0 < r`, `0 ≤ β` and `S < -1`.
* `TauCeti.integral_lt_abs_inv_sq`: `∫ t in {t | T < |t|}, (t²)⁻¹ = 2 / T` for `T ≥ 0`.
* `TauCeti.integral_inv_add_abs`: `∫ t in -T..T, (σ + |t|)⁻¹ = 2 log (1 + T / σ)` for `σ > 0` and
  `T ≥ 0`.
* `TauCeti.norm_integral_le_of_ae_norm_le_mul_sub_rpow`: an integral over `[0, t' - h]` of a
  function bounded by `A h (t' - s)^((α - 4)/2)` is at most `2 / (2 - α) A h^(α/2)` for `α < 2`.
* `TauCeti.integrable_one_div_sqrt_one_sub_sq` and `TauCeti.integral_one_div_sqrt_one_sub_sq`:
  `1 / √(1 - x²)` is integrable and `∫ x in a..b, 1 / √(1 - x²) = arcsin b - arcsin a`.
* `TauCeti.integral_pow_add_two_mul_sqrt_one_sub_sq`: the moments
  `Jₙ = ∫ x in -1..1, xⁿ √(1 - x²)` satisfy `(n + 4) Jₙ₊₂ = (n + 1) Jₙ`.
* `TauCeti.integral_exp_mul`: `∫ x in a..b, exp (c x) = (exp (c b) - exp (c a)) / c` for
  `c ≠ 0`, the real counterpart of Mathlib's `integral_exp_mul_complex`.
* `TauCeti.integral_exp_mul_pos`, `TauCeti.integral_exp_mul_le`: the exponential integral
  `E_λ(T) = ∫₀ᵀ e^{λr} dr` is positive for `T > 0` and at most `T e^{|λ|T}`;
  `TauCeti.hasDerivAt_integral_exp_mul_sub`: `z ↦ E_λ(z - t)` has derivative `1` at `t`.
* `TauCeti.integral_inv_mul_one_add_mul`:
  `∫ σ in s..t, 1 / (σ (1 + C σ)) = log (t / (1 + C t)) - log (s / (1 + C s))` for `s, t > 0` and
  `C ≥ 0`.
* `TauCeti.integral_log_pow_div_self`:
  `∫ t in a..b, (log t) ^ k / t = ((log b) ^ (k + 1) - (log a) ^ (k + 1)) / (k + 1)` when
  `0 ∉ [[a, b]]`.
* `TauCeti.integral_cexp_intCast_mul_mul_I`: `∫ θ in -π..π, exp (k θ i)` is `2π` for
  integer `k = 0` and `0` otherwise, the orthogonality of the Fourier characters on `[-π, π]`.
* `TauCeti.norm_integral_cexp_le`, `TauCeti.norm_integral_cexp_le_of_ne_zero`: the integral
  `∫ t in a..b, exp (t u i)` has modulus at most `|b - a|`, and at most `2 / |u|` for `u ≠ 0`.
* `TauCeti.tendsto_average_integral_cexp`: the averages `T⁻¹ ∫ t in 0..T, exp (t u i)` tend to
  `1` at `u = 0` and to `0` elsewhere as `T → ∞`.
* `TauCeti.integral_cos_pow_mul_cexp`: `∫ θ in -π..π, cosᵏ θ exp (n θ i)` in closed form, via the
  binomial expansion `TauCeti.cos_pow_mul_cexp` of `cosᵏ θ exp (n θ i)` into characters.
* `TauCeti.integral_sin_pow_even_eq_ascPochhammer`: the Wallis integral
  `∫ x in 0..π/2, sin²ⁿ x = (π/2) (1/2)ₙ / n!`, with the rising factorial `(1/2)ₙ`.
* `TauCeti.integral_pow_mul_sub`: `∫ x in p..r, xⁿ (x - p)` as a binomial sum in powers of `r - p`.
* `Real.integral_div_sub_sq_add_sq`: the integral of the Poisson kernel `η / ((t - x)² + η²)`
  over an interval is a difference of arctangents.
* `Real.integral_one_div_add_sq`: `∫ t in 0..b, 1 / (a + t)² = a⁻¹ - (a + b)⁻¹` for `a > 0` and
  `b ≥ 0`.
* `Complex.hasSum_integral_exp_mul_cos_mul_cexp`: `∫ θ in -π..π, e^{z cos θ} exp (n θ i)` as the
  sum of the termwise integrals of the exponential series of `e^{z cos θ}`, for complex `z`.
* `Complex.hasSum_pow_div_factorial_integral_exp_mul_cos_mul_cexp`: for integer `n`, the same
  integral as the series `∑ₗ 2π (z / 2) ^ (2 l + |n|) / (l! (l + |n|)!)`.
* `TauCeti.integral_comp_sin_sq_neg`, `TauCeti.integral_comp_sin_sq_add_int_mul_pi`,
  `TauCeti.integral_comp_sin_sq_int_mul_pi`: the integral from `0` of an integrand
  `θ ↦ G (sin² θ)` (with `G` valued in a normed space) is odd and quasi-periodic in its upper
  limit.
-/

public section

open scoped Nat

namespace TauCeti

/-- The normalized integer power integrates to `c / (m + 1)` from zero to `c`,
including a zero or negative endpoint. -/
theorem integral_div_pow (c : ℝ) (m : ℕ) :
    (∫ s in 0..c, (s / c) ^ m) = c / (m + 1 : ℝ) := by
  by_cases hc : c = 0
  · simp [hc]
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero _), sub_zero, pow_succ]
  field_simp [hc]


/-- The weight `(x - c)^r`, singular at `x = c`, is interval integrable between `a` and `b` for
`r > -1`, wherever `c` lies. -/
theorem intervalIntegrable_sub_const_rpow {r : ℝ} (hr : -1 < r) (c a b : ℝ) :
    IntervalIntegrable (fun x => (x - c) ^ r) MeasureTheory.volume a b := by
  simpa using
    (intervalIntegral.intervalIntegrable_rpow' hr (a := a - c) (b := b - c)).comp_sub_right c

/-- `∫ x in a..b, (x - a)^r = (b - a)^(r + 1) / (r + 1)` for `r > -1`. -/
theorem integral_sub_const_rpow {r : ℝ} (hr : -1 < r) (a b : ℝ) :
    ∫ x in a..b, (x - a) ^ r = (b - a) ^ (r + 1) / (r + 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ r), sub_self,
    integral_rpow (Or.inl hr), Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]

/-- The weight `(b - x)^r`, singular at `x = b`, is interval integrable between `a` and `b` for
`r > -1`. -/
theorem intervalIntegrable_sub_rpow {r : ℝ} (hr : -1 < r) (a b : ℝ) :
    IntervalIntegrable (fun x => (b - x) ^ r) MeasureTheory.volume a b := by
  simpa using (intervalIntegral.intervalIntegrable_rpow' hr (a := b - a) (b := 0)).comp_sub_left b

/-- `∫ x in a..b, (b - x)^r = (b - a)^(r + 1) / (r + 1)` for `r > -1`. -/
theorem integral_sub_rpow {r : ℝ} (hr : -1 < r) (a b : ℝ) :
    ∫ x in a..b, (b - x) ^ r = (b - a) ^ (r + 1) / (r + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ r), sub_self,
    integral_rpow (Or.inl hr), Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]

/-- The exact two-sided power integral, allowing the singularity at either endpoint. -/
theorem integral_abs_sub_rpow_of_le {r c a b : ℝ}
    (hr : -1 < r) (ha : a ≤ c) (hb : c ≤ b) :
    (∫ x in a..b, |x - c| ^ r) =
      ((c - a) ^ (r + 1) + (b - c) ^ (r + 1)) / (r + 1) := by
  have hl : Set.EqOn (fun x : ℝ ↦ |x - c| ^ r) (fun x ↦ (c - x) ^ r)
      (Set.uIcc a c) := by
    intro x hx
    dsimp only
    rw [Set.uIcc_of_le ha] at hx
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub]
  have hh : Set.EqOn (fun x : ℝ ↦ |x - c| ^ r) (fun x ↦ (x - c) ^ r)
      (Set.uIcc c b) := by
    intro x hx
    dsimp only
    rw [Set.uIcc_of_le hb] at hx
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
  have hli := (TauCeti.intervalIntegrable_sub_rpow hr a c).congr
    (hl.symm.mono Set.uIoc_subset_uIcc)
  have hri := (TauCeti.intervalIntegrable_sub_const_rpow hr c c b).congr
    (hh.symm.mono Set.uIoc_subset_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals hli hri,
    intervalIntegral.integral_congr hl,
    intervalIntegral.integral_congr hh,
    TauCeti.integral_sub_rpow hr a c, TauCeti.integral_sub_const_rpow hr c b, add_div]

open MeasureTheory Set in
/-- Away from the singularity, the weight `(b - x)^r` with `r < -1` has integral at most
`c^(r + 1) / -(r + 1)` over `[a, b - c]`, uniformly in `a`. (If `a ≥ b`, the pole `x = b` lies in
the interval of integration, the integrand is not integrable and the integral is `0`.) -/
theorem integral_sub_rpow_le_of_lt_neg_one {r a b c : ℝ} (hr : r < -1) (hc : 0 < c) :
    ∫ x in a..b - c, (b - x) ^ r ≤ c ^ (r + 1) / -(r + 1) := by
  have hr₁ : 0 < -(r + 1) := by linarith
  rcases lt_or_ge 0 (b - a) with hba | hba
  · have hval : ∫ x in a..b - c, (b - x) ^ r = (c ^ (r + 1) - (b - a) ^ (r + 1)) / -(r + 1) := by
      rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ r), sub_sub_cancel,
        integral_rpow (Or.inr ⟨by linarith, Set.notMem_uIcc_of_lt hc hba⟩),
        div_neg, ← neg_div, neg_sub]
    rw [hval]
    gcongr
    exact sub_le_self _ (Real.rpow_nonneg hba.le _)
  · -- the pole `x = b` lies in the interval of integration, so the integral is the junk value `0`
    have hnot : ¬ IntervalIntegrable (fun x => (b - x) ^ r) volume a (b - c) := by
      intro h
      have h1 := (h.comp_sub_left b)
      simp only [sub_sub_cancel] at h1
      have h2 : IntervalIntegrable (fun x : ℝ => x ^ r) volume 0 c :=
        h1.mono_set (by
          rw [uIcc_of_le hc.le, uIcc_of_le (hba.trans hc.le)]
          exact Icc_subset_Icc hba le_rfl)
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hc.le,
        intervalIntegral.integrableOn_Ioo_rpow_iff hc] at h2
      linarith
    rw [intervalIntegral.integral_undef hnot]
    positivity

/-- For `-1 < T`, a nonnegative constant `c` and `0 ≤ δ`, the integral of `c * t ^ T` over
`[δ, 1]` is at most `c / (T + 1)`. -/
theorem integral_const_mul_rpow_le {T c δ : ℝ} (hT : -1 < T) (hc : 0 ≤ c) (hδ : 0 ≤ δ) :
    (∫ t in δ..1, c * t ^ T) ≤ c / (T + 1) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hT), Real.one_rpow]
  have hδpow : 0 ≤ δ ^ (T + 1) := Real.rpow_nonneg hδ _
  have hT1 : 0 < T + 1 := by linarith
  calc
    c * ((1 - δ ^ (T + 1)) / (T + 1)) ≤ c * (1 / (T + 1)) := by gcongr; linarith
    _ = c / (T + 1) := by rw [mul_one_div]

open MeasureTheory Real Set in
open scoped Interval in
/-- For `α < 2`, a function bounded by `A h (t' - s)^((α - 4)/2)` on `(0, t' - h]` has integral
over `[0, t' - h]` of norm at most `2 / (2 - α) A h^(α/2)`. This is the time integration, away from
the singular endpoint, behind temporal Hölder estimates with time step `h`. -/
theorem norm_integral_le_of_ae_norm_le_mul_sub_rpow {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : ℝ → G} {A h t' α : ℝ} (hh : 0 < h) (hht : h < t')
    (hα : α < 2) (hg : ∀ᵐ s, s ∈ Ioc 0 (t' - h) → ‖g s‖ ≤ A * h * (t' - s) ^ ((α - 4) / 2)) :
    ‖∫ s in 0..t' - h, g s‖ ≤ 2 / (2 - α) * A * h ^ (α / 2) := by
  have hA : 0 ≤ A := by
    by_contra hA
    have hnull : volume (Ioc 0 (t' - h)) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hg] with s hs hmem
      have hpos : 0 < (t' - s) ^ ((α - 4) / 2) := rpow_pos_of_pos (by linarith [hmem.2]) _
      have := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (lt_of_not_ge hA) hh) hpos
      linarith [norm_nonneg (g s), hs hmem]
    simp [Real.volume_Ioc] at hnull
    linarith
  have hcont : ContinuousOn (fun s => (t' - s) ^ ((α - 4) / 2)) [[0, t' - h]] :=
    fun s hs => by
      rw [uIcc_of_le (by linarith)] at hs
      have hst : s < t' := by linarith [hs.2]
      exact ((continuousAt_const.sub continuousAt_id).rpow_const
        (Or.inl (sub_pos.2 hst).ne')).continuousWithinAt
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith) hg
    (hcont.intervalIntegrable.const_mul (A * h))).trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hpow : h * h ^ ((α - 4) / 2 + 1) = h ^ (α / 2) := by
    rw [mul_comm, ← rpow_add_one hh.ne']
    congr 1
    ring
  calc A * h * ∫ s in 0..t' - h, (t' - s) ^ ((α - 4) / 2)
      ≤ A * h * (h ^ ((α - 4) / 2 + 1) / -((α - 4) / 2 + 1)) := by
        gcongr
        exact integral_sub_rpow_le_of_lt_neg_one (by linarith) hh
    _ = 2 / (2 - α) * A * h ^ (α / 2) := by
        rw [← hpow, show -((α - 4) / 2 + 1) = (2 - α) / 2 by ring]
        field_simp

open MeasureTheory Set in
/-- The function `1 / √(1 - x²)`, extended by `0` outside `(-1, 1)` as usual, is integrable on `ℝ`:
it is the derivative of the monotone function `arcsin` on `(-1, 1)`. -/
theorem integrable_one_div_sqrt_one_sub_sq :
    Integrable (fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2)) := by
  have hint : IntegrableOn (fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2)) (Ioc (-1) 1) := by
    simpa [one_div] using (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  refine hint.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  have hx' : 1 - x ^ 2 ≤ 0 := by
    by_contra h
    push Not at h
    exact hx ⟨by nlinarith, by nlinarith⟩
  rw [Real.sqrt_eq_zero_of_nonpos hx']
  simp

open MeasureTheory Set intervalIntegral in
/-- The integral of `1 / √(1 - x²)` is `arcsin`, between any two points (outside `(-1, 1)` the
integrand is `0` and `arcsin` is constant). -/
theorem integral_one_div_sqrt_one_sub_sq {a b : ℝ} :
    ∫ x in a..b, 1 / Real.sqrt (1 - x ^ 2) = Real.arcsin b - Real.arcsin a := by
  refine integral_eq_of_hasDerivAt_off_countable _ _ (s := {-1, 1}) (by simp)
    Real.continuous_arcsin.continuousOn (fun x hx => ?_)
    integrable_one_div_sqrt_one_sub_sq.intervalIntegrable
  have h1 : x ≠ -1 := fun h => hx.2 (by simp [h])
  have h2 : x ≠ 1 := fun h => hx.2 (by simp [h])
  simpa [one_div] using Real.hasDerivAt_arcsin h1 h2

open MeasureTheory Real Set intervalIntegral in
/-- Integration by parts against `(1 - x ^ 2) ^ (3 / 2)`: the moments
`Jₙ = ∫ x in -1..1, x ^ n * √(1 - x ^ 2)` of the semicircle height satisfy
`(n + 4) Jₙ₊₂ = (n + 1) Jₙ`. -/
theorem integral_pow_add_two_mul_sqrt_one_sub_sq (n : ℕ) :
    (n + 4 : ℝ) * ∫ x in -1..1, x ^ (n + 2) * √(1 - x ^ 2) =
      (n + 1) * ∫ x in -1..1, x ^ n * √(1 - x ^ 2) := by
  have hu (x : ℝ) (_ : x ∈ uIcc (-1 : ℝ) 1) :
      HasDerivAt (fun y : ℝ ↦ y ^ (n + 1)) ((n + 1 : ℝ) * x ^ n) x := by
    simpa using hasDerivAt_pow (n + 1) x
  have hv (x : ℝ) (_ : x ∈ uIcc (-1 : ℝ) 1) :
      HasDerivAt (fun y : ℝ ↦ (1 - y ^ 2) ^ (3 / 2 : ℝ)) (-3 * x * √(1 - x ^ 2)) x := by
    convert ((hasDerivAt_pow 2 x).const_sub 1).rpow_const (p := 3 / 2)
      (Or.inr (by norm_num)) using 1
    have hexp : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
    rw [sqrt_eq_rpow, hexp]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv
    ((by fun_prop : Continuous fun x : ℝ ↦ (n + 1 : ℝ) * x ^ n).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ ↦ -3 * x * √(1 - x ^ 2)).intervalIntegrable _ _)
  have hlhs : ∫ x in -1..1, x ^ (n + 1) * (-3 * x * √(1 - x ^ 2)) =
      -3 * ∫ x in -1..1, x ^ (n + 2) * √(1 - x ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ ↦ by ring
  have hrhs : ∫ x in -1..1, (n + 1 : ℝ) * x ^ n * (1 - x ^ 2) ^ (3 / 2 : ℝ) =
      (n + 1) * ((∫ x in -1..1, x ^ n * √(1 - x ^ 2)) -
        ∫ x in -1..1, x ^ (n + 2) * √(1 - x ^ 2)) := by
    have hint (k : ℕ) : IntervalIntegrable (fun x : ℝ ↦ x ^ k * √(1 - x ^ 2)) volume (-1) 1 :=
      (by fun_prop : Continuous fun x : ℝ ↦ x ^ k * √(1 - x ^ 2)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub (hint n) (hint (n + 2)),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    have h0 : 0 ≤ 1 - x ^ 2 := by
      rw [uIcc_of_le (by norm_num), mem_Icc] at hx
      nlinarith [hx.1, hx.2]
    have hexp : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [hexp, rpow_add' h0 (by norm_num), rpow_one, ← sqrt_eq_rpow]
    ring
  -- The boundary terms vanish because `(1 - x ^ 2) ^ (3 / 2)` is zero at `x = ±1`.
  rw [hlhs, hrhs] at hibp
  norm_num at hibp
  linarith

/-- The integral of `x ↦ exp (c x)` for a nonzero real `c`: an antiderivative is
`x ↦ exp (c x) / c`. The real counterpart of `integral_exp_mul_complex`. -/
theorem integral_exp_mul {a b c : ℝ} (hc : c ≠ 0) :
    ∫ x in a..b, Real.exp (c * x) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.exp) hc, integral_exp, smul_eq_mul,
    inv_mul_eq_div]

/-- The function `E_λ(T) = ∫₀ᵀ e^{λr} dr` is positive for `T > 0`. -/
theorem integral_exp_mul_pos (lam : ℝ) {T : ℝ} (hT : 0 < T) :
    0 < ∫ r in 0..T, Real.exp (lam * r) :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun r ↦ Real.exp (lam * r)).intervalIntegrable _ _)
    (fun _ _ ↦ Real.exp_pos _) hT

/-- The map `z ↦ ∫ r in 0..(z - t), exp (lam * r)` has derivative `1` at `t`. -/
theorem hasDerivAt_integral_exp_mul_sub (lam t : ℝ) :
    HasDerivAt (fun z ↦ ∫ r in 0..(z - t), Real.exp (lam * r)) 1 t := by
  simpa using ((by fun_prop : Continuous fun r ↦ Real.exp (lam * r)).integral_hasStrictDerivAt
    0 (t - t)).hasDerivAt.comp_sub_const t t

/-- The function `E_λ(T) = ∫₀ᵀ e^{λr} dr` satisfies `E_λ(T) ≤ T e^{|λ|T}`. -/
theorem integral_exp_mul_le (lam T : ℝ) :
    ∫ r in 0..T, Real.exp (lam * r) ≤ T * Real.exp (|lam| * T) := by
  have hc : Continuous fun r ↦ Real.exp (lam * r) := by fun_prop
  rcases le_total 0 T with hT | hT
  · have := intervalIntegral.integral_mono_on (g := fun _ ↦ Real.exp (|lam| * T)) hT
      (hc.intervalIntegrable _ _) (intervalIntegrable_const (μ := MeasureTheory.volume))
      fun r hr ↦ Real.exp_le_exp.2 <| by
        nlinarith [le_abs_self lam, abs_nonneg lam, hr.1, hr.2]
    simpa using this
  · rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_mono_on (f := fun _ ↦ Real.exp (|lam| * T)) hT
      (intervalIntegrable_const (μ := MeasureTheory.volume)) (hc.intervalIntegrable _ _)
      fun r hr ↦ Real.exp_le_exp.2 <| by
        nlinarith [le_abs_self lam, abs_nonneg lam, hr.1, hr.2]
    simp only [intervalIntegral.integral_const, smul_eq_mul, zero_sub] at this
    linarith

/-- The integral of `σ ↦ 1 / (σ (1 + C σ))` between positive limits, for `C ≥ 0`: an
antiderivative is `σ ↦ log (σ / (1 + C σ))`. -/
theorem integral_inv_mul_one_add_mul {s t C : ℝ} (hs : 0 < s) (ht : 0 < t) (hC : 0 ≤ C) :
    ∫ σ in s..t, (σ * (1 + C * σ))⁻¹ =
      Real.log (t / (1 + C * t)) - Real.log (s / (1 + C * s)) := by
  have hpos (σ : ℝ) (hσ : σ ∈ Set.uIcc s t) : 0 < σ := (lt_min hs ht).trans_le hσ.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro σ hσ
    have h1 := hpos σ hσ
    have h2 : 0 < 1 + C * σ := by positivity
    have := ((hasDerivAt_id' σ).div (((hasDerivAt_id' σ).const_mul C).const_add 1) h2.ne').log
      (div_ne_zero h1.ne' h2.ne')
    exact this.congr_deriv (by simp only [Pi.div_apply]; field_simp; ring)
  · refine ContinuousOn.intervalIntegrable (ContinuousOn.inv₀ (by fun_prop) fun σ hσ => ?_)
    have := hpos σ hσ
    positivity

/-- When the interval `[[a, b]]` avoids `0`, the interval integral
`∫ t in a..b, (log t) ^ k / t` evaluates to `((log b) ^ (k + 1) - (log a) ^ (k + 1)) / (k + 1)`. -/
theorem integral_log_pow_div_self (k : ℕ) {a b : ℝ} (h : (0 : ℝ) ∉ Set.uIcc a b) :
    ∫ t : ℝ in a..b, Real.log t ^ k / t =
      (Real.log b ^ (k + 1) - Real.log a ^ (k + 1)) / (k + 1 : ℝ) := by
  have hne (t : ℝ) (ht : t ∈ Set.uIcc a b) : t ≠ 0 := fun ht0 ↦ h (ht0 ▸ ht)
  simpa [div_eq_mul_inv] using
    (intervalIntegral.integral_comp_mul_deriv (f := Real.log) (f' := fun t ↦ t⁻¹)
      (g := fun u ↦ u ^ k) (fun t ht ↦ Real.hasDerivAt_log (hne t ht))
      (continuousOn_inv₀.mono fun t ht ↦ hne t ht) (continuous_pow k)).trans
      (integral_pow (a := Real.log a) (b := Real.log b) k)

/-- The integral of the Fourier character `θ ↦ exp (k θ i)` over `[-π, π]`, for an integer `k`: it
is `2π` when `k = 0`, and vanishes otherwise because `exp (k θ i)` has period `2π`. -/
theorem integral_cexp_intCast_mul_mul_I (k : ℤ) :
    ∫ θ in -Real.pi..Real.pi, Complex.exp (k * θ * Complex.I) =
      if k = 0 then 2 * (Real.pi : ℂ) else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [Int.cast_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      sub_neg_eq_add, Complex.real_smul, mul_one, ↓reduceIte]
    push_cast
    ring
  · have hc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hk) Complex.I_ne_zero
    have hper : Complex.exp (k * Complex.I * Real.pi) =
        Complex.exp (k * Complex.I * ((-Real.pi : ℝ) : ℂ)) :=
      Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, by push_cast; ring⟩
    simp_rw [mul_right_comm _ _ Complex.I]
    rw [integral_exp_mul_complex hc, ite_eq_right hk, hper, sub_self, zero_div]

/-- The interval integral `∫ t in a..b, exp (t u i)` has modulus at most `|b - a|`. -/
theorem norm_integral_cexp_le (u a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (↑(t * u) * Complex.I)‖ ≤ |b - a| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (f := fun t ↦ Complex.exp (↑(t * u) * Complex.I))
    fun t _ ↦ (Complex.norm_exp_ofReal_mul_I _).le
  rwa [one_mul] at h

/-- For `u ≠ 0` the interval integral `∫ t in a..b, exp (t u i)` has modulus at most `2 / |u|`,
uniformly in `a` and `b`. -/
theorem norm_integral_cexp_le_of_ne_zero {u : ℝ} (hu : u ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (↑(t * u) * Complex.I)‖ ≤ 2 / |u| := by
  have hc : (u : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hu) Complex.I_ne_zero
  have h : ∫ t in a..b, Complex.exp (↑(t * u) * Complex.I) =
      (Complex.exp (↑(b * u) * Complex.I) - Complex.exp (↑(a * u) * Complex.I)) /
        (u * Complex.I) := by
    simp_rw [show ∀ t : ℝ, (↑(t * u) : ℂ) * Complex.I = u * Complex.I * t from fun t ↦ by
      push_cast; ring]
    rw [integral_exp_mul_complex hc]
  rw [h, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  exact (norm_sub_le _ _).trans (by simp_rw [Complex.norm_exp_ofReal_mul_I]; norm_num)

open Filter Topology in
/-- The averages `T⁻¹ ∫ t in 0..T, exp (t u i)` tend to `1` at `u = 0` and to `0` elsewhere as
`T → ∞`. -/
theorem tendsto_average_integral_cexp (u : ℝ) :
    Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, Complex.exp (↑(t * u) * Complex.I))
      atTop (𝓝 (({0} : Set ℝ).indicator 1 u)) := by
  rcases eq_or_ne u 0 with rfl | hu
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with T hT
    simp [hT]
  · rw [Set.indicator_of_notMem (by simpa using hu)]
    refine squeeze_zero_norm' ?_ ((tendsto_inv_atTop_zero.const_mul (2 / |u|)).trans
      (by rw [mul_zero]))
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hT.le, mul_comm]
    gcongr
    exact norm_integral_cexp_le_of_ne_zero hu 0 T

/-- The binomial expansion of `cosᵏ θ exp (n θ i)` into the Fourier characters
`exp ((2m - k + n) θ i)`. -/
theorem cos_pow_mul_cexp (k : ℕ) (n : ℤ) (θ : ℝ) :
    (Real.cos θ : ℂ) ^ k * Complex.exp (n * θ * Complex.I) =
      ∑ m ∈ Finset.range (k + 1), (1 / 2 : ℂ) ^ k * k.choose m *
        Complex.exp (((2 * m - k + n : ℤ) : ℂ) * θ * Complex.I) := by
  have hcos : (Real.cos θ : ℂ) =
      (1 / 2) * (Complex.exp (θ * Complex.I) + Complex.exp (-θ * Complex.I)) := by
    rw [Complex.ofReal_cos, ← Complex.two_cos]
    ring
  rw [hcos, mul_pow, add_pow, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [← Complex.exp_natCast_mul, ← Complex.exp_natCast_mul]
  calc (1 / 2 : ℂ) ^ k * (Complex.exp (m * (θ * Complex.I)) *
        Complex.exp ((k - m : ℕ) * (-θ * Complex.I)) * k.choose m) *
        Complex.exp (n * θ * Complex.I)
      = (1 / 2 : ℂ) ^ k * k.choose m * Complex.exp (m * (θ * Complex.I) +
          (k - m : ℕ) * (-θ * Complex.I) + n * θ * Complex.I) := by
        rw [Complex.exp_add, Complex.exp_add]
        ring
    _ = _ := by
        congr 3
        push_cast [hmk]
        ring

/-- The integral `∫ θ in -π..π, cosᵏ θ exp (n θ i)`, which is `2π` times the `n`-th Fourier
coefficient of the even function `cosᵏ`, read off the binomial expansion `cos_pow_mul_cexp` by
orthogonality of the characters. -/
theorem integral_cos_pow_mul_cexp (k : ℕ) (n : ℤ) :
    ∫ θ in -Real.pi..Real.pi, (Real.cos θ : ℂ) ^ k * Complex.exp (n * θ * Complex.I) =
      ∑ m ∈ Finset.range (k + 1),
        (1 / 2 : ℂ) ^ k * k.choose m * if 2 * m - k + n = 0 then 2 * (Real.pi : ℂ) else 0 := by
  simp_rw [cos_pow_mul_cexp]
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (by fun_prop : Continuous fun θ : ℝ => (1 / 2 : ℂ) ^ k * k.choose m *
      Complex.exp (((2 * m - k + n : ℤ) : ℂ) * θ * Complex.I)).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_cexp_intCast_mul_mul_I]

/-- The Wallis integral over a quarter period: `∫ x in 0..π/2, sin²ⁿ x = (π/2) (1/2)ₙ / n!`, where
`(1/2)ₙ = (1/2)(3/2)⋯(n - 1/2)` is the rising factorial. This is the form in which it enters
hypergeometric series. -/
theorem integral_sin_pow_even_eq_ascPochhammer (n : ℕ) :
    ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ (2 * n) =
      Real.pi / 2 * ((ascPochhammer ℝ n).eval (1 / 2) / n !) := by
  have hprod : ∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * i + 2) =
      (ascPochhammer ℝ n).eval (1 / 2) / n ! := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ih, ascPochhammer_succ_eval, Nat.factorial_succ]
      push_cast
      field_simp
      ring
  -- the substitution `x ↦ π - x` shows that both halves of `[0, π]` contribute equally
  have hsymm : ∫ x in Real.pi / 2..Real.pi, Real.sin x ^ (2 * n) =
      ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ (2 * n) := by
    have := intervalIntegral.integral_comp_sub_left (fun x => Real.sin x ^ (2 * n)) Real.pi
      (a := 0) (b := Real.pi / 2)
    simp only [Real.sin_pi_sub, sub_zero] at this
    rw [this]
    ring_nf
  have hint (u v : ℝ) :
      IntervalIntegrable (fun x => Real.sin x ^ (2 * n)) MeasureTheory.volume u v :=
    (Real.continuous_sin.pow _).intervalIntegrable u v
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hint 0 (Real.pi / 2))
    (hint (Real.pi / 2) Real.pi)
  rw [hsymm, integral_sin_pow_even, hprod] at hadd
  linarith

/-- The integral of `x ^ n` against the linear weight `x - p` vanishing at `p`, over `[p, r]`, as
a binomial sum. -/
theorem integral_pow_mul_sub (p r : ℝ) (n : ℕ) :
    ∫ x in p..r, x ^ n * (x - p) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) / (k + 2) * p ^ (n - k) * (r - p) ^ (k + 2) := by
  have hexp (x : ℝ) : x ^ n * (x - p) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * p ^ (n - k) * (x - p) ^ (k + 1) := by
    conv_lhs => rw [show x = (x - p) + p by ring, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum fun k _ ↦
    Continuous.intervalIntegrable (by fun_prop) _ _]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x ↦ x ^ (k + 1)), integral_pow, sub_self,
    zero_pow (Nat.succ_ne_zero _)]
  push_cast
  field_simp
  ring

/-! ### Integrands depending only on `sin² θ`

A function of the form `θ ↦ G (sin θ ^ 2)` is even and `π`-periodic, which gives oddness and
quasi-periodicity of its integral from `0`. -/

/-- The integral from `0` of an integrand depending only on `sin² θ` is odd in its upper limit. -/
theorem integral_comp_sin_sq_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : ℝ → E)
    (x : ℝ) :
    ∫ θ in (0 : ℝ)..-x, G (Real.sin θ ^ 2) = -∫ θ in (0 : ℝ)..x, G (Real.sin θ ^ 2) :=
  intervalIntegral.integral_zero_neg_of_even (g := fun θ ↦ G (Real.sin θ ^ 2))
    (fun θ ↦ by simp only [Real.sin_neg, neg_sq]) x

open MeasureTheory in
/-- **Quasi-periodicity** of the integral from `0` of an integrand depending only on
`sin² θ`: adding `n` half-turns to the upper limit adds `2 n` times the integral over
`[0, π/2]`. -/
theorem integral_comp_sin_sq_add_int_mul_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → E)
    (hG : IntervalIntegrable (fun θ ↦ G (Real.sin θ ^ 2)) volume 0 (Real.pi / 2)) (x : ℝ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..x + n * Real.pi, G (Real.sin θ ^ 2) =
      (∫ θ in (0 : ℝ)..x, G (Real.sin θ ^ 2)) +
        (2 * (n : ℝ)) • ∫ θ in (0 : ℝ)..Real.pi / 2, G (Real.sin θ ^ 2) :=
  Function.Periodic.intervalIntegral_add_int_mul_eq_add_of_even
    (f := fun θ ↦ G (Real.sin θ ^ 2))
    (fun θ ↦ by simp only [Real.sin_add_pi, neg_sq])
    (fun θ ↦ by simp only [Real.sin_neg, neg_sq]) hG 0 x n

/-- The integral from `0` to `n π` of an integrand depending only on `sin² θ` is `2 n` times its
integral over `[0, π/2]`, without any integrability assumption. -/
theorem integral_comp_sin_sq_int_mul_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → E) (n : ℤ) :
    ∫ θ in (0 : ℝ)..n * Real.pi, G (Real.sin θ ^ 2) =
      (2 * (n : ℝ)) • ∫ θ in (0 : ℝ)..Real.pi / 2, G (Real.sin θ ^ 2) := by
  simpa only [zero_add] using Function.Periodic.intervalIntegral_add_int_mul_eq_of_even
    (f := fun θ ↦ G (Real.sin θ ^ 2)) (fun θ ↦ by simp only [Real.sin_add_pi, neg_sq])
    (fun θ ↦ by simp only [Real.sin_neg, neg_sq]) 0 n

/-- For `S < -1`, the integral of `(r + s) ^ S` over `[0, β]` is at most `r ^ (S + 1) / -(S + 1)`,
uniformly in `β`. -/
theorem integral_add_rpow_le_of_lt_neg_one {r β S : ℝ} (hr : 0 < r) (hS : S < -1) :
    ∫ s in (0 : ℝ)..β, (r + s) ^ S ≤ r ^ (S + 1) / -(S + 1) := by
  have h := integral_sub_rpow_le_of_lt_neg_one (a := 0) (b := r + β) (c := r) hS hr
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ S) (r + β)] at h
  rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => x ^ S) r]
  convert h using 2 <;> ring

open MeasureTheory Set in
/-- The integral of `t⁻²` over the tails `|t| > T` of the real line is `2/T`. At `T = 0` the
integrand is not integrable and both sides are `0`. -/
theorem integral_lt_abs_inv_sq {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in {t : ℝ | T < |t|}, (t ^ 2)⁻¹ = 2 / T := by
  rcases hT.eq_or_lt with rfl | hT
  · rw [div_zero]
    refine integral_undef fun h ↦ ?_
    have hsub : Ioo (0 : ℝ) 1 ⊆ {t : ℝ | 0 < |t|} := fun t ht ↦ abs_pos.mpr ht.1.ne'
    have h' : IntegrableOn (fun t : ℝ ↦ t ^ (-2 : ℝ)) (Ioo 0 1) :=
      (IntegrableOn.mono_set h hsub).congr_fun
        (fun t ht ↦ by rw [Real.rpow_neg ht.1.le, Real.rpow_two]) measurableSet_Ioo
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).1 h'
    norm_num at this
  have hS : MeasurableSet {t : ℝ | T < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hind : ({t : ℝ | T < |t|}.indicator fun t ↦ (t ^ 2)⁻¹) =
      fun t ↦ (Ioi T).indicator (fun u ↦ (u ^ 2)⁻¹) |t| := by
    ext t
    by_cases h : T < |t| <;> simp [indicator, h, sq_abs]
  have hpow : ∫ u in Ioi T, (u ^ 2)⁻¹ = ∫ u in Ioi T, u ^ (-2 : ℝ) :=
    setIntegral_congr_fun measurableSet_Ioi fun u (hu : T < u) ↦ by
      rw [Real.rpow_neg (hT.trans hu).le, Real.rpow_two]
  rw [← integral_indicator hS, hind, integral_comp_abs, setIntegral_indicator measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_right hT.le, hpow, integral_Ioi_rpow_of_lt (by norm_num) hT]
  norm_num [Real.rpow_neg_one]
  ring

open Set in
/-- The integral of `(σ + |t|)⁻¹` over `[-T, T]` is `2 log(1 + T/σ)`. -/
theorem integral_inv_add_abs {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, (σ + |t|)⁻¹ = 2 * Real.log (1 + T / σ) := by
  have hc : Continuous fun t : ℝ ↦ (σ + |t|)⁻¹ :=
    (continuous_const.add continuous_abs).inv₀ fun t ↦
      (add_pos_of_pos_of_nonneg hσ (abs_nonneg t)).ne'
  have hpos : ∫ t in (0 : ℝ)..T, (σ + |t|)⁻¹ = Real.log (1 + T / σ) := by
    rw [intervalIntegral.integral_congr (g := fun t ↦ (σ + t)⁻¹) fun t ht ↦ by
        rw [uIcc_of_le hT] at ht; simp [abs_of_nonneg ht.1],
      intervalIntegral.integral_comp_add_left (fun t ↦ t⁻¹) σ, add_zero,
      integral_inv_of_pos hσ (by linarith)]
    congr 1
    field_simp
  have hneg : ∫ t in (-T)..0, (σ + |t|)⁻¹ = ∫ t in (0 : ℝ)..T, (σ + |t|)⁻¹ := by
    simpa [abs_neg] using
      (intervalIntegral.integral_comp_neg (a := 0) (b := T) fun t ↦ (σ + |t|)⁻¹).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), hneg, hpos]
  ring

end TauCeti

namespace Real

/-- The integral of the Poisson kernel `η / ((t - x)² + η²)` over `[a, b]` is a difference of
arctangents: a translate of Mathlib's `integral_div_sq_add_sq`. For `η = 0` both sides vanish. -/
theorem integral_div_sub_sq_add_sq (a b t η : ℝ) :
    ∫ x in a..b, η / ((t - x) ^ 2 + η ^ 2) = arctan ((b - t) / η) - arctan ((a - t) / η) := by
  simp_rw [← neg_sub _ t, neg_sq, add_comm _ (η ^ 2)]
  rw [intervalIntegral.integral_comp_sub_right (fun x => η / (η ^ 2 + x ^ 2)),
    integral_div_sq_add_sq]

open Set intervalIntegral in
/-- The reciprocal-square kernel has an elementary integral on each nonnegative interval:
`∫ t in 0..b, 1 / (a + t)² = a⁻¹ - (a + b)⁻¹` for `a > 0` and `b ≥ 0`. -/
theorem integral_one_div_add_sq {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∫ t : ℝ in 0..b, 1 / (a + t) ^ 2 = a⁻¹ - (a + b)⁻¹ := by
  have hd (t : ℝ) (ht : t ∈ uIcc 0 b) :
      HasDerivAt (fun u : ℝ ↦ -(a + u)⁻¹) (1 / (a + t) ^ 2) t := by
    rw [uIcc_of_le hb] at ht
    have h := (((hasDerivAt_id t).const_add a).inv
      (by linarith [ht.1] : a + t ≠ 0)).neg
    convert h using 1
    · ext u
      rfl
    · simp [neg_div]
  have hc : ContinuousOn (fun t : ℝ ↦ 1 / (a + t) ^ 2) (Icc 0 b) :=
    continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
      (fun t ht ↦ pow_ne_zero _ (by linarith [ht.1] : a + t ≠ 0))
  simpa [sub_eq_add_neg, add_comm] using integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc hb)

end Real

namespace Complex

/-- Termwise integration of the exponential series `e^{z cos θ} = ∑ₖ zᵏ cosᵏ θ / k!` against the
Fourier character `exp (n θ i)` over `[-π, π]`, for a complex coefficient `z`. -/
theorem hasSum_integral_exp_mul_cos_mul_cexp (z : ℂ) (n : ℤ) :
    HasSum (fun k : ℕ => z ^ k / k ! *
        ∫ θ in -Real.pi..Real.pi, (Real.cos θ : ℂ) ^ k * exp (n * θ * I))
      (∫ θ in -Real.pi..Real.pi, exp (z * Real.cos θ) * exp (n * θ * I)) := by
  simp_rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => ‖z‖ ^ k / k !)
    (fun k => by fun_prop) (fun k => MeasureTheory.ae_of_all _ fun θ _ => ?_)
    (MeasureTheory.ae_of_all _ fun _ _ => Real.summable_pow_div_factorial ‖z‖)
    intervalIntegrable_const (MeasureTheory.ae_of_all _ fun θ _ => ?_)
  · have harg : (n : ℂ) * θ * I = ((n * θ : ℝ) : ℂ) * I := by
      push_cast
      ring
    have hexp : ‖exp (n * θ * I)‖ = 1 := by
      rw [harg, norm_exp_ofReal_mul_I]
    have hcos : ‖(Real.cos θ : ℂ)‖ ≤ 1 := by
      rw [norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one θ
    rw [norm_mul, norm_mul, hexp, mul_one, norm_div, norm_pow, norm_natCast, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hcos)
  · have h := (NormedSpace.expSeries_div_hasSum_exp (z * Real.cos θ)).mul_right
      (exp (n * θ * I))
    rw [← exp_eq_exp_ℂ] at h
    convert h using 2 with k
    ring

/-- The series of `∫ θ in -π..π, e^{z cos θ} exp (n θ i)` for an integer `n` and complex `z`:
it is `∑ₗ 2π (z / 2) ^ (2 l + |n|) / (l! (l + |n|)!)`, which for real `z` is the series of
`2π I_{|n|}(z)`. Of the termwise integrals in `hasSum_integral_exp_mul_cos_mul_cexp`, evaluated by
`TauCeti.integral_cos_pow_mul_cexp`, only those of the exponents `k = 2 l + |n|` survive. -/
theorem hasSum_pow_div_factorial_integral_exp_mul_cos_mul_cexp (z : ℂ) (n : ℤ) :
    HasSum (fun l : ℕ => 2 * Real.pi * ((z / 2) ^ (2 * l + n.natAbs) / (l ! * (l + n.natAbs)!)))
      (∫ θ in -Real.pi..Real.pi, exp (z * Real.cos θ) * exp (n * θ * I)) := by
  wlog hn : 0 ≤ n generalizing n
  · convert this (-n) (by omega) using 1
    · simp only [Int.natAbs_neg]
    · have hcomp := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := Real.pi)
        (fun θ : ℝ => exp (z * Real.cos θ) * exp (((-n : ℤ) : ℂ) * θ * I))
      rw [neg_neg] at hcomp
      rw [← hcomp]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [Real.cos_neg, ofReal_neg, Int.cast_neg, neg_mul, mul_neg, neg_neg]
  lift n to ℕ using hn
  rw [Int.natAbs_natCast]
  have h := hasSum_integral_exp_mul_cos_mul_cexp z n
  simp only [TauCeti.integral_cos_pow_mul_cexp] at h
  rw [Int.cast_natCast] at h
  -- Only the exponents `k = 2 l + n` contribute.
  have hz : ∀ k ∉ Set.range (fun l : ℕ => 2 * l + n),
      z ^ k / k ! * (∑ m ∈ Finset.range (k + 1), (1 / 2 : ℂ) ^ k * k.choose m *
        if 2 * (m : ℤ) - k + n = 0 then 2 * (Real.pi : ℂ) else 0) = 0 := by
    intro k hk
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m _ => ?_)
    rw [ite_eq_right fun hm => hk ⟨m, by dsimp only; omega⟩, mul_zero]
  have hinj : Function.Injective fun l : ℕ => 2 * l + n := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff hz] at h
  -- At `k = 2 l + n` only `m = l` contributes.
  convert h using 1
  ext l
  dsimp only [Function.comp_apply]
  rw [Finset.sum_eq_single l (fun m _ hm => by rw [ite_eq_right (by omega), mul_zero])
    (fun hl => absurd (Finset.mem_range.mpr (by omega)) hl), ite_eq_left (by push_cast; ring)]
  have hfac := Nat.choose_mul_factorial_mul_factorial (by omega : l ≤ 2 * l + n)
  rw [show 2 * l + n - l = l + n by omega] at hfac
  have hc : ((2 * l + n).choose l : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [← hfac, div_pow]
  push_cast
  field_simp
  rw [mul_assoc, ← mul_pow]
  norm_num

end Complex
