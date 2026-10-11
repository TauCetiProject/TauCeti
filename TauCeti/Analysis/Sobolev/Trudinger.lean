/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.Poincare.Potential
import TauCeti.MeasureTheory.Integral.RieszPotential

/-!
# The borderline Sobolev embedding `p = n` and Trudinger's inequality

Let `E` be a real normed space of dimension `n ≥ 1` with an additive Haar measure `μ`, and let
`ω = μ(B(0, 1))`. In the borderline case `p = n` of the Sobolev embedding, `W^{1,n}_0(Ω)` does not
embed in `L^∞(Ω)` once `n ≥ 2`, but on a set `Ω` of finite measure it embeds in `L^q(Ω)` for every
finite `q`, with the explicit bound

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) (q (1 - 1/n) + 1) ^ (1 - 1/n + 1/q) μ(Ω) ^ (1/q) ‖Du‖_{Lⁿ}`

for every `q ≥ n`. For `n = 1` the constant is bounded in `q`, in line with the embedding of
`W^{1,1}_0` in `L^∞`. For `n ≥ 2` it grows like `q ^ (1 - 1/n)` as `q → ∞`, and summing these
bounds in the exponential series gives **Trudinger's inequality**: `|u| ^ (n / (n - 1))` is
exponentially integrable, with

`∫_Ω exp ((|u| / (c ‖Du‖_{Lⁿ})) ^ (n / (n - 1))) ≤ e (nⁿ + 5) μ(Ω)`,
`c = (2e) ^ (1 - 1/n) n⁻¹ ω ^ (-1/n)`.

So the substitute for the failed embedding in `L^∞` is an embedding in an exponential Orlicz
space.

The proof of the moment bound is that of Gilbarg–Trudinger, Theorem 7.15. A `C¹` function `u`
with compact support in `Ω` is bounded pointwise by the Riesz potential of `‖Du‖` of order one,
`‖u x‖ ≤ (n ω)⁻¹ ∫_Ω ‖Du y‖ ‖x - y‖ ^ (1 - n) dy`
(`TauCeti.enorm_le_lintegral_enorm_fderiv_mul_enorm_sub_rpow`), and that potential maps `Lⁿ(Ω)`
to `L^q(Ω)` with the stated constant (`TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le` with
`κ = 1/n`, `p = n`). The estimate then passes from test functions to their closure
`W^{1,n}_0(Ω)` (`TauCeti.W1p.eLpNorm_value_le_of_forall_testFunction`).

For Trudinger's inequality, the moment bound at `q = n k / (n - 1)`, `k ≥ n - 1`, reads
`∫_Ω (|u| / (c ‖Du‖_{Lⁿ})) ^ (n k / (n - 1)) ≤ (k + 1) ^ (k + 1) (2e) ^ (-k) μ(Ω)`, and
`(k + 1) ^ (k + 1) / k! ≤ (k + 1) e ^ (k + 1)` makes the `k`-th term of the exponential series at
most `e (k + 1) 2 ^ (-k) μ(Ω)`. The finitely many terms with `k < n - 1` are bounded by the term
`k = n - 1`, using `t ^ k ≤ 1 + t ^ (n - 1)`.

## Main declarations

* `TauCeti.eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv`: the bound for compactly supported
  `C¹` functions.
* `TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient`: the bound on
  `W^{1,n}_0(Ω)`.
* `TauCeti.setLIntegral_exp_norm_div_rpow_le`: Trudinger's inequality for compactly supported
  `C¹` functions.
* `TauCeti.W1p.setLIntegral_exp_abs_value_div_rpow_le`: Trudinger's inequality on
  `W^{1,n}_0(Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.15 and its proof.
* N. S. Trudinger, *On imbeddings into Orlicz spaces and some applications*, J. Math. Mech. 17
  (1967), 473–483.
-/

public section

noncomputable section

namespace TauCeti

open Function MeasureTheory Metric Set Module TopologicalSpace
open scoped Distributions ENNReal NNReal Nat

/-! ### From the moment bounds to exponential integrability -/

section Exponential

/-- The exponential series bound behind Trudinger's inequality:
`(k + 1) ^ (k + 1) / (k! (2e) ^ k) ≤ e (k + 1) / 2 ^ k`. -/
private theorem add_one_pow_div_factorial_mul_le (k : ℕ) :
    ((k : ℝ) + 1) ^ (k + 1) / (2 * Real.exp 1) ^ k / k ! ≤
      Real.exp 1 * (((k : ℝ) + 1) * (1 / 2) ^ k) := by
  have h := Real.pow_div_factorial_le_exp (x := ((k + 1 : ℕ) : ℝ)) (by positivity) (k + 1)
  rw [← Real.exp_one_pow, Nat.factorial_succ, Nat.cast_mul, div_le_iff₀ (by positivity)] at h
  push_cast at h
  rw [div_div, div_le_iff₀ (by positivity)]
  calc ((k : ℝ) + 1) ^ (k + 1) ≤ Real.exp 1 ^ (k + 1) * (((k : ℝ) + 1) * k !) := h
    _ = _ := by rw [mul_pow, one_div_pow]; field_simp; ring

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] {ν : Measure X} {f : X → F}
  {n : ℕ} {S : ℝ≥0∞}

/-- The moment exponent `q = n k / (n - 1)` of Trudinger's inequality satisfies
`q (1 - 1/n) = k`. -/
private theorem div_sub_one_mul_mul_one_sub_inv (hn : (1 : ℝ) < n) (k : ℕ) :
    (n : ℝ) / (n - 1) * k * (1 - (n : ℝ)⁻¹) = k := by
  have : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- `((‖y‖ / c) ^ β) ^ k = ‖y‖ ^ (β k) c ^ (-β k)`, in `ℝ≥0∞`. -/
private theorem ofReal_rpow_pow_norm_div (y : F) {c β : ℝ} (hc : 0 < c) (hβ : 0 ≤ β) (k : ℕ) :
    ENNReal.ofReal (((‖y‖ / c) ^ β) ^ k) = ‖y‖ₑ ^ (β * k) * ENNReal.ofReal (c ^ (-(β * k))) := by
  rw [← Real.rpow_mul_natCast (by positivity), Real.div_rpow (norm_nonneg _) hc.le,
    div_eq_mul_inv, ← Real.rpow_neg hc.le, ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity), ofReal_norm]

/-- The constants of the moment bound at `q = r` with `r (1 - 1/n) = k` combine to
`(k + 1) ^ (k + 1) (2e) ^ (-k)`. -/
private theorem add_one_rpow_rpow_mul_rpow_mul_rpow_neg {k : ℕ} {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) (hrk : r * (1 - (n : ℝ)⁻¹) = k) :
    (((k : ℝ) + 1) ^ (1 - (n : ℝ)⁻¹ + r⁻¹)) ^ r * s ^ r *
        ((2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * s) ^ (-r) =
      ((k : ℝ) + 1) ^ (k + 1) / (2 * Real.exp 1) ^ k := by
  have hexp : (1 - (n : ℝ)⁻¹ + r⁻¹) * r = ((k + 1 : ℕ) : ℝ) := by
    push_cast
    rw [add_mul, inv_mul_cancel₀ hr.ne', mul_comm, hrk]
  have hk' : (1 - (n : ℝ)⁻¹) * -r = -(k : ℝ) := by rw [mul_neg, mul_comm, hrk]
  rw [← Real.rpow_mul (by positivity), hexp, Real.rpow_natCast, Real.mul_rpow (by positivity)
    hs.le, ← Real.rpow_mul (by positivity), hk', Real.rpow_neg (by positivity),
    Real.rpow_neg hs.le, Real.rpow_natCast]
  field_simp

/-- `(a b ^ (1/r) s) ^ r t = a ^ r s ^ r t b` in `ℝ≥0∞`, for real `a, s ≥ 0`, real `t` and
`r > 0`. -/
private theorem ofReal_mul_rpow_inv_mul_ofReal_rpow_mul_ofReal {a s r : ℝ} (ha : 0 ≤ a)
    (hs : 0 ≤ s) (hr : 0 < r) (t : ℝ) (b : ℝ≥0∞) :
    (ENNReal.ofReal a * b ^ r⁻¹ * ENNReal.ofReal s) ^ r * ENNReal.ofReal t =
      ENNReal.ofReal (a ^ r * s ^ r * t) * b := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ENNReal.mul_rpow_of_nonneg _ _ hr.le,
    ENNReal.rpow_inv_rpow hr.ne', ENNReal.ofReal_rpow_of_nonneg ha hr.le,
    ENNReal.ofReal_rpow_of_nonneg hs hr.le, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  ring

/-- The moments behind Trudinger's inequality. If `‖f‖_q ≤ (q (1 - 1/n) + 1) ^ (1 - 1/n + 1/q)
ν(X) ^ (1/q) S` for every `q ≥ n`, then for `c = (2e) ^ (1 - 1/n) S` and `k ≥ n - 1`,
`∫ (‖f‖ / c) ^ (n k / (n - 1)) ≤ (k + 1) ^ (k + 1) (2e) ^ (-k) ν(X)`. -/
private theorem lintegral_ofReal_norm_div_rpow_pow_le (hf : AEStronglyMeasurable f ν)
    (hn : 2 ≤ n) (hS : S ≠ ∞)
    (h : ∀ q : ℝ≥0, (n : ℝ≥0) ≤ q → eLpNorm f q ν ≤
      ENNReal.ofReal ((q * (1 - (n : ℝ)⁻¹) + 1) ^ (1 - (n : ℝ)⁻¹ + (q : ℝ)⁻¹)) *
        ν univ ^ (q : ℝ)⁻¹ * S)
    (hc : 0 < (2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * S.toReal) {k : ℕ} (hk : n - 1 ≤ k) :
    ∫⁻ x, ENNReal.ofReal (((‖f x‖ / ((2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * S.toReal)) ^
        ((n : ℝ) / (n - 1))) ^ k) ∂ν ≤
      ENNReal.ofReal (((k : ℝ) + 1) ^ (k + 1) / (2 * Real.exp 1) ^ k) * ν univ := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hk1 : (n : ℝ) - 1 ≤ k := by
    have : ((n - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
  -- The exponent `q = n k / (n - 1) ≥ n`.
  set r : ℝ := (n : ℝ) / (n - 1) * k with hr_def
  have hr : (n : ℝ) ≤ r := by
    rw [hr_def, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  have hr0 : 0 < r := by linarith
  set q : ℝ≥0 := ⟨r, hr0.le⟩
  have hqr : (q : ℝ) = r := rfl
  have hq : (n : ℝ≥0) ≤ q := by rw [← NNReal.coe_le_coe, hqr]; exact_mod_cast hr
  have hq0 : q ≠ 0 := by rw [← NNReal.coe_ne_zero, hqr]; exact hr0.ne'
  have hqk : r * (1 - (n : ℝ)⁻¹) = k := div_sub_one_mul_mul_one_sub_inv hn1 k
  have hβ : 0 ≤ (n : ℝ) / (n - 1) := div_nonneg (by linarith) (by linarith)
  simp_rw [ofReal_rpow_pow_norm_div _ hc hβ, ← hr_def]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ← hqr,
    ← eLpNorm_nnreal_pow_eq_lintegral hq0 hf, hqr]
  have hkey := h q hq
  rw [hqr, hqk] at hkey
  calc eLpNorm f q ν ^ r * ENNReal.ofReal (((2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * S.toReal) ^ (-r))
      ≤ (ENNReal.ofReal (((k : ℝ) + 1) ^ (1 - (n : ℝ)⁻¹ + r⁻¹)) * ν univ ^ r⁻¹ *
          ENNReal.ofReal S.toReal) ^ r *
          ENNReal.ofReal (((2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * S.toReal) ^ (-r)) := by
        rw [ENNReal.ofReal_toReal hS]; gcongr
    _ = _ := by
      rw [ofReal_mul_rpow_inv_mul_ofReal_rpow_mul_ofReal (by positivity) ENNReal.toReal_nonneg
        hr0, add_one_rpow_rpow_mul_rpow_mul_rpow_neg hr0
        (pos_of_mul_pos_right hc (by positivity)) hqk]

/-- The terms of the exponential series in Trudinger's inequality: under the moment bounds,
`(∫ (‖f‖ / c) ^ (n k / (n - 1))) / k! ≤ ((1 + nⁿ) / k! + e (k + 1) / 2ᵏ) ν(X)`. The first term
covers `k < n - 1`, where `t ^ k ≤ 1 + t ^ (n - 1)`, and the second covers `k ≥ n - 1`. -/
private theorem lintegral_ofReal_norm_div_rpow_pow_mul_le (hf : AEStronglyMeasurable f ν)
    (hn : 2 ≤ n) (hS : S ≠ ∞)
    (h : ∀ q : ℝ≥0, (n : ℝ≥0) ≤ q → eLpNorm f q ν ≤
      ENNReal.ofReal ((q * (1 - (n : ℝ)⁻¹) + 1) ^ (1 - (n : ℝ)⁻¹ + (q : ℝ)⁻¹)) *
        ν univ ^ (q : ℝ)⁻¹ * S)
    (hc : 0 < (2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * S.toReal) (k : ℕ) :
    (∫⁻ x, ENNReal.ofReal (((‖f x‖ / ((2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * S.toReal)) ^
        ((n : ℝ) / (n - 1))) ^ k) ∂ν) * ENNReal.ofReal (k ! : ℝ)⁻¹ ≤
      ENNReal.ofReal ((1 + (n : ℝ) ^ n) / k ! + Real.exp 1 * (((k : ℝ) + 1) * (1 / 2) ^ k)) *
        ν univ := by
  set T : X → ℝ := fun x => (‖f x‖ / ((2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * S.toReal)) ^
    ((n : ℝ) / (n - 1))
  have hT0 : ∀ x, 0 ≤ T x := fun x => by positivity
  have hmom {j : ℕ} (hj : n - 1 ≤ j) := lintegral_ofReal_norm_div_rpow_pow_le hf hn hS h hc hj
  rcases le_or_gt (n - 1) k with hk | hk
  · -- `k ≥ n - 1`: the moment bound.
    calc (∫⁻ x, ENNReal.ofReal (T x ^ k) ∂ν) * ENNReal.ofReal (k ! : ℝ)⁻¹
        ≤ ENNReal.ofReal (((k : ℝ) + 1) ^ (k + 1) / (2 * Real.exp 1) ^ k) * ν univ *
            ENNReal.ofReal (k ! : ℝ)⁻¹ := by gcongr; exact hmom hk
      _ = ENNReal.ofReal (((k : ℝ) + 1) ^ (k + 1) / (2 * Real.exp 1) ^ k / k !) * ν univ := by
        rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv _ (k ! : ℝ)]
      _ ≤ _ := by
        gcongr
        exact (add_one_pow_div_factorial_mul_le k).trans (le_add_of_nonneg_left (by positivity))
  · -- `k < n - 1`: compare with the `(n - 1)`-th moment, `t ^ k ≤ 1 + t ^ (n - 1)`.
    have hpt : ∀ x, ENNReal.ofReal (T x ^ k) ≤ 1 + ENNReal.ofReal (T x ^ (n - 1)) := fun x => by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rcases le_total (T x) 1 with h1 | h1
      · exact (pow_le_one₀ (hT0 x) h1).trans (le_add_of_nonneg_right (by positivity))
      · exact (pow_le_pow_right₀ h1 hk.le).trans (le_add_of_nonneg_left zero_le_one)
    have hnn : ((((n - 1 : ℕ) : ℝ) + 1) ^ (n - 1 + 1) / (2 * Real.exp 1) ^ (n - 1)) ≤
        (n : ℝ) ^ n := by
      rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel, Nat.sub_add_cancel (by omega)]
      exact div_le_self (by positivity)
        (one_le_pow₀ (by linarith [Real.add_one_le_exp 1]))
    calc (∫⁻ x, ENNReal.ofReal (T x ^ k) ∂ν) * ENNReal.ofReal (k ! : ℝ)⁻¹
        ≤ (∫⁻ x, (1 + ENNReal.ofReal (T x ^ (n - 1))) ∂ν) * ENNReal.ofReal (k ! : ℝ)⁻¹ := by
          gcongr with x; exact hpt x
      _ ≤ (ν univ + ENNReal.ofReal ((n : ℝ) ^ n) * ν univ) * ENNReal.ofReal (k ! : ℝ)⁻¹ := by
          rw [lintegral_add_left measurable_const, lintegral_one]
          gcongr
          exact (hmom le_rfl).trans (by gcongr)
      _ = ENNReal.ofReal ((1 + (n : ℝ) ^ n) / k !) * ν univ := by
          rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
          ring
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_right (by positivity)

/-- **Trudinger's inequality from its moment bounds.** If `f` satisfies the bounds
`‖f‖_q ≤ (q (1 - 1/n) + 1) ^ (1 - 1/n + 1/q) ν(X) ^ (1/q) S` for every `q ≥ n`, then
`∫ exp ((‖f‖ / c) ^ (n / (n - 1))) ≤ e (nⁿ + 5) ν(X)` with `c = (2e) ^ (1 - 1/n) S`. -/
private theorem lintegral_exp_norm_div_rpow_le_of_eLpNorm_le (hf : AEStronglyMeasurable f ν)
    (hn : 2 ≤ n)
    (h : ∀ q : ℝ≥0, (n : ℝ≥0) ≤ q → eLpNorm f q ν ≤
      ENNReal.ofReal ((q * (1 - (n : ℝ)⁻¹) + 1) ^ (1 - (n : ℝ)⁻¹ + (q : ℝ)⁻¹)) *
        ν univ ^ (q : ℝ)⁻¹ * S) :
    ∫⁻ x, ENNReal.ofReal (Real.exp ((‖f x‖ / ((2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * S.toReal)) ^
        ((n : ℝ) / (n - 1)))) ∂ν ≤
      ENNReal.ofReal (Real.exp 1 * (n ^ n + 5)) * ν univ := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hβ : 0 < (n : ℝ) / (n - 1) := div_pos (by linarith) (by linarith)
  rcases (show 0 ≤ (2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * S.toReal by positivity).eq_or_lt
    with hc | hc
  · -- If `S` is `0` or `∞`, the integrand is `1`.
    simp only [← hc, div_zero, Real.zero_rpow hβ.ne', Real.exp_zero, ENNReal.ofReal_one,
      lintegral_one]
    refine le_mul_of_one_le_left' (ENNReal.one_le_ofReal.2 ?_)
    nlinarith [Real.add_one_le_exp 1, pow_nonneg (n.cast_nonneg (α := ℝ)) n]
  have hS : S ≠ ∞ := fun hS => by simp [hS] at hc
  set T : X → ℝ := fun x => (‖f x‖ / ((2 * Real.exp 1) ^ (1 - (n : ℝ)⁻¹) * S.toReal)) ^
    ((n : ℝ) / (n - 1))
  have hT0 : ∀ x, 0 ≤ T x := fun x => by positivity
  have hTm : AEMeasurable T ν := (hf.norm.aemeasurable.div_const _).pow_const _
  -- Expand the exponential in its power series.
  have hexp : ∀ x, ENNReal.ofReal (Real.exp (T x)) =
      ∑' k : ℕ, ENNReal.ofReal (T x ^ k) * ENNReal.ofReal (k ! : ℝ)⁻¹ := fun x => by
    have hs := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (T x)
    rw [← Real.exp_eq_exp_ℝ] at hs
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs.summable]
    simp_rw [div_eq_mul_inv, ENNReal.ofReal_mul (pow_nonneg (hT0 x) _)]
  -- The bounding series sums to `(1 + nⁿ) e + 4 e`.
  have hsum : HasSum (fun k : ℕ => (1 + (n : ℝ) ^ n) / k ! +
      Real.exp 1 * (((k : ℝ) + 1) * (1 / 2) ^ k)) (Real.exp 1 * (n ^ n + 5)) := by
    have h1 := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (1 : ℝ)).mul_left (1 + (n : ℝ) ^ n)
    have h2 := ((hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1 / 2)
      (by norm_num)).add hasSum_geometric_two).mul_left (Real.exp 1)
    rw [← Real.exp_eq_exp_ℝ] at h1
    convert h1.add h2 using 1
    · ext k
      simp only [one_pow]
      ring
    · norm_num
      ring
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (T x)) ∂ν
      = ∑' k : ℕ, (∫⁻ x, ENNReal.ofReal (T x ^ k) ∂ν) * ENNReal.ofReal (k ! : ℝ)⁻¹ := by
        simp_rw [hexp]
        rw [lintegral_tsum (f := fun k x => ENNReal.ofReal (T x ^ k) * ENNReal.ofReal (k ! : ℝ)⁻¹)
          fun k => (hTm.pow_const k).ennreal_ofReal.mul_const _]
        simp_rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((1 + (n : ℝ) ^ n) / k ! +
          Real.exp 1 * (((k : ℝ) + 1) * (1 / 2) ^ k)) * ν univ :=
        ENNReal.tsum_le_tsum (lintegral_ofReal_norm_div_rpow_pow_mul_le hf hn hS h hc)
    _ = _ := by
        rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          hsum.summable, hsum.tsum_eq]

end Exponential

section CompactSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω : Set E}

/-- **The borderline Sobolev inequality for compactly supported functions.** Let `n` be the
dimension and `ω = μ(B(0, 1))`. If `u` is `C¹` with compact support inside a measurable set `Ω`,
then for every `q ≥ n`,

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) (q (1 - 1/n) + 1) ^ (1 - 1/n + 1/q) μ(Ω) ^ (1/q) ‖Du‖_{Lⁿ}`. -/
theorem eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) (hΩ : MeasurableSet Ω) (hsupp : tsupport u ⊆ Ω) {q : ℝ≥0}
    (hq : (finrank ℝ E : ℝ≥0) ≤ q) :
    eLpNorm u q μ ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
        (q * (1 - (finrank ℝ E : ℝ)⁻¹) + 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹ + (q : ℝ)⁻¹)) *
        μ Ω ^ (q : ℝ)⁻¹ * eLpNorm (fderiv ℝ u) (finrank ℝ E) μ := by
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1)
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast finrank_pos
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne'
    measure_ball_lt_top.ne
  have hq' : (n : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  -- The Riesz potential of order one of `‖Du‖`, over `Ω`.
  set V : E → ℝ≥0∞ := fun x =>
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((n : ℝ) * ((n : ℝ)⁻¹ - 1)) * ‖fderiv ℝ u y‖ₑ ∂μ
  have hcont := hu.continuous_fderiv one_ne_zero
  -- The pointwise potential bound `‖u x‖ ≤ (n ω)⁻¹ V x`.
  have hpt : ∀ x, ‖u x‖ₑ ≤ ENNReal.ofReal ((n * ω)⁻¹) * ‖V x‖ₑ := fun x => by
    refine (enorm_le_lintegral_enorm_fderiv_mul_enorm_sub_rpow (μ := μ) hu h2u x).trans_eq ?_
    rw [enorm_eq_self, ← setLIntegral_eq_of_support_subset (s := Ω)]
    · congr 1
      refine lintegral_congr fun y => ?_
      rw [mul_comm, show (n : ℝ) * ((n : ℝ)⁻¹ - 1) = 1 - n by field_simp]
    · intro y hy
      by_contra hyΩ
      rw [mem_support, fderiv_of_notMem_tsupport ℝ fun h => hyΩ (hsupp h)] at hy
      simp [enorm_eq_nnnorm] at hy
  -- The `Lⁿ`-`L^q` bound for the potential, with `κ = 1/n`, `p = n` and `δ = 1/n - 1/q`.
  have hpot := eLpNorm_setLIntegral_enorm_sub_rpow_mul_le (μ := μ) (p := (n : ℝ≥0)) (q := q)
    (κ := (n : ℝ)⁻¹) (δ := (n : ℝ)⁻¹ - (q : ℝ)⁻¹) (by exact_mod_cast finrank_pos) hq
    (by simp) (by linarith [inv_pos.2 hq0]) (inv_le_one_of_one_le₀ hn) hΩ
    hcont.enorm.aemeasurable
  rw [← eLpNorm_restrict_eq_of_support_subset hu.continuous.aestronglyMeasurable
    ((subset_tsupport _).trans hsupp)]
  calc
    eLpNorm u q (μ.restrict Ω) ≤ ENNReal.ofReal ((n * ω)⁻¹) * eLpNorm V q (μ.restrict Ω) :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _ hu.continuous.aestronglyMeasurable.restrict
        (ae_of_all _ hpt)
    _ ≤ _ := by
      rw [mul_assoc]
      refine (mul_le_mul_right hpot _).trans_eq ?_
      have hbase : (1 - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) / ((n : ℝ)⁻¹ - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) =
          q * (1 - (n : ℝ)⁻¹) + 1 := by
        field_simp [hn0]
        ring
      have hexp : 1 - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) = 1 - (n : ℝ)⁻¹ + (q : ℝ)⁻¹ := by ring
      have hω' : ω ^ (1 - (n : ℝ)⁻¹) = ω * ω ^ (-(n : ℝ)⁻¹) := by
        rw [sub_eq_add_neg, Real.rpow_add hω, Real.rpow_one]
      rw [hbase, hexp, hω', sub_sub_cancel, eLpNorm_enorm _ hcont.aestronglyMeasurable,
        eLpNorm_restrict_eq_of_support_subset hcont.aestronglyMeasurable
          ((support_fderiv_subset ℝ).trans hsupp),
        ENNReal.coe_natCast, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      rw [mul_assoc]
      congr 2
      field_simp

omit [Nontrivial E] in
/-- **Trudinger's inequality for compactly supported functions.** Let `n ≥ 2` be the dimension
and `ω = μ(B(0, 1))`. If `u` is `C¹` with compact support inside a measurable set `Ω`, then

`∫_Ω exp ((‖u‖ / (c ‖Du‖_{Lⁿ})) ^ (n / (n - 1))) ≤ e (nⁿ + 5) μ(Ω)`,

where `c = (2e) ^ (1 - 1/n) n⁻¹ ω ^ (-1/n)`. -/
theorem setLIntegral_exp_norm_div_rpow_le (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    (hΩ : MeasurableSet Ω) (hsupp : tsupport u ⊆ Ω) (hn : 2 ≤ finrank ℝ E) :
    ∫⁻ x in Ω, ENNReal.ofReal (Real.exp ((‖u x‖ /
        ((2 * Real.exp 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) * (finrank ℝ E : ℝ)⁻¹ *
          μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
          (eLpNorm (fderiv ℝ u) (finrank ℝ E) μ).toReal)) ^
        ((finrank ℝ E : ℝ) / (finrank ℝ E - 1)))) ∂μ ≤
      ENNReal.ofReal (Real.exp 1 * (finrank ℝ E ^ finrank ℝ E + 5)) * μ Ω := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set K : ℝ := (finrank ℝ E : ℝ)⁻¹ * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹)
  have hK : 0 ≤ K := by positivity
  have h := lintegral_exp_norm_div_rpow_le_of_eLpNorm_le (ν := μ.restrict Ω)
    (S := ENNReal.ofReal K * eLpNorm (fderiv ℝ u) (finrank ℝ E) μ)
    hu.continuous.aestronglyMeasurable hn fun q hq => by
      rw [eLpNorm_restrict_eq_of_support_subset hu.continuous.aestronglyMeasurable
        ((subset_tsupport _).trans hsupp), Measure.restrict_apply_univ]
      refine (eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv hu h2u hΩ hsupp hq).trans_eq ?_
      rw [ENNReal.ofReal_mul (by positivity)]
      ring
  rw [Measure.restrict_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] at h
  simpa only [K, mul_assoc] using h

end CompactSupport

section W1p0

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The borderline Sobolev inequality on `W^{1,n}_0(Ω)`.** Let `n` be the dimension and
`ω = μ(B(0, 1))`. If `Ω` has finite measure, then every `u ∈ W^{1,n}_0(Ω)` lies in `L^q(Ω)` for
every finite `q ≥ n`, with

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) (q (1 - 1/n) + 1) ^ (1 - 1/n + 1/q) μ(Ω) ^ (1/q) ‖∇u‖_{Lⁿ}`.

No regularity of `Ω` is assumed. -/
theorem W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient (hp : p = finrank ℝ E)
    (hOmega : mu Omega ≠ ∞) {q : ℝ≥0} (hq : (finrank ℝ E : ℝ≥0) ≤ q)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
        (q * (1 - (finrank ℝ E : ℝ)⁻¹) + 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹ + (q : ℝ)⁻¹)) *
        mu Omega ^ (q : ℝ)⁻¹ * ‖W1p.gradient u‖ₑ := by
  have hn : 0 < finrank ℝ E := by
    have h1 : (1 : ℝ≥0∞) ≤ p := Fact.out
    rw [hp] at h1
    exact_mod_cast h1
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hn
  set C : ℝ≥0∞ := ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ *
    mu.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
    (q * (1 - (finrank ℝ E : ℝ)⁻¹) + 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹ + (q : ℝ)⁻¹)) *
    mu Omega ^ (q : ℝ)⁻¹
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hOmega)
  have h := W1p.eLpNorm_value_le_of_forall_testFunction (q := q) (C := C.toNNReal)
    (fun phi => ?_) hu
  · rwa [ENNReal.coe_toNNReal hC] at h
  · rw [ENNReal.coe_toNNReal hC, hp]
    exact eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv (phi.contDiff.of_le (by simp))
      phi.hasCompactSupport Omega.isOpen.measurableSet phi.tsupport_subset hq

/-- **Trudinger's inequality on `W^{1,n}_0(Ω)`.** Let `n ≥ 2` be the dimension and
`ω = μ(B(0, 1))`. Every `u ∈ W^{1,n}_0(Ω)` satisfies

`∫_Ω exp ((|u| / (c ‖∇u‖_{Lⁿ})) ^ (n / (n - 1))) ≤ e (nⁿ + 5) μ(Ω)`,

where `c = (2e) ^ (1 - 1/n) n⁻¹ ω ^ (-1/n)`. So if `μ(Ω) < ∞` and `∇u ≠ 0`, then
`exp (σ |u| ^ (n / (n - 1)))` is integrable on `Ω` for `σ = (c ‖∇u‖_{Lⁿ}) ^ (-n / (n - 1))`,
although `u` need not be bounded. No regularity of `Ω` is assumed. -/
theorem W1p.setLIntegral_exp_abs_value_div_rpow_le (hp : p = finrank ℝ E)
    (hn : 2 ≤ finrank ℝ E) {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    ∫⁻ x in Omega, ENNReal.ofReal (Real.exp ((|W1p.value u x| /
        ((2 * Real.exp 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) * (finrank ℝ E : ℝ)⁻¹ *
          mu.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) * ‖W1p.gradient u‖)) ^
        ((finrank ℝ E : ℝ) / (finrank ℝ E - 1)))) ∂mu ≤
      ENNReal.ofReal (Real.exp 1 * (finrank ℝ E ^ finrank ℝ E + 5)) * mu Omega := by
  rcases eq_or_ne (mu Omega) ∞ with hOmega | hOmega
  · rw [hOmega, ENNReal.mul_top (by positivity)]
    exact le_top
  set K : ℝ := (finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹)
  have hK : 0 ≤ K := by positivity
  have h := lintegral_exp_norm_div_rpow_le_of_eLpNorm_le (ν := mu.restrict Omega)
    (f := (W1p.value u : E → ℝ)) (S := ENNReal.ofReal K * ‖W1p.gradient u‖ₑ)
    (Lp.aestronglyMeasurable _) hn fun q hq => by
      rw [Measure.restrict_apply_univ]
      refine (W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient hp hOmega hq hu).trans_eq ?_
      rw [ENNReal.ofReal_mul (by positivity)]
      ring
  rw [Measure.restrict_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK,
    toReal_enorm] at h
  simpa only [K, Real.norm_eq_abs, mul_assoc] using h

end W1p0

end TauCeti
