/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Exponential

/-!
# The Ingham exponent of a zero-free width

A zero-free width is a function `η` such that an `L`-function has no zeros in the region
`Re s ≥ 1 - η(|Im s| + 3)`. Ingham's transfer theorem turns such a region into the error term
`x exp(-c ω_η(x))` for the coefficient sums of the `L`-function, where

`ω_η(x) = inf_{t ≥ 3} (η(t) log x + log t)`

is the *Ingham exponent* of `η`. The infimum balances the saving `x^{-η(t)}` from moving the
contour to the left edge of the region against the loss `t` from truncating it at height `t`. For
`η(t) = c₀ / log t` it is `2 √(c₀ log x)` once `√(c₀ log x) ≥ log 3`, which gives the classical
error `x exp(-c √(log x))`; for a constant width `η₀` it is `η₀ log x + log 3`.

This file defines `ω_η` with Mathlib's real infimum and proves its basic properties, for `η`
nonnegative on `[3, ∞)` and `x ≥ 1`, where the infimum is bounded below by `log 3`.

## Main definitions

* `TauCeti.inghamExponent η x`: the Ingham exponent `inf_{t ≥ 3} (η(t) log x + log t)`.

## Main results

* `TauCeti.exists_inghamExponent_eq`: for continuous `η` the infimum is attained.
* `TauCeti.monotoneOn_inghamExponent`: the exponent is nondecreasing in `x`.
* `TauCeti.le_inghamExponent`: `c ≤ ω_η(x)` whenever `c ≤ η(t) log x + log t` for every `t ≥ 3`.
* `TauCeti.log_three_le_inghamExponent`, `TauCeti.inghamExponent_le`: the bounds
  `log 3 ≤ ω_η(x) ≤ η(t) log x + log t` for every `t ≥ 3`, in particular for `t = 3`.
* `TauCeti.le_inghamExponent_of_mul_log_rpow_le`: if `η(t) ≥ a₀ (log t)^{-A}` then
  `ω_η(x) ≥ a₀^{1/(1+A)} (log x)^{1/(1+A)}`.
* `TauCeti.exists_log_pow_mul_exp_neg_inghamExponent_le`: if `η(t) ≥ a₀ (log t)^{-A}` with
  `a₀ > 0`, then for every `c > 0` and `n` the product `(log x)^n exp(-c ω_η(x))` is bounded in
  `x ≥ 1`.
* `TauCeti.inghamExponent_mono`: the exponent is monotone in the width `η`.
* `TauCeti.exists_rpow_eq_and_inghamExponent_le`: for continuous nonincreasing `η` and large `x`
  there is a height `T ≥ 3` with `x^{η(T + 3)} = T` and `ω_η(x) ≤ 2 log T + log 2`.

## References

* A. E. Ingham, *The Distribution of Prime Numbers*, Cambridge Tracts 30 (1932), Chapter II.
* D. J. Platt, T. S. Trudgian, *The error term in the prime number theorem*, Math. Comp. 90
  (2021), §1.
* H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 6.
* The choice of height in `TauCeti.exists_rpow_eq_and_inghamExponent_le` follows the lemma
  `GenStrengthPNT` in the formalization
  [PrimeNumberTheoremAnd, revision df0ccba](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/df0ccba486bb86e273ecab565b6ab222c37f8320/PrimeNumberTheoremAnd/MediumPNT.lean),
  file `PrimeNumberTheoremAnd/MediumPNT.lean`.
-/

public section

open Real Set Filter

namespace TauCeti

/-- The **Ingham exponent** `ω_η(x) = inf_{t ≥ 3} (η(t) log x + log t)` of a zero-free width `η`.
It is the real infimum, which is meaningful where the set of values is bounded below: for `η`
nonnegative on `[3, ∞)` and `x ≥ 1` it is at least `log 3`, and it is attained when `η` is
continuous on `[3, ∞)`. -/
noncomputable def inghamExponent (η : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨅ t : Ici (3 : ℝ), (η t * Real.log x + Real.log t)

variable {η : ℝ → ℝ} {x : ℝ}

/-- For `η ≥ 0` and `x ≥ 1`, each value `η(t) log x + log t` with `t ≥ 3` is at least `log t`. -/
private lemma log_le_mul_log_add_log (hη : ∀ t, 3 ≤ t → 0 ≤ η t) (hx : 1 ≤ x) {t : ℝ}
    (ht : 3 ≤ t) : Real.log t ≤ η t * Real.log x + Real.log t :=
  le_add_of_nonneg_left (mul_nonneg (hη t ht) (Real.log_nonneg hx))

private lemma bddBelow_range (hη : ∀ t, 3 ≤ t → 0 ≤ η t) (hx : 1 ≤ x) :
    BddBelow (range fun t : Ici (3 : ℝ) ↦ η t * Real.log x + Real.log t) :=
  ⟨Real.log 3, by
    rintro _ ⟨t, rfl⟩
    exact (Real.log_le_log (by norm_num) t.property).trans
      (log_le_mul_log_add_log hη hx t.property)⟩

/-- **Lower bounds for `ω_η(x)`.** If `c ≤ η(t) log x + log t` for every `t ≥ 3`, then
`c ≤ ω_η(x)`. -/
theorem le_inghamExponent {c : ℝ} (h : ∀ t, 3 ≤ t → c ≤ η t * Real.log x + Real.log t) :
    c ≤ inghamExponent η x :=
  le_ciInf fun t ↦ h t t.property

/-- **`log 3 ≤ ω_η(x)`** for `η` nonnegative on `[3, ∞)` and `x ≥ 1`. -/
theorem log_three_le_inghamExponent (hη : ∀ t, 3 ≤ t → 0 ≤ η t) (hx : 1 ≤ x) :
    Real.log 3 ≤ inghamExponent η x :=
  le_inghamExponent fun _ ht ↦ (Real.log_le_log (by norm_num) ht).trans
    (log_le_mul_log_add_log hη hx ht)

/-- **`ω_η(x) ≤ η(t) log x + log t`** for every `t ≥ 3`, for `η` nonnegative on `[3, ∞)` and
`x ≥ 1`. At `t = 3` this is the upper bound `ω_η(x) ≤ η(3) log x + log 3`. -/
theorem inghamExponent_le (hη : ∀ t, 3 ≤ t → 0 ≤ η t) (hx : 1 ≤ x) {t : ℝ} (ht : 3 ≤ t) :
    inghamExponent η x ≤ η t * Real.log x + Real.log t :=
  ciInf_le (bddBelow_range hη hx) (⟨t, ht⟩ : Ici (3 : ℝ))

/-- **The infimum defining `ω_η(x)` is attained** when `η` is continuous and nonnegative on
`[3, ∞)` and `x ≥ 1`: the function `t ↦ η(t) log x + log t` is continuous and tends to `∞`. -/
theorem exists_inghamExponent_eq (hηc : ContinuousOn η (Ici 3)) (hη : ∀ t, 3 ≤ t → 0 ≤ η t)
    (hx : 1 ≤ x) : ∃ t, 3 ≤ t ∧ inghamExponent η x = η t * Real.log x + Real.log t := by
  set f : ℝ → ℝ := fun t ↦ η t * Real.log x + Real.log t
  have hfc : ContinuousOn f (Ici 3) :=
    (hηc.mul continuousOn_const).add
      (Real.continuousOn_log.mono fun t ht ↦ (by positivity : (0 : ℝ) < 3).trans_le ht |>.ne')
  -- beyond `exp (f 3)`, `f` is at least `log t ≥ f 3`
  have hc : ∀ᶠ t in cocompact ℝ ⊓ 𝓟 (Ici 3), f 3 ≤ f t := by
    rw [eventually_inf_principal, cocompact_eq_atBot_atTop, eventually_sup]
    refine ⟨(eventually_lt_atBot 3).mono fun t ht h3 ↦ absurd h3 (not_le.2 ht), ?_⟩
    filter_upwards [eventually_ge_atTop (Real.exp (f 3))] with t ht h3
    calc f 3 = Real.log (Real.exp (f 3)) := (Real.log_exp _).symm
      _ ≤ Real.log t := Real.log_le_log (Real.exp_pos _) ht
      _ ≤ f t := log_le_mul_log_add_log hη hx h3
  obtain ⟨t, ht, hmin⟩ := hfc.exists_isMinOn' isClosed_Ici self_mem_Ici hc
  exact ⟨t, ht, le_antisymm (inghamExponent_le hη hx ht) (le_inghamExponent fun _ hs ↦ hmin hs)⟩

/-- **`ω_η(x)` is nondecreasing in `x ≥ 1`** for `η` nonnegative on `[3, ∞)`. -/
theorem monotoneOn_inghamExponent (hη : ∀ t, 3 ≤ t → 0 ≤ η t) :
    MonotoneOn (inghamExponent η) (Ici 1) := fun x hx _ _ hxy ↦
  ciInf_mono (bddBelow_range hη hx) fun t ↦ by
    have := hη t t.property
    gcongr
    linarith [mem_Ici.1 hx]

/-- **`ω_η` is monotone in the width**: if `0 ≤ η ≤ η'` on `[3, ∞)` and `x ≥ 1`, then
`ω_η(x) ≤ ω_η'(x)`. -/
theorem inghamExponent_mono {η' : ℝ → ℝ} (hη : ∀ t, 3 ≤ t → 0 ≤ η t)
    (hle : ∀ t, 3 ≤ t → η t ≤ η' t) (hx : 1 ≤ x) :
    inghamExponent η x ≤ inghamExponent η' x :=
  ciInf_mono (bddBelow_range hη hx) fun t ↦ by
    have := Real.log_nonneg hx
    gcongr
    exact hle t t.property

/-- **Lower bound from a lower bound on the width.** If `η(t) ≥ a₀ (log t)^{-A}` on `[3, ∞)`
with `a₀ ≥ 0` and `A ≥ 0`, then `ω_η(x) ≥ a₀^{1/(1+A)} (log x)^{1/(1+A)}` for `x ≥ 1`. For
`η(t) = c₀ / log t` this gives `ω_η(x) ≥ √(c₀ log x)`, half the exact value `2 √(c₀ log x)` that
`ω_η(x)` takes once `√(c₀ log x) ≥ log 3`. -/
theorem le_inghamExponent_of_mul_log_rpow_le {a₀ A : ℝ} (ha₀ : 0 ≤ a₀) (hA : 0 ≤ A)
    (hη : ∀ t, 3 ≤ t → a₀ * Real.log t ^ (-A) ≤ η t) (hx : 1 ≤ x) :
    a₀ ^ (1 / (1 + A)) * Real.log x ^ (1 / (1 + A)) ≤ inghamExponent η x := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [← Real.mul_rpow ha₀ hL]
  set M := (a₀ * Real.log x) ^ (1 / (1 + A))
  refine le_inghamExponent fun t ht ↦ ?_
  have hu : 0 < Real.log t := Real.log_pos (by linarith)
  have hηt : a₀ * Real.log x * Real.log t ^ (-A) ≤ η t * Real.log x := by
    rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right (hη t ht) hL
  have hηt0 : 0 ≤ η t * Real.log x :=
    (by positivity : 0 ≤ a₀ * Real.log x * Real.log t ^ (-A)).trans hηt
  rcases le_or_gt M (Real.log t) with hMu | huM
  · linarith
  -- for `log t < M`, the width term alone is at least `a₀ log x · M^{-A} = M`
  have hM : 0 < M := hu.trans huM
  have hMpow : M ^ (1 + A) = a₀ * Real.log x := by
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith), Real.rpow_one]
  have hMeq : a₀ * Real.log x * M ^ (-A) = M := by
    rw [← hMpow, ← Real.rpow_add hM, add_neg_cancel_right, Real.rpow_one]
  have : M ^ (-A) ≤ Real.log t ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos hu huM.le (neg_nonpos.2 hA)
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ a₀ * Real.log x)]

/-- **Powers of `log x` are absorbed by `exp(-c ω_η(x))`.** If `η(t) ≥ a₀ (log t)^{-A}` on
`[3, ∞)` with `a₀ > 0`, then for every `c > 0` and `n : ℕ` the product `(log x)^n exp(-c ω_η(x))`
is bounded on `x ≥ 1`: the exponent `ω_η(x)` is at least a positive multiple of
`(log x)^{1/(1+A)}` when `A ≥ 0`, and of `log x` when `A < 0`. -/
theorem exists_log_pow_mul_exp_neg_inghamExponent_le {a₀ A c : ℝ} (ha₀ : 0 < a₀) (hc : 0 < c)
    (hη : ∀ t, 3 ≤ t → a₀ * Real.log t ^ (-A) ≤ η t) (n : ℕ) :
    ∃ D, ∀ x, 1 ≤ x → Real.log x ^ n * Real.exp (-c * inghamExponent η x) ≤ D := by
  -- for `A < 0` the width is at least the constant `a₀ (log 3)^{-A}`, the case `A = 0`
  wlog hA : 0 ≤ A generalizing a₀ A
  · refine this (a₀ := a₀ * Real.log 3 ^ (-A)) (A := 0) (by positivity) (fun t ht ↦ ?_) le_rfl
    rw [neg_zero, Real.rpow_zero, mul_one]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (Real.log_le_log (by norm_num) ht) (by linarith)) ha₀.le).trans (hη t ht)
  set m := ⌈(1 + A) * n⌉₊
  set b := c * a₀ ^ (1 / (1 + A))
  have hb : 0 < b := by positivity
  refine ⟨1 + m.factorial / b ^ m, fun x hx ↦ ?_⟩
  have hL := Real.log_nonneg hx
  set y := Real.log x ^ (1 / (1 + A))
  have hy : 0 ≤ y := by positivity
  -- `(log x)^n = y^{(1+A) n} ≤ 1 + y^m`, and `exp(-c ω_η(x)) ≤ exp(-b y)`
  have hLy : Real.log x ^ n ≤ 1 + y ^ m := by
    have h : Real.log x ^ n = y ^ ((1 + A) * n) := by
      have he : 1 / (1 + A) * ((1 + A) * n) = n := by field_simp
      rw [← Real.rpow_mul hL, he, Real.rpow_natCast]
    rw [h]
    rcases le_or_gt y 1 with hy1 | hy1
    · linarith [Real.rpow_le_one hy hy1 (by positivity : 0 ≤ (1 + A) * n), pow_nonneg hy m]
    · rw [← Real.rpow_natCast]
      linarith [Real.rpow_le_rpow_of_exponent_le hy1.le (Nat.le_ceil ((1 + A) * n))]
  have hexp : Real.exp (-c * inghamExponent η x) ≤ Real.exp (-(b * y)) := by
    have := le_inghamExponent_of_mul_log_rpow_le ha₀.le hA hη hx
    rw [Real.exp_le_exp, neg_mul, neg_le_neg_iff, mul_assoc]
    exact mul_le_mul_of_nonneg_left this hc.le
  -- `y^m exp(-b y) ≤ m! / b^m`, from `(b y)^m / m! ≤ exp(b y)`
  have hym : y ^ m * Real.exp (-(b * y)) ≤ m.factorial / b ^ m := by
    have h := Real.pow_div_factorial_le_exp (x := b * y) (by positivity) m
    rw [mul_pow, div_le_iff₀ (by positivity)] at h
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    linarith
  calc Real.log x ^ n * Real.exp (-c * inghamExponent η x)
      ≤ (1 + y ^ m) * Real.exp (-(b * y)) := by gcongr
    _ = Real.exp (-(b * y)) + y ^ m * Real.exp (-(b * y)) := by ring
    _ ≤ 1 + m.factorial / b ^ m := add_le_add (Real.exp_le_one_iff.2 (by nlinarith)) hym


/-- **A height balancing the width against the truncation.** Let `η` be continuous and
nonincreasing on `[3, ∞)`, and let `x ≥ 1` satisfy `log 3 ≤ η(6) log x`. Then there is a height
`T ≥ 3` with `x^{η(T + 3)} = T` and `ω_η(x) ≤ 2 log T + log 2`. Moving a contour to the line
`Re s = 1 - η(T + 3)` then saves the factor `x^{-η(T + 3)} = 1/T`, which is at most
`√2 exp(-ω_η(x)/2)`. -/
theorem exists_rpow_eq_and_inghamExponent_le (hηc : ContinuousOn η (Ici 3))
    (hηa : AntitoneOn η (Ici 3)) (hx : 1 ≤ x) (h6 : Real.log 3 ≤ η 6 * Real.log x) :
    ∃ T, 3 ≤ T ∧ x ^ η (T + 3) = T ∧ inghamExponent η x ≤ 2 * Real.log T + Real.log 2 := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  set f : ℝ → ℝ := fun t ↦ η (t + 3) * Real.log x - Real.log t
  set T₁ := Real.exp (η 6 * Real.log x)
  have hT₁ : 3 ≤ T₁ := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.2 h6
  have hfc : ContinuousOn f (Icc 3 T₁) :=
    ((hηc.comp (continuousOn_id.add continuousOn_const) fun t ht ↦
        mem_Ici.2 (by linarith [ht.1] : 3 ≤ t + 3)).mul continuousOn_const).sub
      (Real.continuousOn_log.mono fun t ht ↦ (by linarith [ht.1] : (0 : ℝ) < t).ne')
  have hf₁ : f T₁ ≤ 0 := by
    have : η (T₁ + 3) ≤ η 6 :=
      hηa (mem_Ici.2 (by norm_num)) (mem_Ici.2 (by linarith)) (by linarith)
    have hfT₁ : f T₁ = (η (T₁ + 3) - η 6) * Real.log x := by
      simp only [f, T₁, Real.log_exp]
      ring
    rw [hfT₁]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hL
  have hf₃ : 0 ≤ f 3 := by
    simp only [f, show (3 : ℝ) + 3 = 6 by norm_num]
    linarith
  obtain ⟨T, hT, hfT⟩ := intermediate_value_Icc' hT₁ hfc ⟨hf₁, hf₃⟩
  have hlog : Real.log T = η (T + 3) * Real.log x := by
    simp only [f] at hfT
    linarith
  have hT0 : 0 < T := by linarith [hT.1]
  refine ⟨T, hT.1, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos (by linarith), mul_comm, ← hlog, Real.exp_log hT0]
  by_cases hb : BddBelow (range fun t : Ici (3 : ℝ) ↦ η t * Real.log x + Real.log t)
  · calc inghamExponent η x ≤ η (T + 3) * Real.log x + Real.log (T + 3) :=
          ciInf_le hb (⟨T + 3, mem_Ici.2 (by linarith)⟩ : Ici (3 : ℝ))
      _ ≤ Real.log T + Real.log (2 * T) := by
          rw [← hlog]
          exact add_le_add le_rfl (Real.log_le_log (by linarith) (by linarith [hT.1]))
      _ = 2 * Real.log T + Real.log 2 := by
          rw [Real.log_mul two_ne_zero hT0.ne']
          ring
  -- an unbounded infimum takes the junk value `0`
  rw [inghamExponent, Real.iInf_of_not_bddBelow hb]
  have := Real.log_nonneg (by linarith [hT.1] : (1 : ℝ) ≤ T)
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  linarith

end TauCeti
