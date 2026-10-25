/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.Algebraic.Integral

import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Logarithms of algebraic numbers

A complex number `λ` is a *logarithm of an algebraic number* if `exp λ` is algebraic over `ℚ`.
These numbers form a `ℚ`-subspace `𝓛` of `ℂ`: it is closed under addition because
`exp (λ + μ) = exp λ * exp μ`, and under multiplication by `a / b ∈ ℚ` because
`exp ((a / b) λ) ^ b = (exp λ) ^ a`, and a root of an algebraic number is algebraic.

The space `𝓛` is the common carrier of the statements of transcendence theory about logarithms:
Hermite–Lindemann (every nonzero `λ ∈ 𝓛` is transcendental), Gelfond–Schneider (two elements
of `𝓛` that are linearly independent over `ℚ` are linearly independent over the algebraic
numbers) and Baker's theorem. It contains every logarithm, principal or not, of every nonzero
algebraic number, so it is strictly larger than the image of the algebraic numbers under the
principal branch `Complex.log`; for instance `2πi ∈ 𝓛`, while `Complex.log` takes values with
imaginary part in `(-π, π]`.

## Main definitions

* `TauCeti.algebraicLogs`: the `ℚ`-subspace `𝓛 = {λ ∈ ℂ | exp λ is algebraic over ℚ}`.

## Main results

* `TauCeti.mem_algebraicLogs`: `λ ∈ 𝓛 ↔ IsAlgebraic ℚ (exp λ)`.
* `TauCeti.span_setOf_isAlgebraic_exp_eq`: `𝓛` is the `ℚ`-span of its defining set.
* `TauCeti.mem_algebraicLogs_iff_exists_int`: `λ ∈ 𝓛` if and only if
  `λ = log α + 2πik` for a nonzero algebraic number `α` and an integer `k`.
* `TauCeti.log_mem_algebraicLogs`: the principal logarithm of an algebraic number lies in `𝓛`.
* `TauCeti.intCast_mul_two_pi_I_mem_algebraicLogs`: `2πik ∈ 𝓛` for every integer `k`.
* `TauCeti.conj_mem_algebraicLogs`: `𝓛` is stable under complex conjugation.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §1.1, Theorem 1.4.
* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.3.
-/

public section

open Complex ComplexConjugate

namespace TauCeti

/-- The `ℚ`-subspace `𝓛` of `ℂ` of logarithms of algebraic numbers: the complex numbers `λ`
such that `exp λ` is algebraic over `ℚ`. Every branch of the logarithm of a nonzero algebraic
number lies in `𝓛`, not only the principal one. -/
noncomputable def algebraicLogs : Submodule ℚ ℂ where
  carrier := {l | IsAlgebraic ℚ (exp l)}
  add_mem' {l μ} hl hμ := by
    simpa only [Set.mem_ofPred_eq, exp_add] using IsAlgebraic.mul hl hμ
  zero_mem' := by simpa only [Set.mem_ofPred_eq, exp_zero] using isAlgebraic_one
  smul_mem' q l hl := by
    -- `exp (q • l) ^ q.den = exp (q.num * l)` is algebraic, hence so is `exp (q • l)`.
    refine IsAlgebraic.of_pow q.den_pos ?_
    have h : (q.den : ℂ) * (q • l) = q.num * l := by
      rw [Rat.smul_def, ← mul_assoc]
      congr 1
      exact_mod_cast q.den_mul_eq_num
    rw [← exp_nat_mul, h, exp_int_mul]
    rcases Int.eq_nat_or_neg q.num with ⟨m, hm | hm⟩ <;> rw [hm]
    · simpa using hl.pow m
    · simpa using (hl.pow m).inv

/-- Membership in `𝓛`: `λ ∈ 𝓛` if and only if `exp λ` is algebraic over `ℚ`. -/
@[simp]
theorem mem_algebraicLogs {l : ℂ} : l ∈ algebraicLogs ↔ IsAlgebraic ℚ (exp l) :=
  Iff.rfl

/-- The underlying set of `𝓛` is the set of `λ` such that `exp λ` is algebraic over `ℚ`. -/
theorem coe_algebraicLogs : (algebraicLogs : Set ℂ) = {l | IsAlgebraic ℚ (exp l)} :=
  Set.ext fun _ ↦ mem_algebraicLogs

/-- `𝓛` is the `ℚ`-span of the set of `λ` such that `exp λ` is algebraic over `ℚ`: this set is
already a `ℚ`-subspace. -/
theorem span_setOf_isAlgebraic_exp_eq :
    Submodule.span ℚ {l : ℂ | IsAlgebraic ℚ (exp l)} = algebraicLogs := by
  rw [← coe_algebraicLogs, Submodule.span_eq]

/-- The principal logarithm of an algebraic number lies in `𝓛`. This includes `log 0 = 0`. -/
theorem log_mem_algebraicLogs {α : ℂ} (hα : IsAlgebraic ℚ α) : log α ∈ algebraicLogs := by
  rcases eq_or_ne α 0 with rfl | h0
  · simp
  · rwa [mem_algebraicLogs, exp_log h0]

/-- `2πik ∈ 𝓛` for every integer `k`, since `exp (2πik) = 1`. -/
theorem intCast_mul_two_pi_I_mem_algebraicLogs (k : ℤ) :
    (k : ℂ) * (2 * Real.pi * I) ∈ algebraicLogs := by
  rw [mem_algebraicLogs, exp_int_mul_two_pi_mul_I]
  exact isAlgebraic_one

/-- `πi ∈ 𝓛`, since `exp (πi) = -1`. -/
theorem pi_mul_I_mem_algebraicLogs : (Real.pi : ℂ) * I ∈ algebraicLogs := by
  rw [mem_algebraicLogs, exp_pi_mul_I]
  exact isAlgebraic_one.neg

/-- The elements of `𝓛` are exactly the numbers `log α + 2πik` with `α` a nonzero algebraic
number and `k` an integer: all branches of the logarithms of nonzero algebraic numbers. -/
theorem mem_algebraicLogs_iff_exists_int {l : ℂ} :
    l ∈ algebraicLogs ↔
      ∃ α : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ ∃ k : ℤ, l = log α + k * (2 * Real.pi * I) := by
  refine ⟨fun hl ↦ ⟨exp l, hl, exp_ne_zero l, ?_⟩, ?_⟩
  · rw [← exp_eq_exp_iff_exists_int, exp_log (exp_ne_zero l)]
  · rintro ⟨α, hα, h0, k, rfl⟩
    exact add_mem (log_mem_algebraicLogs hα) (intCast_mul_two_pi_I_mem_algebraicLogs k)

/-- The logarithm `log x` of a real algebraic number lies in `𝓛`; here `Real.log x = log |x|`,
and `Real.log 0 = 0`. In particular `log q ∈ 𝓛` for every rational number `q`. -/
theorem ofReal_log_mem_algebraicLogs {x : ℝ} (hx : IsAlgebraic ℚ x) :
    (Real.log x : ℂ) ∈ algebraicLogs := by
  have habs : IsAlgebraic ℚ |x| := by
    rcases abs_choice x with h | h <;> rw [h]
    exacts [hx, hx.neg]
  rw [← Real.log_abs, ofReal_log (abs_nonneg x)]
  exact log_mem_algebraicLogs (habs.algebraMap (A := ℂ))

/-- `𝓛` is stable under complex conjugation: `exp (conj λ) = conj (exp λ)`, and the complex
conjugate of an algebraic number is algebraic. -/
theorem conj_mem_algebraicLogs {l : ℂ} (hl : l ∈ algebraicLogs) :
    conj l ∈ algebraicLogs := by
  rw [mem_algebraicLogs, exp_conj]
  exact hl.algHom (starRingEnd ℂ).toRatAlgHom

/-- `conj λ ∈ 𝓛` if and only if `λ ∈ 𝓛`. -/
theorem conj_mem_algebraicLogs_iff {l : ℂ} : conj l ∈ algebraicLogs ↔ l ∈ algebraicLogs :=
  ⟨fun h ↦ by simpa using conj_mem_algebraicLogs h, conj_mem_algebraicLogs⟩

example : (0 : ℂ) ∈ algebraicLogs := zero_mem _

/-- `2πi ∈ 𝓛`, but `2πi` is not a value of the principal logarithm, whose imaginary part is at
most `π`: a definition of `𝓛` through `Complex.log` alone would miss it. -/
example : 2 * (Real.pi : ℂ) * I ∈ algebraicLogs ∧ 2 * (Real.pi : ℂ) * I ∉ Set.range log := by
  refine ⟨by simpa using intCast_mul_two_pi_I_mem_algebraicLogs 1, ?_⟩
  rintro ⟨z, hz⟩
  have h := log_im_le_pi z
  have him : (2 * (Real.pi : ℂ) * I).im = 2 * Real.pi := by simp
  rw [hz, him] at h
  linarith [Real.pi_pos]

example : (Real.log 2 : ℂ) ∈ algebraicLogs ∧ (Real.log 2 : ℂ) = log 2 :=
  ⟨by simpa using ofReal_log_mem_algebraicLogs (isAlgebraic_ratCast ℚ (2 : ℚ)),
    by simp⟩

end TauCeti
