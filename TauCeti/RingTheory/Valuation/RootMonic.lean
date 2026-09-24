/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

/-!
# Valuations of roots of monic polynomials

Elementary estimates for a valuation `ν` on a ring: a product of two `ν`-integral
elements that is a `ν`-unit has `ν`-unit factors, and for a monic polynomial `p` with
`ν`-integral coefficients the leading term dominates at any `t` with `1 < ν t`, so that
`ν (p.eval t) = ν t ^ p.natDegree`. Consequently, a root of such a polynomial has value at
most one. These estimates do not require the ring to be commutative or the value monoid to
have inverses.

## Main results

* `Valuation.eq_one_of_mul_eq_one`: if `ν a ≤ 1`, `ν b ≤ 1` and `ν (a * b) = 1`, then `ν a = 1`.
* `Valuation.map_eval_eq_of_one_lt`: `ν (p.eval t) = ν t ^ p.natDegree` for monic `p` with
  `ν`-integral coefficients and `1 < ν t`.
* `Valuation.le_one_of_root_monic`: a root of a monic polynomial with `ν`-integral coefficients
  has value at most one.
* `Valuation.map_quadratic_eq_of_one_lt` and `Valuation.one_lt_map_sq_add_mul_sub_iff`:
  `map_eval_eq_of_one_lt` for the monic quadratic `t² + at + c`, and its consequence that
  `t² + at - c` has a pole exactly where `t` does — the `x`-coordinate `λ² + a₁λ - a₂ - x₁ - x₂`
  of a chord sum, read in its slope `λ`.
* `Valuation.map_cubic_eq_of_one_lt` and `Valuation.le_one_of_root_cubic`: the two statements above
  for the monic cubic `t³ + at² + bt + c`, which is the shape a Weierstrass equation takes.

The cubic bounds apply to the Weierstrass equation: a root of the cubic is integral at every
prime where its coefficients are integral. The companion estimate, for a polynomial expression
in an element that is already integral, is `TauCeti.RingTheory.Valuation.Polynomial`.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, commit `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `Valuation`, together with the cubic specializations
from `EllipticCurves/WeakMordellWeil.lean`, section `Cubic`.
-/

public section

namespace Valuation

open Polynomial

variable {L Γ : Type*} [Ring L] [LinearOrderedCommMonoidWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}

/-- If two elements have value at most one and their product has value one, then the first
element has value one. -/
lemma eq_one_of_mul_eq_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hab : ν (a * b) = 1) :
    ν a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = ν a * ν b := by rw [← map_mul, hab]
    _ ≤ ν a * 1 := by gcongr
    _ = ν a := mul_one _

/-- If `p` is monic with coefficients that are integral for the valuation `ν` and `1 < ν t`,
then the value of `p` at `t` is dominated by the leading term: `ν (p.eval t) = ν t ^ p.natDegree`.
In particular, `p.eval t ≠ 0`. -/
lemma map_eval_eq_of_one_lt {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (ht : 1 < ν t) :
    ν (p.eval t) = ν t ^ p.natDegree := by
  nontriviality Γ
  set n := p.natDegree with hn
  have h0 : ν t ≠ 0 := (zero_lt_one.trans ht).ne'
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hlt : ν (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < ν (t ^ n) := by
    rw [map_pow]
    refine ν.map_sum_lt (pow_ne_zero n h0) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    calc ν (p.coeff i * t ^ i) ≤ 1 * ν t ^ i := by
          rw [map_mul, map_pow]; gcongr; exact hcoeff i hi
      _ = ν t ^ i := one_mul _
      _ < ν t ^ n := pow_lt_pow_right₀ ht hi
  rw [heval, ν.map_add_eq_of_lt_right hlt, map_pow]

/-- A root of a monic polynomial whose coefficients have value at most one also has value
at most one. -/
lemma le_one_of_root_monic {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (heq : p.eval t = 0) :
    ν t ≤ 1 := by
  nontriviality Γ
  by_contra! ht
  have h := ν.map_eval_eq_of_one_lt hp hcoeff ht
  rw [heq, map_zero] at h
  exact (pow_ne_zero _ (zero_lt_one.trans ht).ne') h.symm

section Quadratic

variable {c : L}

/-- A monic quadratic with integral coefficients, evaluated at an element of value `> 1`, is
dominated by its leading term. -/
lemma map_quadratic_eq_of_one_lt (ha : ν a ≤ 1) (hc : ν c ≤ 1) (ht : 1 < ν t) :
    ν (t ^ 2 + a * t + c) = ν t ^ 2 := by
  nontriviality Γ
  have := domain_nontrivial ν ν.map_zero ν.map_one
  have hp : (X ^ 2 + C a * X + C c).Monic := by monicity!
  have hdeg : (X ^ 2 + C a * X + C c).natDegree = 2 := by compute_degree!
  have h := ν.map_eval_eq_of_one_lt hp (fun i hi ↦ by
    rw [hdeg] at hi
    interval_cases i <;> simp [ha, hc]) ht
  rw [hdeg] at h
  simpa [eval_X_pow] using h

/-- **A monic quadratic with integral coefficients has a pole exactly where its variable does**:
`1 < ν (t² + a t - c)` if and only if `1 < ν t`, for `ν a ≤ 1` and `ν c ≤ 1`. -/
lemma one_lt_map_sq_add_mul_sub_iff (ha : ν a ≤ 1) (hc : ν c ≤ 1) :
    1 < ν (t ^ 2 + a * t - c) ↔ 1 < ν t := by
  refine ⟨fun h ↦ ?_, fun ht ↦ ?_⟩
  · by_contra ht
    push Not at ht
    refine h.not_ge (ν.map_sub_le (ν.map_add_le ?_ ?_) hc)
    · rw [map_pow]
      exact pow_le_one₀ zero_le ht
    · rw [map_mul]
      exact mul_le_one' ha ht
  · rw [sub_eq_add_neg, map_quadratic_eq_of_one_lt ν ha (by rwa [Valuation.map_neg]) ht]
    exact lt_of_lt_of_le ht (by simpa using pow_le_pow_right₀ ht.le one_le_two)

end Quadratic

section Cubic

variable {c : L}

-- After the subsingleton value-monoid case is discharged, `ν` supplies the nontriviality
-- of `L` needed to compute the degree and monicity of the cubic.

/-- The non-leading coefficients of `X³ + aX² + bX + c` are `a`, `b`, `c` (and zeros), so they
are integral as soon as `a`, `b`, `c` are. This is the coefficient hypothesis that the general
lemmas above take. -/
private lemma cubic_coeff_le_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1) :
    ∀ i < (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree,
      ν ((X ^ 3 + C a * X ^ 2 + C b * X + C c).coeff i) ≤ 1 := by
  nontriviality Γ
  have := domain_nontrivial ν ν.map_zero ν.map_one
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  intro i hi
  rw [hdeg] at hi
  interval_cases i <;> simp [ha, hb, hc]

/-- A monic cubic with integral coefficients, evaluated at an element of value `> 1`, is
dominated by its leading term. -/
lemma map_cubic_eq_of_one_lt (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1) (ht : 1 < ν t) :
    ν (t ^ 3 + a * t ^ 2 + b * t + c) = ν t ^ 3 := by
  nontriviality Γ
  have := domain_nontrivial ν ν.map_zero ν.map_one
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  have h := ν.map_eval_eq_of_one_lt hp (cubic_coeff_le_one ν ha hb hc) ht
  rw [hdeg] at h
  simpa [eval_X_pow] using h

/-- A root of a monic cubic with integral coefficients is integral. -/
lemma le_one_of_root_cubic (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (heq : t ^ 3 + a * t ^ 2 + b * t + c = 0) :
    ν t ≤ 1 := by
  nontriviality Γ
  have := domain_nontrivial ν ν.map_zero ν.map_one
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  refine ν.le_one_of_root_monic hp (cubic_coeff_le_one ν ha hb hc) ?_
  simpa [eval_X_pow] using heq

end Cubic

end Valuation

end
