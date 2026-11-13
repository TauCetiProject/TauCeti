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
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Finset.Order
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Valuations of roots of monic polynomials

Elementary estimates for a valuation `ν` on a ring: a product of two `ν`-integral
elements that is a `ν`-unit has `ν`-unit factors, and the leading term of a polynomial `p`
dominates its value at `t` as soon as it dominates each lower term, so that
`ν (p.eval t) = ν (leadingCoeff p) * ν t ^ p.natDegree`. For `p` monic with `ν`-integral
coefficients this holds at any `t` with `1 < ν t`, so a root of such a polynomial has value at
most one. These estimates do not require the ring to be commutative or the value monoid to
have inverses. With values in a group with zero, the leading term of a polynomial that need not be
monic dominates at any `t` with `1 ≤ ν t` at which each lower coefficient has value below
`ν (leadingCoeff p) * ν t`, and so, over a division ring, at every `t` of large enough value.
The last estimate, that at a root of a monic cubic with `ν`-integral quadratic and linear
coefficients and unit discriminant the derivative is a unit, is stated over a commutative ring.

## Main results

* `Valuation.eq_one_of_mul_eq_one`: if `ν a ≤ 1`, `ν b ≤ 1` and `ν (a * b) = 1`, then `ν a = 1`.
* `Valuation.map_eval_eq_leadingCoeff_mul_pow`: the leading term of `p` dominates its value at `t`
  when it dominates each lower term.
* `Valuation.map_eval_eq_of_one_lt`: `ν (p.eval t) = ν t ^ p.natDegree` for monic `p` with
  `ν`-integral coefficients and `1 < ν t`.
* `Valuation.map_eval_eq_leadingCoeff_mul_pow_of_one_le` and
  `Valuation.exists_map_eval_eq_leadingCoeff_mul_pow`: the non-monic forms, at `t` with `1 ≤ ν t`
  whose value is large compared with the lower coefficients, and over a division ring at every `t`
  of large enough value.
* `Valuation.le_one_of_root_monic`: a root of a monic polynomial with `ν`-integral coefficients
  has value at most one.
* `Valuation.map_quadratic_eq_of_one_lt` and `Valuation.one_lt_map_sq_add_mul_sub_iff`:
  `map_eval_eq_of_one_lt` for the monic quadratic `t² + at + c`, and its consequence that
  `t² + at - c` has a pole exactly where `t` does — the `x`-coordinate `λ² + a₁λ - a₂ - x₁ - x₂`
  of a chord sum, read in its slope `λ`.
* `Valuation.map_cubic_eq_of_one_lt` and `Valuation.le_one_of_root_cubic`: the two statements above
  for the monic cubic `t³ + at² + bt + c`, which is the shape a Weierstrass equation takes.
* `Valuation.map_cubic_deriv_eq_one`: at a root of a monic cubic `t³ + at² + bt + c` whose
  discriminant has value `1`, and whose coefficients `a`, `b` (but not necessarily `c`) are
  `ν`-integral, the derivative `3t² + 2at + b` has value `1`.

The cubic bounds apply to the Weierstrass equation: a root of the cubic is integral at every
prime where its coefficients are integral. The companion estimate, for a polynomial expression
in an element that is already integral, is `TauCeti.RingTheory.Valuation.Polynomial`.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, commit `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `Valuation`, together with the cubic specializations
from `EllipticCurves/WeakMordellWeil.lean`, section `Cubic`. `map_cubic_deriv_eq_one` follows the
private lemma of that name in the same section at the later revision `3bfe124`, without its
hypothesis `ν c ≤ 1`: here `c` is eliminated with the root equation, and the Bézout identity that
the source takes as a hypothesis is not needed.
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

/-- **The leading term of a polynomial dominates its value when it dominates each lower term**:
if `ν (p.coeff i) * ν t ^ i < ν (leadingCoeff p) * ν t ^ natDegree p` for every
`i < natDegree p`, then `ν (p.eval t) = ν (leadingCoeff p) * ν t ^ natDegree p`. -/
lemma map_eval_eq_leadingCoeff_mul_pow {p : L[X]}
    (hp : ∀ i < p.natDegree, ν (p.coeff i) * ν t ^ i < ν p.leadingCoeff * ν t ^ p.natDegree) :
    ν (p.eval t) = ν p.leadingCoeff * ν t ^ p.natDegree := by
  set n := p.natDegree with hn
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · simp [eval_eq_sum_range, ← hn, h0, leadingCoeff]
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + p.leadingCoeff * t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, leadingCoeff]
  have hlt : ν (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < ν (p.leadingCoeff * t ^ n) := by
    rw [map_mul, map_pow]
    refine ν.map_sum_lt (zero_le.trans_lt (hp 0 h0)).ne' fun i hi ↦ ?_
    rw [map_mul, map_pow]
    exact hp i (Finset.mem_range.mp hi)
  rw [heval, ν.map_add_eq_of_lt_right hlt, map_mul, map_pow]

/-- If `p` is monic with coefficients that are integral for the valuation `ν` and `1 < ν t`,
then the value of `p` at `t` is dominated by the leading term: `ν (p.eval t) = ν t ^ p.natDegree`.
In particular, `p.eval t ≠ 0`. -/
lemma map_eval_eq_of_one_lt {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (ht : 1 < ν t) :
    ν (p.eval t) = ν t ^ p.natDegree := by
  have h := ν.map_eval_eq_leadingCoeff_mul_pow (p := p) (t := t) fun i hi ↦ by
    rw [hp.leadingCoeff, ν.map_one, one_mul]
    calc ν (p.coeff i) * ν t ^ i ≤ 1 * ν t ^ i := by gcongr; exact hcoeff i hi
      _ = ν t ^ i := one_mul _
      _ < ν t ^ p.natDegree := pow_lt_pow_right₀ ht hi
  rwa [hp.leadingCoeff, ν.map_one, one_mul] at h

section Group

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **The leading term of a polynomial dominates its value at a large argument**: if `ν t ≥ 1` and
every coefficient of `p` below the leading one has value less than `ν (leadingCoeff p) * ν t`, then
`ν (p.eval t) = ν (leadingCoeff p) * ν t ^ natDegree p`. -/
theorem map_eval_eq_leadingCoeff_mul_pow_of_one_le (ν : Valuation L Γ₀) {p : L[X]}
    (ht : 1 ≤ ν t) (hp : ∀ i < p.natDegree, ν (p.coeff i) < ν p.leadingCoeff * ν t) :
    ν (p.eval t) = ν p.leadingCoeff * ν t ^ p.natDegree := by
  have ht0 : 0 < ν t := zero_lt_one.trans_le ht
  refine ν.map_eval_eq_leadingCoeff_mul_pow fun i hi ↦ ?_
  calc ν (p.coeff i) * ν t ^ i < ν p.leadingCoeff * ν t * ν t ^ i :=
        mul_lt_mul_of_pos_right (hp i hi) (pow_pos ht0 i)
    _ = ν p.leadingCoeff * ν t ^ (i + 1) := by rw [pow_succ', mul_assoc]
    _ ≤ ν p.leadingCoeff * ν t ^ p.natDegree := by
      gcongr ν p.leadingCoeff * ?_
      exact pow_le_pow_right₀ ht hi

/-- **The leading term of a polynomial dominates at every large enough argument**: over a division
ring, there is a bound `R` such that `ν (p.eval t) = ν (leadingCoeff p) * ν t ^ natDegree p`
whenever `R < ν t`. -/
theorem exists_map_eval_eq_leadingCoeff_mul_pow {K : Type*} [DivisionRing K] (ν : Valuation K Γ₀)
    (p : K[X]) :
    ∃ R : Γ₀, ∀ t : K, R < ν t → ν (p.eval t) = ν p.leadingCoeff * ν t ^ p.natDegree := by
  obtain ⟨M, hM⟩ := ((Finset.range p.natDegree).image
    fun i ↦ ν (p.coeff i) / ν p.leadingCoeff).exists_le
  refine ⟨max 1 M, fun t ht ↦ ν.map_eval_eq_leadingCoeff_mul_pow_of_one_le
    ((le_max_left _ _).trans ht.le) fun i hi ↦ ?_⟩
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hi
  have hlc : 0 < ν p.leadingCoeff := by
    rw [zero_lt_iff, ne_eq, ν.zero_iff, leadingCoeff_eq_zero]
    exact hp
  have hi' := (hM _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi))).trans_lt
    ((le_max_right _ _).trans_lt ht)
  rwa [div_lt_iff₀ hlc, mul_comm] at hi'

end Group

/-- A root of a monic polynomial whose coefficients have value at most one also has value
at most one. -/
lemma le_one_of_root_monic {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (heq : p.eval t = 0) :
    ν t ≤ 1 :=
  le_of_not_gt fun ht ↦ pow_ne_zero _ (zero_le.trans_lt ht).ne' <| by
    rw [← ν.map_eval_eq_of_one_lt hp hcoeff ht, heq, map_zero]

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
  · contrapose! h
    exact ν.map_sub_le (ν.map_add_le (by simpa using pow_le_one₀ zero_le h)
      (by simpa using mul_le_one' ha h)) hc
  · rw [sub_eq_add_neg, map_quadratic_eq_of_one_lt ν ha (by rwa [Valuation.map_neg]) ht]
    exact ht.trans_le (le_self_pow₀ ht.le two_ne_zero)

end Quadratic

section Cubic

variable {c : L}

-- After the subsingleton value-monoid case is discharged, `ν` supplies the nontriviality
-- of `L` needed to compute the degree and monicity of the cubic.

/-- A monic cubic with integral coefficients, evaluated at an element of value `> 1`, is
dominated by its leading term. -/
lemma map_cubic_eq_of_one_lt (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1) (ht : 1 < ν t) :
    ν (t ^ 3 + a * t ^ 2 + b * t + c) = ν t ^ 3 := by
  nontriviality Γ
  have := domain_nontrivial ν ν.map_zero ν.map_one
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  have h := ν.map_eval_eq_of_one_lt hp (fun i hi ↦ by
    rw [hdeg] at hi
    interval_cases i <;> simp [ha, hb, hc]) ht
  rw [hdeg] at h
  simpa [eval_X_pow] using h

/-- A root of a monic cubic with integral coefficients is integral. -/
lemma le_one_of_root_cubic (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (heq : t ^ 3 + a * t ^ 2 + b * t + c = 0) :
    ν t ≤ 1 :=
  le_of_not_gt fun ht ↦ pow_ne_zero 3 (zero_le.trans_lt ht).ne' <| by
    rw [← ν.map_cubic_eq_of_one_lt ha hb hc ht, heq, map_zero]

end Cubic

section CubicDerivative

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommMonoidWithZero Γ] (ν : Valuation L Γ)
  {t a b c : L}

/-- **At a root of a monic cubic with `ν`-integral `a`, `b` and unit discriminant, the derivative
is a unit.** If `t³ + at² + bt + c = 0`, the coefficients `a`, `b` are integral and the
discriminant `a²b² - 4b³ - 4a³c - 27c² + 18abc` of the cubic has value `1`, then
`3t² + 2at + b` has value `1`. At a root, the discriminant is `s² ((a² - 3b) - s)` for the
derivative `s = 3t² + 2at + b`; integrality of `c` and `t` is not needed. -/
lemma map_cubic_deriv_eq_one (ha : ν a ≤ 1) (hb : ν b ≤ 1)
    (heq : t ^ 3 + a * t ^ 2 + b * t + c = 0)
    (hd : ν (a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 + 18 * a * b * c) = 1) :
    ν (3 * t ^ 2 + 2 * a * t + b) = 1 := by
  have hc : c = -(t ^ 3 + a * t ^ 2 + b * t) := by linear_combination heq
  subst hc
  have hdisc : a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * (-(t ^ 3 + a * t ^ 2 + b * t)) -
      27 * (-(t ^ 3 + a * t ^ 2 + b * t)) ^ 2 + 18 * a * b * (-(t ^ 3 + a * t ^ 2 + b * t)) =
      (3 * t ^ 2 + 2 * a * t + b) ^ 2 * ((a ^ 2 - 3 * b) - (3 * t ^ 2 + 2 * a * t + b)) := by
    ring
  have h3b : ν (3 * b) ≤ 1 := by
    rw [show 3 * b = b + b + b by ring]
    exact ν.map_add_le (ν.map_add_le hb hb) hb
  have hK : ν (a ^ 2 - 3 * b) ≤ 1 :=
    ν.map_sub_le (by rw [map_pow]; exact pow_le_one' ha 2) h3b
  -- The derivative `s` is a root of the monic cubic `s³ - (a² - 3b) s² + disc`, so it is integral.
  have hs : ν (3 * t ^ 2 + 2 * a * t + b) ≤ 1 :=
    ν.le_one_of_root_cubic ((ν.map_sub_swap (3 * b) (a ^ 2)).trans_le hK)
      (ν.map_zero.trans_le zero_le) hd.le (by linear_combination hdisc)
  have hK' : ν ((a ^ 2 - 3 * b) - (3 * t ^ 2 + 2 * a * t + b)) ≤ 1 := ν.map_sub_le hK hs
  rw [hdisc, map_mul, map_pow] at hd
  refine ν.eq_one_of_mul_eq_one (b := (3 * t ^ 2 + 2 * a * t + b) *
      ((a ^ 2 - 3 * b) - (3 * t ^ 2 + 2 * a * t + b))) hs
    (by rw [map_mul]; exact mul_le_one' hs hK') ?_
  rw [show (3 * t ^ 2 + 2 * a * t + b) * ((3 * t ^ 2 + 2 * a * t + b) *
    ((a ^ 2 - 3 * b) - (3 * t ^ 2 + 2 * a * t + b))) = (3 * t ^ 2 + 2 * a * t + b) ^ 2 *
    ((a ^ 2 - 3 * b) - (3 * t ^ 2 + 2 * a * t + b)) by ring, map_mul, map_pow]
  exact hd

end CubicDerivative

end Valuation

end
