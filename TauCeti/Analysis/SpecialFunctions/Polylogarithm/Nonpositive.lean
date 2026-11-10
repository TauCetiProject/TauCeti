/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Rational formulas for nonpositive polylogarithms

The integer polynomial `negNumerator r` expresses the nonpositive polylogarithm as
`Li₋ᵣ(z) = z Aᵣ(z) / (1 - z)^(r+1)` away from 1. Its differential recurrence
comes from the Euler operator `z d/dz`. The identity `Aᵣ(1) = r!` gives the exact
leading coefficient at the pole and shows that no nonpositive weight is continuous at 1.
These formulas describe the functions on the whole punctured plane, not just on a slit domain.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762,
  Astérisque 216 (1993), §1.1, (2)–(3), p. 50, for the Euler differential recursion.
  The polynomial recurrence and pole statements are elementary consequences.
-/

public section

open Polynomial Filter Topology

namespace TauCeti.Polylog

/-- The integer numerator polynomials of the nonpositive polylogarithms:
`Li₋ᵣ(z) = z Aᵣ(z) / (1 - z)^(r+1)` for `z ≠ 1`. -/
noncomputable def negNumerator : ℕ → ℤ[X]
  | 0 => 1
  | r + 1 => (1 + C (r : ℤ) * X) * negNumerator r +
      X * (1 - X) * (negNumerator r).derivative

/-- The numerator of weight zero is 1. -/
@[simp] theorem negNumerator_zero : negNumerator 0 = 1 := (rfl)

/-- The numerator recurrence induced by Euler differentiation. -/
theorem negNumerator_succ (r : ℕ) :
    negNumerator (r + 1) = (1 + C (r : ℤ) * X) * negNumerator r +
      X * (1 - X) * (negNumerator r).derivative := (rfl)

/-- The numerator of weight minus one is also 1. -/
@[simp] theorem negNumerator_one : negNumerator 1 = 1 := by
  simp [negNumerator_succ]

/-- The numerator of weight minus two is `1 + X`. -/
@[simp] theorem negNumerator_two : negNumerator 2 = 1 + X := by
  simp [negNumerator_succ]

/-- Evaluation at the pole is a factorial, so the numerator cannot cancel the pole. -/
@[simp] theorem negNumerator_eval_one (r : ℕ) :
    (negNumerator r).eval 1 = (r.factorial : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp [negNumerator_succ, ih, Nat.factorial_succ, add_comm]

/-- None of the numerator polynomials vanishes at 1. -/
theorem negNumerator_eval_one_ne_zero (r : ℕ) : (negNumerator r).eval 1 ≠ 0 := by
  rw [negNumerator_eval_one]
  exact_mod_cast Nat.factorial_ne_zero r

/-- Every nonpositive weight is the indicated rational function away from its pole. -/
theorem polylog_neg_nat_eq_div (r : ℕ) {z : ℂ} (hz : z ≠ 1) :
    polylog (-(r : ℤ)) z = z * aeval z (negNumerator r) / (1 - z) ^ (r + 1) := by
  induction r generalizing z with
  | zero => simp
  | succ r ih =>
    have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
    have hlocal : polylog (-(r : ℤ)) =ᶠ[𝓝 z]
        (fun w : ℂ => w * aeval w (negNumerator r) / (1 - w) ^ (r + 1)) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact ih hw
    have hd := ((hasDerivAt_id z).mul ((negNumerator r).hasDerivAt_aeval z)).div
      (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).pow (r + 1))
      (pow_ne_zero _ hne)
    rw [polylog_neg_nat_succ, (hd.congr_of_eventuallyEq hlocal).deriv]
    dsimp only [id_eq, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    simp only [negNumerator_succ, map_add, map_mul, map_sub, map_one, aeval_C, aeval_X]
    push_cast
    simp only [pow_succ]
    field_simp
    ring

/-- In weight minus two the rational numerator is `z(1 + z)`. -/
theorem polylog_neg_two {z : ℂ} (hz : z ≠ 1) :
    polylog (-2) z = z * (1 + z) / (1 - z) ^ 3 := by
  simpa using polylog_neg_nat_eq_div 2 hz

/-- Removing the pole of order `r + 1` gives the nonzero leading coefficient `r!`.
The limit is punctured, so it does not use any assigned value of `Li₋ᵣ` at 1. -/
theorem tendsto_pow_mul_polylog_neg_nat (r : ℕ) :
    Tendsto (fun z : ℂ => (1 - z) ^ (r + 1) * polylog (-(r : ℤ)) z)
      (𝓝[≠] 1) (𝓝 (r.factorial : ℂ)) := by
  have heval : aeval (1 : ℂ) (negNumerator r) = (r.factorial : ℂ) := by
    simp [aeval_def]
  have h : Tendsto (fun z : ℂ => z * aeval z (negNumerator r))
      (𝓝[≠] 1) (𝓝 (r.factorial : ℂ)) := by
    have hcont : Continuous (fun z : ℂ => z * aeval z (negNumerator r)) :=
      continuous_id.mul (negNumerator r).continuous_aeval
    simpa only [one_mul, heval] using
      hcont.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z ≠ 1 := by simpa using hz
  rw [polylog_neg_nat_eq_div r hne]
  field_simp

/-- Totalisation at the pole never makes a nonpositive polylogarithm continuous there. -/
theorem not_continuousAt_polylog_neg_nat (r : ℕ) :
    ¬ ContinuousAt (polylog (-(r : ℤ))) 1 := by
  intro hc
  have hzero : Tendsto
      (fun z : ℂ => (1 - z) ^ (r + 1) * polylog (-(r : ℤ)) z)
      (𝓝[≠] 1) (𝓝 0) := by
    have hcont : ContinuousAt
        (fun z : ℂ => (1 - z) ^ (r + 1) * polylog (-(r : ℤ)) z) 1 :=
      ((continuous_const.sub continuous_id).pow (r + 1)).continuousAt.mul hc
    simpa using hcont.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  have heq := tendsto_nhds_unique hzero (tendsto_pow_mul_polylog_neg_nat r)
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r) : (r.factorial : ℂ) ≠ 0) heq.symm

end TauCeti.Polylog
