/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
public import TauCeti.RingTheory.Polynomial.Eulerian
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Rational formulas for nonpositive polylogarithms

The Eulerian polynomial `Aᵣ = TauCeti.eulerianPolynomial r` is the reduced polynomial
factor after factoring out `z` in `Li₋ᵣ(z) = z Aᵣ(z) / (1 - z)^(r+1)`.
This identity holds even at the totalised value at 1. Its differential recurrence
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

namespace TauCeti

namespace Polylog

private theorem polylog_neg_nat_eq_div_of_ne_one (r : ℕ) {z : ℂ} (hz : z ≠ 1) :
    polylog (-(r : ℤ)) z = z * aeval z (eulerianPolynomial r) / (1 - z) ^ (r + 1) := by
  induction r generalizing z with
  | zero => simp
  | succ r ih =>
    have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
    have hlocal : polylog (-(r : ℤ)) =ᶠ[𝓝 z]
        (fun w : ℂ => w * aeval w (eulerianPolynomial r) / (1 - w) ^ (r + 1)) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact ih hw
    have hd := ((hasDerivAt_id z).mul ((eulerianPolynomial r).hasDerivAt_aeval z)).div
      (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).pow (r + 1))
      (pow_ne_zero _ hne)
    rw [polylog_neg_nat_succ, (hd.congr_of_eventuallyEq hlocal).deriv]
    dsimp only [id_eq, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    simp only [eulerianPolynomial_succ, map_add, map_mul, map_sub, map_one, aeval_C, aeval_X]
    push_cast
    simp only [pow_succ]
    field_simp
    ring

/-- Removing the pole of order `r + 1` gives the nonzero leading coefficient `r!`.
The limit is punctured, so it does not use any assigned value of `Li₋ᵣ` at 1. -/
theorem tendsto_one_sub_pow_mul_polylog_neg_nat_nhdsNE_one (r : ℕ) :
    Tendsto (fun z : ℂ => (1 - z) ^ (r + 1) * polylog (-(r : ℤ)) z)
      (𝓝[≠] 1) (𝓝 (r.factorial : ℂ)) := by
  have heval : aeval (1 : ℂ) (eulerianPolynomial r) = (r.factorial : ℂ) := by
    simp [aeval_def]
  have h : Tendsto (fun z : ℂ => z * aeval z (eulerianPolynomial r))
      (𝓝[≠] 1) (𝓝 (r.factorial : ℂ)) := by
    have hcont : Continuous (fun z : ℂ => z * aeval z (eulerianPolynomial r)) :=
      continuous_id.mul (eulerianPolynomial r).continuous_aeval
    simpa only [one_mul, heval] using
      hcont.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z ≠ 1 := by simpa using hz
  rw [polylog_neg_nat_eq_div_of_ne_one r hne]
  field_simp

/-- Totalisation at the pole never makes a nonpositive polylogarithm continuous there. -/
theorem not_continuousAt_polylog_neg_nat_one (r : ℕ) :
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
  have heq := tendsto_nhds_unique hzero
    (tendsto_one_sub_pow_mul_polylog_neg_nat_nhdsNE_one r)
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r) : (r.factorial : ℂ) ≠ 0) heq.symm

/-- Every nonpositive weight is the indicated rational function, including at the
totalised pole, where both sides vanish. -/
theorem polylog_neg_nat_eq_div (r : ℕ) (z : ℂ) :
    polylog (-(r : ℤ)) z = z * aeval z (eulerianPolynomial r) / (1 - z) ^ (r + 1) := by
  by_cases hz : z = 1
  · subst z
    cases r with
    | zero => simp
    | succ r =>
      rw [polylog_neg_nat_succ, deriv_zero_of_not_differentiableAt
        (mt DifferentiableAt.continuousAt (not_continuousAt_polylog_neg_nat_one r))]
      simp
  · exact polylog_neg_nat_eq_div_of_ne_one r hz

/-- In weight minus two the rational numerator is `z(1 + z)`.
The identity includes the totalised value at 1. -/
theorem polylog_neg_two (z : ℂ) :
    polylog (-2) z = z * (1 + z) / (1 - z) ^ 3 := by
  simpa using polylog_neg_nat_eq_div 2 z

end Polylog

end TauCeti
