/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Valuation
public import TauCeti.Topology.Algebra.MvPolynomial.OrderAt

/-!
# Constant Lazard valuation passes to polynomial factors

The lexicographically first nonzero Taylor coefficient stays nonzero near its center. Thus
Lazard valuation is locally bounded above by its value at the center. Additivity then implies
that a divisor of a nonzero polynomial has locally constant valuation wherever the polynomial
does. Over a preconnected parameter set, the divisor's valuation is constant.

The parametrization may be a continuous root section. This allows a common stack for a product
to supply constant valuations for its individual factors, including where ordinary fibers are
nullified. Nonzeroness of the product is essential: a zero product supplies no information.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Propositions 3.2 and 3.4.

The argument follows the ambient-order factor argument in
`MvPolynomial.eventually_orderAt_eq_of_dvd`, with the lexicographic valuation in place of
total Taylor order.
-/

public section

open Filter Set Topology

namespace MvPolynomial

variable {σ R : Type*} [LinearOrder σ] [WellFoundedGT σ]

/-- Near a center, a polynomial's Lazard valuation is at most its valuation at that center.
This also includes the zero polynomial, whose valuation is infinite. -/
theorem eventually_lazardValuation_le [CommSemiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] [T1Space R] (p : MvPolynomial σ R) (a : σ → R) :
    ∀ᶠ b in 𝓝 a, p.lazardValuation b ≤ p.lazardValuation a := by
  induction h : p.lazardValuation a with
  | top => simp
  | coe v =>
    have hd := coeff_taylor_ne_zero_of_lazardValuation_eq
      (v := ofLex v) (by simpa using h)
    filter_upwards [(p.continuous_coeff_taylor (ofLex v)).continuousAt.eventually_ne hd]
      with b hb
    simpa using lazardValuation_le_of_coeff_taylor_ne_zero hb

variable [CommRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [NoZeroDivisors R]
  [T1Space R] {Y : Type*} {l : Filter Y} {f : Y → σ → R} {a : σ → R}

/-- Along a parametrization tending to a center, a divisor of a nonzero polynomial has
eventually constant Lazard valuation if the polynomial does. -/
theorem eventually_lazardValuation_eq_of_dvd (p : MvPolynomial σ R)
    {q : MvPolynomial σ R} (hq : q ≠ 0) (hpq : p ∣ q)
    (hf : Tendsto f l (𝓝 a))
    (hval : ∀ᶠ y in l, q.lazardValuation (f y) = q.lazardValuation a) :
    ∀ᶠ y in l, p.lazardValuation (f y) = p.lazardValuation a := by
  obtain ⟨r, rfl⟩ := hpq
  have hr : r ≠ 0 := right_ne_zero_of_mul hq
  filter_upwards [hf.eventually (p.eventually_lazardValuation_le a),
    hf.eventually (r.eventually_lazardValuation_le a), hval] with y hp hrle hsum
  apply le_antisymm hp
  apply (WithTop.add_le_add_iff_right (lazardValuation_eq_top_iff.not.2 hr)).1
  calc
    p.lazardValuation a + r.lazardValuation a =
        p.lazardValuation (f y) + r.lazardValuation (f y) := by
      simpa only [lazardValuation_mul] using hsum.symm
    _ ≤ p.lazardValuation (f y) + r.lazardValuation a := add_le_add le_rfl hrle

/-- A divisor of a nonzero polynomial has constant Lazard valuation along a continuous
parametrization of a preconnected set whenever the polynomial does. -/
theorem lazardValuation_eq_of_dvd (p : MvPolynomial σ R) {q : MvPolynomial σ R}
    (hq : q ≠ 0) (hpq : p ∣ q) [TopologicalSpace Y] {S : Set Y}
    (hS : IsPreconnected S) (hf : ContinuousOn f S)
    (hval : ∀ x ∈ S, ∀ y ∈ S, q.lazardValuation (f x) = q.lazardValuation (f y))
    {x y : Y} (hx : x ∈ S) (hy : y ∈ S) :
    p.lazardValuation (f x) = p.lazardValuation (f y) := by
  apply hS.apply_eq_of_eventually_eq ?_ hx hy
  intro z hz
  exact p.eventually_lazardValuation_eq_of_dvd hq hpq (hf z hz)
    (Filter.Eventually.mono self_mem_nhdsWithin fun w hw ↦ hval w hw z hz)

end MvPolynomial
