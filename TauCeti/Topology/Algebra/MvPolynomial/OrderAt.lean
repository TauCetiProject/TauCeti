/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.OrderAt
public import Mathlib.Topology.Algebra.MvPolynomial
public import TauCeti.Topology.LocallyConstant.Preconnected

/-!
# Constant ambient order passes to polynomial factors

Taylor coefficients vary continuously with their center, so the ambient order of a fixed
polynomial cannot increase near a point. Over a domain, orders add on products. If a nonzero
product has constant order along a continuous parametrization, neither factor can lose order
locally, because the other factor cannot gain it. Each factor therefore has locally constant
order, and constant order on a preconnected parameter set.

The nonzero-product hypothesis is essential: a zero product has infinite order everywhere
and gives no information about the orders of its factors. Zero polynomials are nevertheless
included in the local upper bound.

These results complement additivity of ambient order: on a preconnected set, a nonzero
product is order-invariant exactly when its factors are. In particular, constant product
order gives constant factor orders, which imply sign-invariance of the factors over a
linearly ordered topological ring. A continuous root section is another possible parametrization.
The order is computed in all polynomial variables, rather than in a specialized univariate
fiber.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998),
  pp. 242–268, the product order-invariance lemma. `IsPreconnected.orderAt_eq_of_prod`
  generalizes its product-to-factors implication to continuous parametrizations over
  topological domains.
-/

public section

open Filter Set Topology

namespace MvPolynomial

variable {σ R : Type*}

section Continuity

variable [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- Each Taylor coefficient of a fixed polynomial depends continuously on the center. -/
theorem continuous_coeff_taylor (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    Continuous fun a : σ → R ↦ (taylor a p).coeff d := by
  simpa only [eval_coeff_taylor_map_C] using
    continuous_eval ((taylor (X : σ → MvPolynomial σ R) (map C p)).coeff d)

/-- Near any center, the ambient order of a polynomial is at most its order at that center.
This includes the zero polynomial, whose order is infinite. -/
theorem eventually_orderAt_le [T1Space R] (p : MvPolynomial σ R) (a : σ → R) :
    ∀ᶠ b in 𝓝 a, p.orderAt b ≤ p.orderAt a := by
  by_cases htop : p.orderAt a = ⊤
  · simp [htop]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 htop
  obtain ⟨⟨d, hd, hdeg⟩, _⟩ := orderAt_eq_coe_iff.1 hm.symm
  filter_upwards [(p.continuous_coeff_taylor d).continuousAt.eventually_ne hd] with b hb
  simpa only [hdeg, hm] using orderAt_le hb

end Continuity

section Factors

variable [CommRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [NoZeroDivisors R] [T1Space R]
  {Y : Type*} {l : Filter Y} {f : Y → σ → R} {a : σ → R}

/-- Along a parametrization tending to `a`, a divisor of a nonzero polynomial has eventually
constant ambient order whenever the ambient order of the polynomial is eventually constant. -/
theorem eventually_orderAt_eq_of_dvd (p : MvPolynomial σ R) {q : MvPolynomial σ R}
    (hq : q ≠ 0) (hpq : p ∣ q)
    (hf : Tendsto f l (𝓝 a)) (horder : ∀ᶠ y in l, q.orderAt (f y) = q.orderAt a) :
    ∀ᶠ y in l, p.orderAt (f y) = p.orderAt a := by
  obtain ⟨r, rfl⟩ := hpq
  have hr : r ≠ 0 := right_ne_zero_of_mul hq
  filter_upwards [hf.eventually (p.eventually_orderAt_le a),
    hf.eventually (r.eventually_orderAt_le a), horder] with y hp hrle hsum
  apply le_antisymm hp
  apply (ENat.add_le_add_iff_right (orderAt_eq_top_iff.not.2 hr)).1
  calc
    p.orderAt a + r.orderAt a = p.orderAt (f y) + r.orderAt (f y) := by
      simpa only [orderAt_mul] using hsum.symm
    _ ≤ p.orderAt (f y) + r.orderAt a := add_le_add le_rfl hrle

/-- On a preconnected parameter set, a divisor of a nonzero polynomial has constant ambient
order if the polynomial has constant ambient order. The centers may be any continuous
parametrization, including a moving root section. -/
theorem orderAt_eq_of_dvd (p : MvPolynomial σ R) {q : MvPolynomial σ R}
    (hq : q ≠ 0) (hpq : p ∣ q)
    [TopologicalSpace Y] {S : Set Y} (hS : IsPreconnected S) (hf : ContinuousOn f S)
    (horder : ∀ x ∈ S, ∀ y ∈ S, q.orderAt (f x) = q.orderAt (f y))
    {x y : Y} (hx : x ∈ S) (hy : y ∈ S) :
    p.orderAt (f x) = p.orderAt (f y) := by
  apply hS.apply_eq_of_eventually_eq ?_ hx hy
  intro z hz
  exact p.eventually_orderAt_eq_of_dvd hq hpq (hf z hz)
    (Filter.Eventually.mono self_mem_nhdsWithin fun w hw ↦ horder w hw z hz)

end Factors

end MvPolynomial

/-- Constant finite ambient order of a polynomial product on a preconnected parameter set
implies constant ambient order of every factor. Repeated factors and the empty product are
allowed, but the product must be nonzero. -/
theorem IsPreconnected.orderAt_eq_of_prod {σ R Y ι : Type*} [CommRing R]
    [NoZeroDivisors R] [TopologicalSpace R] [IsTopologicalSemiring R] [T1Space R]
    [TopologicalSpace Y] {S : Set Y} (hS : IsPreconnected S)
    (p : ι → MvPolynomial σ R) (s : Finset ι) {f : Y → σ → R}
    (hprod : ∏ i ∈ s, p i ≠ 0) (hf : ContinuousOn f S)
    (horder : ∀ x ∈ S, ∀ y ∈ S,
      (∏ i ∈ s, p i).orderAt (f x) = (∏ i ∈ s, p i).orderAt (f y))
    {i : ι} (hi : i ∈ s) {x y : Y} (hx : x ∈ S) (hy : y ∈ S) :
    (p i).orderAt (f x) = (p i).orderAt (f y) :=
  (p i).orderAt_eq_of_dvd hprod (Finset.dvd_prod_of_mem p hi) hS hf horder hx hy
