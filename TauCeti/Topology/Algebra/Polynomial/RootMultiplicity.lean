/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Multiplicities along continuous polynomial sections

For a coefficientwise continuous family of locally bounded degree, multiplicity at a continuous
point is locally bounded above by its central value, provided the central polynomial is nonzero.
Hasse derivatives give this statement in arbitrary characteristic. Over an integral domain,
if each factor is nonzero at the base point and the multiplicity in a finite product is locally
constant, every factor multiplicity is locally constant: none can increase, and their sum cannot
decrease.

This transfers the multiplicities of root sections of a product to its individual factors,
including factors sharing roots and roots of multiplicity greater than one.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Section 2 (delineability of a polynomial basis).
-/

public section

open Filter Topology

namespace Polynomial

variable {B R : Type*} [TopologicalSpace B] [TopologicalSpace R]
  {r : B → R} {x₀ : B} {d : ℕ}

/-- Evaluation of a Hasse derivative along a point continuous at `x₀` is continuous at `x₀`
for a family whose coefficients of indices from `m` through `d` are continuous at `x₀` and
whose degrees are bounded by `d` near `x₀`. Coefficients below `m` do not affect the derivative. -/
theorem continuousAt_hasseDeriv_eval [Semiring R] [IsTopologicalSemiring R] {F : B → R[X]}
    (m : ℕ) (hF : ∀ i, m ≤ i → i ≤ d → ContinuousAt (fun x ↦ (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (hr : ContinuousAt r x₀) :
    ContinuousAt (fun x ↦ (hasseDeriv m (F x)).eval (r x)) x₀ := by
  have hcoeff (i : ℕ) : ContinuousAt (fun x ↦ (hasseDeriv m (F x)).coeff i) x₀ := by
    by_cases hi : i + m ≤ d
    · simp only [hasseDeriv_coeff]
      exact continuousAt_const.mul (hF _ (Nat.le_add_left m i) hi)
    · refine (continuousAt_const (y := (0 : R))).congr_of_eventuallyEq ?_
      filter_upwards [hdeg] with x hx
      simp [hasseDeriv_coeff, coeff_eq_zero_of_natDegree_lt (hx.trans_lt (Nat.lt_of_not_ge hi))]
  exact continuousAt_eval (fun i _ ↦ hcoeff i)
    (hdeg.mono fun x hx ↦
      (natDegree_hasseDeriv_le _ _).trans ((Nat.sub_le _ _).trans hx)) hr

variable [CommRing R] [IsTopologicalSemiring R] {F : B → R[X]}

/-- Multiplicity at a continuous point cannot increase nearby when the central polynomial
is nonzero. Zero nearby polynomials are allowed, with their usual multiplicity zero. -/
theorem eventually_rootMultiplicity_le [T1Space R]
    (hF : ∀ i ≤ d, ContinuousAt (fun x ↦ (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (hr : ContinuousAt r x₀)
    (hne : F x₀ ≠ 0) :
    ∀ᶠ x in 𝓝 x₀, (F x).rootMultiplicity (r x) ≤ (F x₀).rootMultiplicity (r x₀) := by
  have hcenter : (hasseDeriv ((F x₀).rootMultiplicity (r x₀)) (F x₀)).eval (r x₀) ≠ 0 := by
    rw [← taylor_coeff, rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
    exact coeff_natTrailingDegree_ne_zero.2 ((taylor_eq_zero _ _).not.2 hne)
  filter_upwards [(continuousAt_hasseDeriv_eval _ (fun i _ hi ↦ hF i hi) hdeg hr).eventually_ne
    hcenter] with x hx
  rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
  exact natTrailingDegree_le_of_ne_zero (by rwa [taylor_coeff])

/-- Along a continuous point, locally constant multiplicity in a nonzero finite product
forces locally constant multiplicity in every factor. No coprimality is required. -/
theorem eventually_rootMultiplicity_eq_of_prod [IsDomain R] [T1Space R]
    {ι : Type*} {F : ι → B → R[X]} {d : ι → ℕ} (s : Finset ι)
    (hF : ∀ k ∈ s, ∀ i ≤ d k, ContinuousAt (fun x ↦ (F k x).coeff i) x₀)
    (hdeg : ∀ k ∈ s, ∀ᶠ x in 𝓝 x₀, (F k x).natDegree ≤ d k) (hr : ContinuousAt r x₀)
    (hne : ∀ k ∈ s, F k x₀ ≠ 0)
    (hmult : ∀ᶠ x in 𝓝 x₀,
      (∏ k ∈ s, F k x).rootMultiplicity (r x) =
        (∏ k ∈ s, F k x₀).rootMultiplicity (r x₀)) :
    ∀ᶠ x in 𝓝 x₀, ∀ k ∈ s, (F k x).rootMultiplicity (r x) =
      (F k x₀).rootMultiplicity (r x₀) := by
  classical
  have hsum (x : B) (hx : ∀ k ∈ s, F k x ≠ 0) :
      (∏ k ∈ s, F k x).rootMultiplicity (r x) =
        ∑ k ∈ s, (F k x).rootMultiplicity (r x) := by
    rw [← count_roots, roots_prod _ _ (Finset.prod_ne_zero_iff.2 hx), Multiset.count_bind]
    simp only [count_roots, Finset.sum_map_val]
  have hle := (eventually_all_finset s).2 fun k hk ↦
    eventually_rootMultiplicity_le (hF k hk) (hdeg k hk) hr (hne k hk)
  have hnonzero : ∀ᶠ x in 𝓝 x₀, ∀ k ∈ s, F k x ≠ 0 :=
    (eventually_all_finset s).2 fun k hk ↦ by
      have hc := (hF k hk _ (hdeg k hk).self_of_nhds).eventually_ne
        (by simpa only [coeff_natDegree] using (leadingCoeff_ne_zero.2 (hne k hk)))
      exact hc.mono fun x hx hzero ↦ hx (by simp [hzero])
  filter_upwards [hle, hnonzero, hmult] with x hx hxne hxm
  rw [hsum x hxne, hsum x₀ hne] at hxm
  exact (Finset.sum_eq_sum_iff_of_le hx).1 hxm

end Polynomial
