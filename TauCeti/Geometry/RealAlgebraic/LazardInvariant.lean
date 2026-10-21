/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MvPolynomial
public import TauCeti.Geometry.RealAlgebraic.SignInvariant
public import TauCeti.RingTheory.MvPolynomial.Lazard.Reindex

/-!
# Constant Lazard valuation and constant sign

A polynomial is sign-invariant on a preconnected set on which one of its reindexed Lazard
valuations is constant, because the valuation vanishes exactly where the polynomial does not.
This is how Lazard-valuation invariance of the cells of a decomposition yields the
sign-invariance asked of a cylindrical algebraic decomposition.

## Main results

* `IsPreconnected.signInvariant_eval_of_lazardValuationReindex_eq`: constant Lazard valuation
  implies sign-invariance on preconnected sets.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.
-/

public section

open MvPolynomial

/-- A polynomial whose reindexed Lazard valuation is constant on a preconnected set is
sign-invariant there: the valuation vanishes exactly where the polynomial does not. -/
theorem IsPreconnected.signInvariant_eval_of_lazardValuationReindex_eq {σ τ R : Type*}
    [LinearOrder τ] [WellFoundedGT τ] [CommSemiring R] [LinearOrder R] [TopologicalSpace R]
    [OrderTopology R] [IsTopologicalSemiring R] {s : Set (σ → R)} (hs : IsPreconnected s)
    {p : MvPolynomial σ R} {e : σ ≃ τ}
    (h : ∀ x ∈ s, ∀ y ∈ s, p.lazardValuationReindex e x = p.lazardValuationReindex e y) :
    TauCeti.SignInvariant (fun x ↦ eval x p) s :=
  hs.signInvariant_of_eq_zero_iff (continuous_eval p).continuousOn fun x hx y hy ↦ by
    have hx' := lazardValuationReindex_eq_zero_iff p e x
    rw [h x hx y hy, lazardValuationReindex_eq_zero_iff] at hx'
    exact not_iff_not.1 hx'.symm
