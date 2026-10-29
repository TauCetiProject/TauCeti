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

A polynomial `p` has constant Lazard valuation on a set `S`, in a fixed coordinate order, when
`p.lazardValuationReindex e x` is the same at every point `x ∈ S`. The valuation vanishes exactly
where `p` does not, so on a preconnected set constant valuation forces `p` to be sign-invariant,
just as constant order of vanishing does.

## Main results

* `IsPreconnected.signInvariant_eval_of_lazardValuationReindex_eq`: constant Lazard valuation on
  a preconnected set implies sign-invariance.

## References

* D. Lazard, *An improved projection for cylindrical algebraic decomposition*, in *Algebraic
  Geometry and its Applications*, Springer (1994), 467–476.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69.
-/

public section

open MvPolynomial

/-- A polynomial whose Lazard valuation, in some fixed coordinate order, is the same at all
points of a preconnected set `S` is sign-invariant on `S`: the valuation vanishes exactly where
the polynomial does not. -/
theorem IsPreconnected.signInvariant_eval_of_lazardValuationReindex_eq {σ τ R : Type*}
    [CommSemiring R] [LinearOrder R] [TopologicalSpace R] [OrderTopology R]
    [IsTopologicalSemiring R] [LinearOrder τ] [WellFoundedGT τ]
    {p : MvPolynomial σ R} {e : σ ≃ τ} {S : Set (σ → R)} (hS : IsPreconnected S)
    (h : ∀ x ∈ S, ∀ y ∈ S, p.lazardValuationReindex e x = p.lazardValuationReindex e y) :
    TauCeti.SignInvariant (fun x ↦ eval x p) S :=
  hS.signInvariant_of_eq_zero_iff (continuous_eval p).continuousOn fun x hx y hy ↦ by
    have hxy := lazardValuationReindex_eq_zero_iff p e x
    rw [h x hx y hy, lazardValuationReindex_eq_zero_iff] at hxy
    exact not_iff_not.1 hxy.symm
