/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.RingTheory.AdicCompletion.IdealOrder

/-!
# Stalk order in formal coordinates

On an affine neighbourhood, expand generators of an ideal sheaf in a chosen power-series
chart of the completed local ring. The stalk order is the infimum of the total-degree orders
of these expansions. In particular, for a finite generating family it is the minimum, not a
sum; an empty family has order infinity.

The chart is an explicit ring equivalence. The field of coefficients may be the residue field
of a non-rational point, and there is no characteristic-zero hypothesis in this comparison.
Existence of such a chart is a separate regular-local-ring question.

The order convention follows Bierstone–Milman, *Canonical desingularization in characteristic
zero by blowing up the maximum strata of a local invariant* (1997), Corollary 3.20 and §4.1.
-/

public section

open IsLocalRing

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

/-- Given formal coordinates at a point, expand any family generating the section ideal on
an affine neighbourhood. The least expansion order computes the stalk order. This allows
non-rational points, arbitrary characteristic and empty generating families. -/
theorem stalkOrder_eq_iInf_order_of_span_of_completion_equiv
    {σ k ι : Type*} [Finite σ] [Field k] (I : X.IdealSheafData) (U : X.affineOpens)
    (f : ι → Γ(X, U)) (hf : I.ideal U = Ideal.span (Set.range f)) (x : X) (hx : x ∈ U.val)
    (hfg : (maximalIdeal (X.presheaf.stalk x)).FG)
    (e : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      MvPowerSeries σ k) :
    I.stalkOrder x = ⨅ i,
      (e (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
        ((X.presheaf.germ U.val x hx).hom (f i)))).order := by
  rw [stalkOrder_def, I.stalkIdeal_eq_map U x hx, hf, Ideal.map_span, ← Set.range_comp]
  exact Ideal.localOrder_span_range_eq_iInf_order_of_completion_equiv _ hfg e

end AlgebraicGeometry.Scheme.IdealSheafData
