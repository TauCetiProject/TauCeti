/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Basic
public import TauCeti.RingTheory.PowerSeries.Valuation

/-!
# Newton polygons of sums

The coefficient heights of a sum satisfy the ultrametric inequality
`min (v (coeff n f)) (v (coeff n g)) ≤ v (coeff n (f + g))`
(`PowerSeries.min_addValuation_coeff_le_addValuation_coeff_add`). Passing to lower convex
envelopes, the Newton polygon of `f + g` lies above the lower convex envelope of the pointwise
minimum of the Newton polygons of `f` and `g`, and hence above every common convex lower bound of
the two polygons. These are the lower bounds used to control the Newton polygon of a perturbation.

The pointwise minimum of the two polygons is generally not convex, and it is not a lower bound
for the polygon of the sum. For example, over a field the polygons of `1` and `X ^ 2` are both
infinite at the index one, while the polygon of `1 + X ^ 2` is finite there.

The inequality cannot be improved to an equality: cancellation in `f + g` can raise any
coefficient height, as for `f + (-f) = 0`. For power series both summands are assumed to have
admissible coefficient heights, and then so does the sum. Without that hypothesis the statement
fails: an inadmissible summand has the all-infinite fallback polygon, although a sum such as
`f + (1 - f) = 1` can have a finite polygon.

## Main results

* `PowerSeries.isAdmissible_addValuation_coeff_add`: a sum of power series with admissible
  coefficient heights has admissible coefficient heights.
* `PowerSeries.lowerConvexEnvelope_inf_le_newtonPolygon_add` and
  `Polynomial.lowerConvexEnvelope_inf_le_newtonPolygon_add`: the Newton polygon of a sum lies
  above the lower convex envelope of the pointwise minimum of the Newton polygons of the
  summands.
* `PowerSeries.le_newtonPolygon_add` and `Polynomial.le_newtonPolygon_add`: a common convex lower
  bound of the Newton polygons of two summands lies below the Newton polygon of their sum.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

open TauCeti

namespace PowerSeries

variable {R : Type*} [Ring R] {v : AddValuation R (WithTop ℝ)} {f g : R⟦X⟧}

/-- A sum of power series with admissible coefficient heights has admissible coefficient
heights. -/
theorem isAdmissible_addValuation_coeff_add (hf : IsAdmissible fun n => v (coeff n f))
    (hg : IsAdmissible fun n => v (coeff n g)) :
    IsAdmissible fun n => v (coeff n (f + g)) :=
  (hf.inf hg).mono fun n => min_addValuation_coeff_le_addValuation_coeff_add v f g n

/-- For power series with admissible coefficient heights, the Newton polygon of a sum lies above
the lower convex envelope of the pointwise minimum of the Newton polygons of the summands. -/
theorem lowerConvexEnvelope_inf_le_newtonPolygon_add (hf : IsAdmissible fun n => v (coeff n f))
    (hg : IsAdmissible fun n => v (coeff n g)) :
    lowerConvexEnvelope (f.newtonPolygon v ⊓ g.newtonPolygon v) ≤ (f + g).newtonPolygon v := by
  simp only [newtonPolygon_def]
  rw [lowerConvexEnvelope_inf_lowerConvexEnvelope hf hg]
  exact lowerConvexEnvelope_mono (hf.inf hg)
    fun n => min_addValuation_coeff_le_addValuation_coeff_add v f g n

/-- For power series with admissible coefficient heights, a convex sequence lying below the
Newton polygons of both summands lies below the Newton polygon of their sum. -/
theorem le_newtonPolygon_add {H : ℕ → WithTop ℝ} (hH : IsConvexSeq H)
    (hf : IsAdmissible fun n => v (coeff n f)) (hg : IsAdmissible fun n => v (coeff n g))
    (hHf : H ≤ f.newtonPolygon v) (hHg : H ≤ g.newtonPolygon v) :
    H ≤ (f + g).newtonPolygon v :=
  (le_lowerConvexEnvelope hH (le_inf hHf hHg)).trans
    (lowerConvexEnvelope_inf_le_newtonPolygon_add hf hg)

end PowerSeries

namespace Polynomial

variable {R : Type*} [Ring R] {v : AddValuation R (WithTop ℝ)}

/-- The Newton polygon of a sum of polynomials lies above the lower convex envelope of the
pointwise minimum of the Newton polygons of the summands. -/
theorem lowerConvexEnvelope_inf_le_newtonPolygon_add (f g : R[X]) :
    lowerConvexEnvelope (f.newtonPolygon v ⊓ g.newtonPolygon v) ≤ (f + g).newtonPolygon v := by
  simpa only [← coe_add, newtonPolygon_coe] using
    PowerSeries.lowerConvexEnvelope_inf_le_newtonPolygon_add
      (f := (f : PowerSeries R)) (g := (g : PowerSeries R))
      (by simpa only [coeff_coe] using isAdmissible_addValuation_coeff f v)
      (by simpa only [coeff_coe] using isAdmissible_addValuation_coeff g v)

/-- A convex sequence lying below the Newton polygons of two polynomials lies below the Newton
polygon of their sum. -/
theorem le_newtonPolygon_add {H : ℕ → WithTop ℝ} (hH : IsConvexSeq H) {f g : R[X]}
    (hHf : H ≤ f.newtonPolygon v) (hHg : H ≤ g.newtonPolygon v) :
    H ≤ (f + g).newtonPolygon v :=
  (le_lowerConvexEnvelope hH (le_inf hHf hHg)).trans
    (lowerConvexEnvelope_inf_le_newtonPolygon_add f g)

end Polynomial
