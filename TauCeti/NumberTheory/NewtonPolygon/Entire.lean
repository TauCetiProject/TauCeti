/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.GaussNorm
public import TauCeti.NumberTheory.NewtonPolygon.Mul
public import TauCeti.RingTheory.PowerSeries.Entire.Basic

/-!
# Newton polygons of products of restricted and entire series

Fix a real additive valuation `v` on a normed division ring and a base `b > 1` with
`‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x`. A nonzero series restricted at the radius `b ^ σ`
attains its Gauss norm there, so its coefficient heights touch a supporting line of slope `σ`.
Consequently, at every slope `σ` such that two series are restricted at the radius `b ^ σ`, the
supporting value at `σ` of the Newton polygon of their product is the sum of those of the
factors. This includes a radius on the boundary of convergence, where a polygon may end in a ray.

An entire series is restricted at every radius, so for entire series the supporting values add at
every slope. Since a convex height sequence is determined by its supporting values, the Newton
polygon of a product of entire series is the Minkowski sum of the Newton polygons of the factors.
This global identity fails for series that are only restricted on a disc: `1 - X` and the
geometric series `∑ Xⁿ` have product `1`, a single point, while the Minkowski sum of their
polygons is a horizontal half-line.

## Main results

* `PowerSeries.supportingValue_newtonPolygon_mul_of_isRestricted`: supporting values of Newton
  polygons add under multiplication at every slope of a common restricted radius.
* `PowerSeries.IsEntire.newtonPolygon_mul`: the Newton polygon of a product of entire series is
  the Minkowski sum of the Newton polygons of the factors.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open TauCeti

namespace PowerSeries

variable {K : Type*} [NormedDivisionRing K] (v : AddValuation K (WithTop ℝ)) {b : ℝ}
  (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f g : K⟦X⟧}

include hb hv

/-- If `f` and `g` are restricted at the radius `b ^ σ`, the supporting value at `σ` of the
Newton polygon of `f * g` is the sum of those of the Newton polygons of `f` and `g`. The radius
may lie on the boundary of convergence of either factor. -/
theorem supportingValue_newtonPolygon_mul_of_isRestricted {σ : ℝ}
    (hf : f.IsRestricted (b ^ σ)) (hg : g.IsRestricted (b ^ σ)) :
    supportingValue ((f * g).newtonPolygon v) σ =
      supportingValue (f.newtonPolygon v) σ + supportingValue (g.newtonPolygon v) σ := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul, newtonPolygon_zero, supportingValue_top, EReal.top_add_of_ne_bot
      (supportingValue_newtonPolygon_ne_bot_of_isRestricted g v hb hv hg)]
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero, newtonPolygon_zero, supportingValue_top, EReal.add_top_of_ne_bot
      (supportingValue_newtonPolygon_ne_bot_of_isRestricted f v hb hv hf)]
  obtain ⟨c, i, hc, hi⟩ :=
    exists_isSupportingLine_mem_supportingFace_of_isRestricted f v hb hv hf hf0
  obtain ⟨d, j, hd, hj⟩ :=
    exists_isSupportingLine_mem_supportingFace_of_isRestricted g v hb hv hg hg0
  exact supportingValue_newtonPolygon_mul v hc hi hd hj

/-- The Newton polygon of a product of entire series is the Minkowski sum of the Newton polygons
of the factors. -/
theorem IsEntire.newtonPolygon_mul (hf : f.IsEntire) (hg : g.IsEntire) :
    (f * g).newtonPolygon v = minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul, newtonPolygon_zero, top_minkowskiSum]
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero, newtonPolygon_zero, minkowskiSum_top]
  exact newtonPolygon_mul_of_forall_exists_mem_supportingFace v
    (fun _ => exists_isSupportingLine_mem_supportingFace_of_isRestricted f v hb hv
      (hf.isRestricted _) hf0)
    (fun _ => exists_isSupportingLine_mem_supportingFace_of_isRestricted g v hb hv
      (hg.isRestricted _) hg0)

end PowerSeries
