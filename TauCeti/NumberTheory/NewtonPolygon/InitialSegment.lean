/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Entire
public import TauCeti.Analysis.Convex.Sequence.Minkowski.InitialSegment

/-!
# Initial Newton slopes of entire products

An initial segment of an entire factor's Newton polygon survives multiplication if all its
slopes are at most every finite slope of the other factor. The second factor contributes its
order of vanishing as an index shift, and its first nonzero coefficient valuation as a height
translation. In particular, for factors with nonzero constant coefficients there is no index
shift, and the initial unit slopes occur unchanged in the product. Equality at the separating
slope is permitted.

The conclusion concerns genuine finite edges strictly before the specified endpoint. It does
not assert preservation of the outgoing edge or of the rest of the polygon. Entire convergence
is used for the global polygon product identity; that identity is not valid for arbitrary
series restricted on just one disc.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §§3–4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
-/

public section

open TauCeti

namespace PowerSeries

variable {K : Type*} [NormedDivisionRing K] (v : AddValuation K (WithTop ℝ)) {B : ℝ}
  (hB : 1 < B) (hv : ∀ x ≠ 0, ‖x‖ = B ^ (-(v x).untop₀)) {f g : K⟦X⟧}

include hB hv

/-- An entire product preserves an initial polygon segment whose slopes precede all slopes
of the second factor. The shift `a` is the order of the second factor, and the added height
is the valuation of its first nonzero coefficient. Take `a = 0` for nonzero constants. -/
theorem IsEntire.newtonPolygon_mul_eqOn_initialSegment (hf : f.IsEntire) (hg : g.IsEntire)
    {p a : ℕ} (hp : f.newtonPolygon v p ≠ ⊤) (ha : g.order = a)
    (hslopes : ∀ k ∈ finiteEdges (f.newtonPolygon v), k < p →
      ∀ j ∈ finiteEdges (g.newtonPolygon v),
        unitSlope (f.newtonPolygon v) k ≤ unitSlope (g.newtonPolygon v) j) :
    ∀ i ≤ p, (f * g).newtonPolygon v (i + a) =
      f.newtonPolygon v i + v (g.coeff a) := by
  have hga : IsAdmissible fun n => v (g.coeff n) :=
    (isAdmissible_addValuation_coeff_iff_exists_isRestricted g v hB hv).mpr
      ⟨1, zero_lt_one, hg.isRestricted 1⟩
  have hanchor : g.newtonPolygon v a = v (g.coeff a) :=
    g.newtonPolygon_eq_of_order_eq v hga ha
  have hfinite : g.newtonPolygon v a ≠ ⊤ := by
    rw [hanchor]
    exact v.ne_top_iff.mpr (order_eq_nat.mp ha).1
  have hbefore : ∀ j < a, g.newtonPolygon v j = ⊤ := by
    intro j hj
    apply g.newtonPolygon_eq_top_of_lt_order v
    rw [ha]
    exact_mod_cast hj
  intro i hip
  rw [hf.newtonPolygon_mul v hB hv hg]
  exact (minkowskiSum_eqOn_initialSegment (f.isConvexSeq_newtonPolygon v)
    (g.isConvexSeq_newtonPolygon v) hp hfinite hbefore hslopes i hip).trans
      (congrArg (f.newtonPolygon v i + ·) hanchor)

/-- The initial genuine finite edges of an entire factor retain their slopes in the
product, with the index shift given by the order of the other factor. No completeness,
splitting, or discreteness assumption is needed. -/
theorem IsEntire.unitSlope_newtonPolygon_mul_of_unitSlope_le
    (hf : f.IsEntire) (hg : g.IsEntire) {p a : ℕ}
    (hp : f.newtonPolygon v p ≠ ⊤) (ha : g.order = a)
    (hslopes : ∀ k ∈ finiteEdges (f.newtonPolygon v), k < p →
      ∀ j ∈ finiteEdges (g.newtonPolygon v),
        unitSlope (f.newtonPolygon v) k ≤ unitSlope (g.newtonPolygon v) j)
    {i : ℕ} (hi : i ∈ finiteEdges (f.newtonPolygon v)) (hip : i < p) :
    i + a ∈ finiteEdges ((f * g).newtonPolygon v) ∧
      unitSlope ((f * g).newtonPolygon v) (i + a) = unitSlope (f.newtonPolygon v) i := by
  have hga : IsAdmissible fun n => v (g.coeff n) :=
    (isAdmissible_addValuation_coeff_iff_exists_isRestricted g v hB hv).mpr
      ⟨1, zero_lt_one, hg.isRestricted 1⟩
  have hfinite : g.newtonPolygon v a ≠ ⊤ := by
    rw [g.newtonPolygon_eq_of_order_eq v hga ha]
    exact v.ne_top_iff.mpr (order_eq_nat.mp ha).1
  have hbefore : ∀ j < a, g.newtonPolygon v j = ⊤ := by
    intro j hj
    apply g.newtonPolygon_eq_top_of_lt_order v
    rw [ha]
    exact_mod_cast hj
  rw [hf.newtonPolygon_mul v hB hv hg]
  exact unitSlope_minkowskiSum_of_unitSlope_le (f.isConvexSeq_newtonPolygon v)
    (g.isConvexSeq_newtonPolygon v) hp hfinite hbefore hslopes hi hip

end PowerSeries
