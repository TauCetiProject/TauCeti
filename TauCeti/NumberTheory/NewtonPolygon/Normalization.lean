/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Map
public import TauCeti.NumberTheory.NewtonPolygon.Slopes
public import TauCeti.RingTheory.Valuation.NormNormalization
import Mathlib.Algebra.Order.GroupWithZero.OrderIso

/-!
# Newton polygons under a change of valuation normalisation

Changing the additive scale of coefficient valuations changes the polygon by the
same map on its heights, leaving its finite domain unchanged. For polynomials the
finite slope multiset is mapped by that scale as well.

In particular, if valuations `v` and `w` recover one norm using bases `b > 1` and
`b' > 1`, then the heights and slopes for `w` are those for `v` multiplied by
`log b / log b'`. Zero inputs and missing coefficients are included: infinity
remains infinity and the zero polynomial has no finite slopes. No completeness
or discreteness hypothesis is needed.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §§3–4.
-/

public section

open TauCeti

namespace TauCeti

private noncomputable def normNormalizationIso {b b' : ℝ} (hb : 1 < b) (hb' : 1 < b') : ℝ ≃+o ℝ :=
  let c := Real.log b / Real.log b'
  have hc : 0 < c := div_pos (Real.log_pos hb) (Real.log_pos hb')
  { (OrderIso.mulLeft₀ c hc).toEquiv with
    map_add' := mul_add c
    map_le_map_iff' := mul_le_mul_iff_right₀ hc }

private theorem coe_normNormalizationIso {b b' : ℝ} (hb : 1 < b) (hb' : 1 < b') :
    ⇑(normNormalizationIso hb hb') = fun t => (Real.log b / Real.log b') * t := rfl

end TauCeti

namespace PowerSeries

/-- An ordered additive change in coefficient values induces the same change in
Newton heights, including the fallback for inadmissible coefficient sequences. -/
theorem newtonPolygon_eq_map_of_forall_eq_map {R : Type*} [Ring R] (f : R⟦X⟧)
    (v w : AddValuation R (WithTop ℝ)) (e : ℝ ≃+o ℝ)
    (hvw : ∀ x, w x = WithTop.map e (v x)) :
    f.newtonPolygon w = fun n => WithTop.map e (f.newtonPolygon v n) := by
  simp only [newtonPolygon_def, hvw]
  exact lowerConvexEnvelope_map e

/-- Replacing a norm-recovery base `b` by `b'` multiplies Newton heights by
`log b / log b'`. Infinity is preserved, even for vertical coefficient sequences. -/
theorem newtonPolygon_eq_map_of_norm_eq_rpow {K : Type*} [NormedDivisionRing K]
    (f : K⟦X⟧) (v w : AddValuation K (WithTop ℝ))
    {b b' : ℝ} (hb : 1 < b) (hb' : 1 < b')
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
    (hw : ∀ x ≠ 0, ‖x‖ = b' ^ (-(w x).untop₀)) :
    f.newtonPolygon w = fun n =>
      WithTop.map (fun t => (Real.log b / Real.log b') * t) (f.newtonPolygon v n) := by
  simpa only [coe_normNormalizationIso] using
    f.newtonPolygon_eq_map_of_forall_eq_map v w (normNormalizationIso hb hb')
      (by simpa only [coe_normNormalizationIso] using v.eq_map_of_norm_eq_rpow w hb hb' hv hw)

end PowerSeries

namespace Polynomial

/-- An ordered additive change in coefficient values induces the same change in
polynomial Newton heights. -/
theorem newtonPolygon_eq_map_of_forall_eq_map {R : Type*} [Ring R] (f : R[X])
    (v w : AddValuation R (WithTop ℝ)) (e : ℝ ≃+o ℝ)
    (hvw : ∀ x, w x = WithTop.map e (v x)) :
    f.newtonPolygon w = fun n => WithTop.map e (f.newtonPolygon v n) := by
  simpa only [newtonPolygon_coe] using
    (f : PowerSeries R).newtonPolygon_eq_map_of_forall_eq_map v w e hvw

/-- Changing the additive value scale maps every finite polynomial slope, with its
multiplicity. No endpoint sentinel contributes a slope. -/
theorem newtonSlopes_eq_map_of_forall_eq_map {R : Type*} [Ring R] (f : R[X])
    (v w : AddValuation R (WithTop ℝ)) (e : ℝ ≃+o ℝ)
    (hvw : ∀ x, w x = WithTop.map e (v x)) :
    f.newtonSlopes w = (f.newtonSlopes v).map e := by
  have hpoly := f.newtonPolygon_eq_map_of_forall_eq_map v w e hvw
  exact newtonSlopes_eq_map (f := f) (v := v) Function.injective_id.injOn
    (by rw [hpoly, finiteEdges_map, Set.image_id])
    (fun n _ => by rw [hpoly, id, unitSlope_map])

/-- Replacing a norm-recovery base `b` by `b'` multiplies polynomial Newton heights
by `log b / log b'`. -/
theorem newtonPolygon_eq_map_of_norm_eq_rpow {K : Type*} [NormedDivisionRing K]
    (f : K[X]) (v w : AddValuation K (WithTop ℝ))
    {b b' : ℝ} (hb : 1 < b) (hb' : 1 < b')
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
    (hw : ∀ x ≠ 0, ‖x‖ = b' ^ (-(w x).untop₀)) :
    f.newtonPolygon w = fun n =>
      WithTop.map (fun t => (Real.log b / Real.log b') * t) (f.newtonPolygon v n) := by
  simpa only [newtonPolygon_coe] using
    (f : PowerSeries K).newtonPolygon_eq_map_of_norm_eq_rpow v w hb hb' hv hw

/-- Replacing a norm-recovery base `b` by `b'` multiplies every finite polynomial
slope by `log b / log b'`, preserving multiplicities and the empty slope multiset. -/
theorem newtonSlopes_eq_map_of_norm_eq_rpow {K : Type*} [NormedDivisionRing K]
    (f : K[X]) (v w : AddValuation K (WithTop ℝ))
    {b b' : ℝ} (hb : 1 < b) (hb' : 1 < b')
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
    (hw : ∀ x ≠ 0, ‖x‖ = b' ^ (-(w x).untop₀)) :
    f.newtonSlopes w = (f.newtonSlopes v).map
      (fun t => (Real.log b / Real.log b') * t) := by
  simpa only [coe_normNormalizationIso] using
    f.newtonSlopes_eq_map_of_forall_eq_map v w (normNormalizationIso hb hb')
      (by simpa only [coe_normNormalizationIso] using v.eq_map_of_norm_eq_rpow w hb hb' hv hw)

end Polynomial
