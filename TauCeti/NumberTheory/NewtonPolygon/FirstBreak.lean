/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.FirstBreak
public import TauCeti.NumberTheory.NewtonPolygon.ActiveFace
public import TauCeti.NumberTheory.NewtonPolygon.Weierstrass

/-!
# First breaks of Newton polygons

The Newton polygon of a power series `f` has a *first break* at `j` with slope `σ`
(`TauCeti.IsFirstBreak (f.newtonPolygon v) σ l j`) when its first segment, starting at the order of
vanishing `l` of `f`, has slope `σ` and ends at `j`. Since the Newton polygon is the lower convex
envelope of the coefficient heights `n ↦ v (coeff n f)`, the first-break criterion
`TauCeti.IsLowerConvexEnvelope.isFirstBreak_iff` reads it off the coefficients: the line of slope
`σ` through the first coefficient point lies on or below every coefficient point and passes
through the point at `j`, and a line of some strictly larger slope through the point at `j` also
lies on or below every coefficient point.

Fix a real additive valuation `v` on a normed division ring `K` and a base `b > 1` with
`‖x‖ = b ^ (-(v x).untop₀)` for `x ≠ 0`. In terms of the radius `b ^ σ`, a first break at `j` makes
the first nonzero coefficient attain the Gauss norm and makes `f` distinguished of degree `j`
(`PowerSeries.isLowestDominant_and_isDistinguished_of_isFirstBreak_newtonPolygon`). Below a radius
with bounded weighted coefficients these conditions characterise the first break
(`PowerSeries.isFirstBreak_newtonPolygon_iff`). Without the larger radius the converse fails: at a
convergence boundary the first and last active coefficients can lie on an infinite ray of the
polygon.

Weierstrass preparation at `b ^ σ` then splits off the first segment: a prepared polynomial factor
`P` with `u * P = f`, for a restricted unit `u`, has the `j - l` finite slopes of the first segment
and no others (`PowerSeries.newtonSlopes_eq_replicate_of_isFirstBreak`).

For a polynomial the last segment ends at its degree, so it is a first break exactly when the
polynomial is pure (`Polynomial.isFirstBreak_newtonPolygon_natDegree_iff`).

## Main results

* `PowerSeries.order_eq_of_isFirstBreak_newtonPolygon`: a first break starts at the order of
  vanishing.
* `PowerSeries.isLowestDominant_and_isDistinguished_of_isFirstBreak_newtonPolygon` and
  `PowerSeries.isFirstBreak_newtonPolygon_iff`: first breaks and active coefficients.
* `PowerSeries.newtonSlopes_eq_replicate_of_isFirstBreak`: the first-segment factor.
* `Polynomial.isFirstBreak_newtonPolygon_iff`: the polynomial version, at every radius.
* `Polynomial.isFirstBreak_newtonPolygon_natDegree_iff`: a first break at the degree is purity.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open scoped PowerSeries
open TauCeti

namespace PowerSeries

section Ring

variable {R : Type*} [Ring R] {f : R⟦X⟧} {v : AddValuation R (WithTop ℝ)} {σ : ℝ} {l j : ℕ}

/-- The coefficient heights of a series whose Newton polygon has a first break are admissible. -/
theorem isAdmissible_of_isFirstBreak_newtonPolygon
    (hbr : IsFirstBreak (f.newtonPolygon v) σ l j) : IsAdmissible fun n => v (coeff n f) :=
  isAdmissible_of_lowerConvexEnvelope_ne_top (n := l) (f.newtonPolygon_def v ▸ hbr.left_ne_top)

/-- If only zero has infinite valuation, a first break of the Newton polygon starts at the order of
vanishing of the series. Over a division ring the hypothesis on `v` is `AddValuation.top_iff`. -/
theorem order_eq_of_isFirstBreak_newtonPolygon (hv : ∀ x, v x = ⊤ → x = 0)
    (hbr : IsFirstBreak (f.newtonPolygon v) σ l j) : f.order = l := by
  have hadm := isAdmissible_of_isFirstBreak_newtonPolygon hbr
  obtain ⟨i, hil, -, -, hi, -⟩ := (lowerConvexEnvelope_ne_top_iff hadm).mp
    (f.newtonPolygon_def v ▸ hbr.left_ne_top)
  have hle : f.order ≤ l :=
    (order_le i fun h => hi (by rw [h, v.map_zero])).trans (by exact_mod_cast hil)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top l) hle)
  refine le_antisymm hle (le_of_not_gt fun hlt => ?_)
  -- The Newton polygon starts at the first nonzero coefficient, which is finite.
  have hcoeff := newtonPolygon_eq_of_order_eq (v := v) hadm hm.symm
  rw [hbr.eq_top_of_lt m (by rw [← hm] at hlt; exact_mod_cast hlt)] at hcoeff
  exact (order_eq_nat.mp hm.symm).1 (hv _ hcoeff.symm)

end Ring

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K] {f : K⟦X⟧}
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {σ : ℝ} {l j : ℕ}

include hb hv

/-- At the radius `b ^ σ`, a first break at `j` of slope `σ` makes the first nonzero coefficient
`l` attain the Gauss norm and makes the series distinguished of degree `j`. This needs no
restrictedness hypothesis. -/
theorem isLowestDominant_and_isDistinguished_of_isFirstBreak_newtonPolygon
    (hbr : IsFirstBreak (f.newtonPolygon v) σ l j) :
    TauCeti.PowerSeries.IsLowestDominant (b ^ σ) l f ∧
      TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f := by
  have hface := hbr.isFiniteFace (f.isConvexSeq_newtonPolygon v)
  obtain ⟨c, hc, -⟩ := hface.exists_intercept
  have hc' := (f.isLowerConvexEnvelope_newtonPolygon
    (isAdmissible_of_isFirstBreak_newtonPolygon hbr)).isSupportingLine_iff.mp hc
  have hG : f.HasGaussNorm norm (b ^ σ) := (hasGaussNorm_iff_supportingValue_ne_bot f v hb hv σ).mpr
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) (isSupportingLine_iff.mp hc'))
  exact isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv hG hface

/-- **First breaks and active coefficients.** At a radius `b ^ σ` strictly below a radius `b ^ τ`
with bounded weighted coefficients, the Newton polygon has a first break at `j` of slope `σ`
starting at `l` exactly when `l < j`, `l` is the order of vanishing, the coefficient in degree `l`
attains the Gauss norm at `b ^ σ`, and `f` is distinguished of degree `j` there. -/
theorem isFirstBreak_newtonPolygon_iff {τ : ℝ} (hf : f.HasGaussNorm norm (b ^ τ)) (hστ : σ < τ) :
    IsFirstBreak (f.newtonPolygon v) σ l j ↔ l < j ∧ f.order = l ∧
      TauCeti.PowerSeries.IsLowestDominant (b ^ σ) l f ∧
      TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f := by
  refine ⟨fun hbr => ⟨hbr.lt, order_eq_of_isFirstBreak_newtonPolygon (fun _ => v.top_iff.mp) hbr,
    (isFiniteFace_newtonPolygon_iff f v hb hv hf hστ).mp
      (hbr.isFiniteFace (f.isConvexSeq_newtonPolygon v))⟩, fun ⟨hlj, hord, hface⟩ =>
    (f.isConvexSeq_newtonPolygon v).isFirstBreak_iff.mpr ⟨hlj,
      fun n hn => f.newtonPolygon_eq_top_of_lt_order v (by rw [hord]; exact_mod_cast hn),
      (isFiniteFace_newtonPolygon_iff f v hb hv hf hστ).mpr hface⟩⟩

/-- **First-segment factor.** If the Newton polygon of `f` has a first break at `j` of slope `σ`
starting at `l`, and `u * P = f` for a unit `u` of the ring of series restricted at `b ^ σ` and a
polynomial `P` of degree at most `j`, then the finite slopes of `P` are `j - l` copies of `σ`. -/
theorem newtonSlopes_eq_replicate_of_isFirstBreak [IsUltrametricDist K]
    (hbr : IsFirstBreak (f.newtonPolygon v) σ l j)
    {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u) {P : Polynomial K}
    (hPdeg : P.natDegree ≤ j) (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) :
    P.newtonSlopes v = Multiset.replicate (j - l) σ := by
  have hv0 : ∀ x, v x = ⊤ → x = 0 := fun _ => v.top_iff.mp
  have hfd := (isLowestDominant_and_isDistinguished_of_isFirstBreak_newtonPolygon v hb hv hbr).2
  have hdeg := TauCeti.PowerSeries.natDegree_eq_of_isUnit_mul
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hfd hu hPdeg hmul
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact hfd.ne_zero (by rw [← hmul, Polynomial.coe_zero, mul_zero])
  -- Up to `j`, the Newton polygons of `P` and `f` have the same finite domain, so `P` vanishes at
  -- zero to the same order `l` as `f`.
  have hu0 : v ((u : K⟦X⟧).coeff 0) ≠ ⊤ :=
    v.ne_top_iff.mpr (TauCeti.PowerSeries.isDistinguished_zero_of_isUnit
      (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hu).coeff_ne_zero
  have hne {n : ℕ} (hn : n ≤ j) : P.newtonPolygon v n ≠ ⊤ ↔ f.newtonPolygon v n ≠ ⊤ := by
    rw [newtonPolygon_eq_add_of_isUnit_mul v hb hv hfd hu hPdeg hmul hn, WithTop.add_ne_top,
      and_iff_left hu0]
  have htrail : P.natTrailingDegree = l := by
    have hP := (P.newtonPolygon_ne_top_iff v hv0 hP0 (n := l)).mp
      ((hne hbr.lt.le).mpr hbr.left_ne_top)
    refine le_antisymm hP.1 (Polynomial.le_natTrailingDegree_of_forall_lt_newtonPolygon_eq_top
      (mt (hv0 _) (Polynomial.trailingCoeff_ne_zero.mpr hP0)) fun n hn => ?_)
    by_contra hPn
    exact (hne (hn.trans hbr.lt).le).mp hPn (hbr.eq_top_of_lt n hn)
  have hfr : f.IsRestricted (b ^ σ) := hmul ▸ IsRestricted.mem_subring.mp
    (Subring.mul_mem _ u.2 (IsRestricted.mem_subring.mpr
      (TauCeti.PowerSeries.isRestricted_polynomial P)))
  refine Multiset.eq_replicate.mpr ⟨?_, forall_mem_newtonSlopes_eq_of_isFiniteFace_of_order_eq v hb
    hv hfr (hbr.isFiniteFace (f.isConvexSeq_newtonPolygon v))
    (order_eq_of_isFirstBreak_newtonPolygon hv0 hbr) hu hPdeg hmul⟩
  rw [Polynomial.card_newtonSlopes P v hv0, hdeg, htrail]

end NormedDivisionRing

end PowerSeries

namespace Polynomial

/-- **Pure polynomials.** If the trailing and leading coefficients of `f` have finite valuation,
the Newton polygon of `f` has a first break at the degree of `f`, with slope `σ`, exactly when `f`
is not a monomial and every finite slope of `f` equals `σ`. -/
theorem isFirstBreak_newtonPolygon_natDegree_iff {R : Type*} [Ring R] {f : R[X]}
    {v : AddValuation R (WithTop ℝ)} (htr : v f.trailingCoeff ≠ ⊤) (hld : v f.leadingCoeff ≠ ⊤)
    {σ : ℝ} :
    IsFirstBreak (f.newtonPolygon v) σ f.natTrailingDegree f.natDegree ↔
      f.natTrailingDegree < f.natDegree ∧ ∀ s ∈ f.newtonSlopes v, s = σ := by
  have hedges := f.finiteEdges_newtonPolygon_of_ne_top v htr hld
  constructor
  · intro hbr
    refine ⟨hbr.lt, fun s hs => ?_⟩
    obtain ⟨i, hi, rfl⟩ := (f.mem_newtonSlopes v).mp hs
    rw [hedges, Set.mem_Ico] at hi
    exact hbr.unitSlope_eq i hi.1 hi.2
  · rintro ⟨hlt, hpure⟩
    refine ⟨hlt, fun n hn => f.newtonPolygon_eq_top_of_lt_natTrailingDegree v hn,
      fun n hln hnd => (f.newtonPolygon_ne_top_iff_of_ne_top v htr hld).mpr ⟨hln, hnd⟩,
      fun i hli hid => hpure _ ((f.mem_newtonSlopes v).mpr ⟨i, hedges ▸ ⟨hli, hid⟩, rfl⟩),
      fun h => absurd (f.newtonPolygon_eq_top_of_natDegree_lt v (Nat.lt_succ_self _)) h⟩

/-- At every radius `b ^ σ`, the Newton polygon of a polynomial `p` has a first break at `j` of
slope `σ` starting at `l` exactly when `l < j`, `l` is the order of vanishing of `p` at zero, the
coefficient in degree `l` attains the Gauss norm at `b ^ σ`, and `p` is distinguished of degree `j`
there. -/
theorem isFirstBreak_newtonPolygon_iff {K : Type*} [NormedDivisionRing K] (p : K[X])
    (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (σ : ℝ) {l j : ℕ} :
    IsFirstBreak (p.newtonPolygon v) σ l j ↔ l < j ∧ p.natTrailingDegree = l ∧
      TauCeti.PowerSeries.IsLowestDominant (b ^ σ) l (p : K⟦X⟧) ∧
      TauCeti.PowerSeries.IsDistinguished (b ^ σ) j (p : K⟦X⟧) := by
  have hv0 : ∀ x, v x = ⊤ → x = 0 := fun _ => v.top_iff.mp
  rw [(p.isConvexSeq_newtonPolygon v).isFirstBreak_iff, p.isFiniteFace_newtonPolygon_iff v hb hv σ]
  refine ⟨fun ⟨hlj, hl, hface⟩ => ⟨hlj, ?_, hface⟩, fun ⟨hlj, htrail, hface⟩ =>
    ⟨hlj, fun n hn => p.newtonPolygon_eq_top_of_lt_natTrailingDegree v (htrail ▸ hn), hface⟩⟩
  -- The order of vanishing is the first index where the Newton polygon is finite.
  have hp0 : p ≠ 0 := Polynomial.coe_eq_zero_iff.not.mp hface.2.ne_zero
  exact le_antisymm (natTrailingDegree_le_of_ne_zero (by simpa using hface.1.coeff_ne_zero))
    (le_natTrailingDegree_of_forall_lt_newtonPolygon_eq_top
      (mt (hv0 _) (trailingCoeff_ne_zero.mpr hp0)) hl)

end Polynomial
