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
# The first break of a Newton polygon

The Newton polygon of a polynomial or power series `f` has its first break at `j`, with first
slope `m`, when its first segment runs from the order of vanishing `a` of `f` to `j` with slope
`m`, and the slope strictly increases after `j` (or the polygon ends at `j`). This file reads the
general criterion `TauCeti.IsLowerConvexEnvelope.isFirstBreak_iff` on coefficient valuations and
translates a first break into distinguishedness, so that Weierstrass preparation splits off the
first segment.

In coefficient form, the polygon of a power series has its first break at `j` with slope `m`
exactly when `a < j`, the line of slope `m` through `(a, v (coeff a f))` passes through
`(j, v (coeff j f))` and lies below every coefficient point, and some line of strictly larger
slope through `(j, v (coeff j f))` lies below every later coefficient point. For a polynomial the
last condition says only that every later coefficient point lies strictly above the line of slope
`m`; for a power series this pointwise condition is weaker, since the later coefficient points
may approach the line.

Over a normed division ring whose norm is `‖x‖ = b ^ (-v x)`, a first break at `j` with slope `m`
makes `f` distinguished of degree `j` at the radius `b ^ m`, and makes the order of vanishing its
lowest dominant degree there. When the weighted coefficients are bounded at some larger radius,
the converse holds as well. A first break also makes `f` restricted at `b ^ m`, so over a complete
ultrametric normed field Weierstrass preparation at `b ^ m` writes `f` uniquely as a restricted
unit times a monic polynomial of degree `j`, and that polynomial is pure of slope `m`.

## Main results

* `PowerSeries.isFirstBreak_newtonPolygon_iff` and `Polynomial.isFirstBreak_newtonPolygon_iff`:
  the coefficient-line criteria for a first break.
* `PowerSeries.isFirstBreak_newtonPolygon_iff_isFiniteFace`: a first break at `j` of slope `m` is
  the face of slope `m` from the order of vanishing to `j`.
* `PowerSeries.isLowestDominant_and_isDistinguished_of_isFirstBreak_newtonPolygon`: a first break
  at `j` of slope `m` gives distinguishedness of degree `j` at `b ^ m`, with the order of vanishing
  as lowest dominant degree.
* `PowerSeries.isFirstBreak_newtonPolygon_iff_isLowestDominant_and_isDistinguished`: with bounded
  weighted coefficients at a larger radius, a first break is exactly this pair of active indices.
* `PowerSeries.existsUnique_isUnit_isMonicOfDegree_mul_eq_of_isFirstBreak`: first-segment
  unique factorisation by Weierstrass preparation.
* `PowerSeries.forall_mem_newtonSlopes_eq_of_isFirstBreak`: the polynomial factor is pure of
  the first slope, even without completeness.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 3.
-/

public section

open scoped PowerSeries
open TauCeti

namespace PowerSeries

section Ring

variable {R : Type*} [Ring R] {f : R⟦X⟧} {v : AddValuation R (WithTop ℝ)}

/-- **Coefficient-line criterion for the first break of a Newton polygon.** Let `a` be the order of
vanishing of `f`, with `v (coeff a f)` finite. The Newton polygon of `f` has its first break at
`j` with slope `m` exactly when `a < j`, some line of slope `m` supports the coefficient heights
and passes through the coefficient points at `a` and `j`, and some line of strictly larger slope
`τ` through the coefficient point at `j` lies below every later coefficient point. -/
theorem isFirstBreak_newtonPolygon_iff {a : ℕ} (ha : f.order = a) (hva : v (coeff a f) ≠ ⊤)
    {m : ℝ} {j : ℕ} :
    IsFirstBreak (f.newtonPolygon v) m j ↔ a < j ∧ ∃ c : ℝ,
      IsSupportingLine (fun n ↦ v (coeff n f)) m c ∧
      v (coeff a f) = ((c + m * a : ℝ) : WithTop ℝ) ∧
      v (coeff j f) = ((c + m * j : ℝ) : WithTop ℝ) ∧
      ∃ τ > m, IsSupportingLine (fun n ↦ v (coeff (j + n) f)) τ (c + m * j) := by
  have hpre : ∀ n < a, v (coeff n f) = ⊤ := fun n hn ↦ by
    rw [(order_eq_nat.mp ha).2 n hn, AddValuation.map_zero]
  by_cases hadm : IsAdmissible fun n ↦ v (coeff n f)
  · rw [(f.isLowerConvexEnvelope_newtonPolygon hadm).isFirstBreak_iff hva hpre]
    simp only [mem_supportingFace]
  -- Without an affine lower bound there is neither a polygon nor a supporting line.
  have htop : f.newtonPolygon v = ⊤ := by
    rw [newtonPolygon_def]
    exact lowerConvexEnvelope_of_not_isAdmissible hadm
  refine iff_of_false (fun hb ↦ ?_) fun ⟨_, c, hc, _⟩ ↦ hadm hc.isAdmissible
  exact hb.ne_top (by rw [htop, Pi.top_apply])

/-- The Newton polygon of `f` has its first break at `j` with slope `m` exactly when its face of
slope `m` runs from the order of vanishing `a < j` of `f` to `j`. Here `v` is finite on the
coefficient at `a`, as for any valuation on a division ring. -/
theorem isFirstBreak_newtonPolygon_iff_isFiniteFace {a : ℕ} (ha : f.order = a)
    (hva : v (coeff a f) ≠ ⊤) {m : ℝ} {j : ℕ} : IsFirstBreak (f.newtonPolygon v) m j ↔
      a < j ∧ IsFiniteFace (f.newtonPolygon v) m a j := by
  rw [(f.isConvexSeq_newtonPolygon v).isFirstBreak_iff_isFiniteFace]
  refine ⟨fun ⟨a', ha'j, hpre, hface⟩ ↦ ?_, fun ⟨haj, hface⟩ ↦ ⟨a, haj, fun n hn ↦
    f.newtonPolygon_eq_top_of_lt_order v (ha ▸ by exact_mod_cast hn), hface⟩⟩
  have hadm : IsAdmissible fun n ↦ v (coeff n f) :=
    isAdmissible_of_lowerConvexEnvelope_ne_top (f.newtonPolygon_def v ▸ hface.left_ne_top)
  -- The face starts at the order of vanishing, the first finite point of the polygon.
  have hfa : f.newtonPolygon v a ≠ ⊤ := by
    rwa [f.newtonPolygon_eq_of_order_eq v hadm ha]
  obtain rfl : a' = a := le_antisymm (not_lt.mp fun h ↦ hfa (hpre a h))
    (not_lt.mp fun h ↦ hface.left_ne_top
      (f.newtonPolygon_eq_top_of_lt_order v (ha ▸ by exact_mod_cast h)))
  exact ⟨ha'j, hface⟩

end Ring

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K] {f : K⟦X⟧}
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- A first break makes the series restricted at the radius of its first slope. -/
theorem isRestricted_of_isFirstBreak_newtonPolygon {m : ℝ} {j : ℕ}
    (hbr : IsFirstBreak (f.newtonPolygon v) m j) : f.IsRestricted (b ^ m) := by
  obtain ⟨a, -, -, hface⟩ :=
    (f.isConvexSeq_newtonPolygon v).isFirstBreak_iff_isFiniteFace.mp hbr
  exact isRestricted_of_isFiniteFace_newtonPolygon f v hb hv hface

/-- **A first break gives distinguishedness.** If the Newton polygon of `f` has its first break at
`j` with slope `m`, then at the radius `b ^ m` the series `f` is distinguished of degree `j`, and
its order of vanishing `a` is its lowest dominant degree. No restrictedness is needed: the
supporting line of slope `m` already bounds the weighted coefficients at `b ^ m`. -/
theorem isLowestDominant_and_isDistinguished_of_isFirstBreak_newtonPolygon {a : ℕ}
    (ha : f.order = a) {m : ℝ} {j : ℕ} (hbr : IsFirstBreak (f.newtonPolygon v) m j) :
    TauCeti.PowerSeries.IsLowestDominant (b ^ m) a f ∧
      TauCeti.PowerSeries.IsDistinguished (b ^ m) j f := by
  obtain ⟨-, hface⟩ := (isFirstBreak_newtonPolygon_iff_isFiniteFace ha
    (v.ne_top_iff.mpr (order_eq_nat.mp ha).1)).mp hbr
  exact isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv hface

/-- **First breaks as active indices.** Suppose the weighted coefficients of `f` are bounded at a
radius `b ^ τ` with `m < τ`, and let `a` be the order of vanishing of `f`. Then the
Newton polygon of `f` has its first break at `j` with slope `m` exactly when, at the radius
`b ^ m`, `a < j`, the order of vanishing is the lowest dominant degree of `f`, and `f` is
distinguished of degree `j`. The larger radius is needed: at a convergence boundary the last
dominant coefficient can lie on a polygon ray of slope `m` that continues past it. -/
theorem isFirstBreak_newtonPolygon_iff_isLowestDominant_and_isDistinguished {τ : ℝ}
    (hf : f.HasGaussNorm norm (b ^ τ)) {m : ℝ} (hmτ : m < τ) {a j : ℕ} (ha : f.order = a) :
    IsFirstBreak (f.newtonPolygon v) m j ↔ a < j ∧
      TauCeti.PowerSeries.IsLowestDominant (b ^ m) a f ∧
        TauCeti.PowerSeries.IsDistinguished (b ^ m) j f := by
  rw [isFirstBreak_newtonPolygon_iff_isFiniteFace ha (v.ne_top_iff.mpr (order_eq_nat.mp ha).1),
    isFiniteFace_newtonPolygon_iff f v hb hv hf hmτ]

/-- Every polynomial factor of degree at most the first break, with a restricted unit as
cofactor at the first-slope radius, is pure of that slope. -/
theorem forall_mem_newtonSlopes_eq_of_isFirstBreak [IsUltrametricDist K] {m : ℝ} {j : ℕ}
    (hbr : IsFirstBreak (f.newtonPolygon v) m j)
    {u : IsRestricted.subring (R := K) (b ^ m)} (hu : IsUnit u)
    {P : Polynomial K} (hPdeg : P.natDegree ≤ j) (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) :
    ∀ s ∈ P.newtonSlopes v, s = m := by
  have hf0 : f ≠ 0 := fun hf ↦ hbr.ne_top (by simp [hf])
  have ha : f.order = f.order.toNat := (ENat.natCast_toNat (order_eq_top.not.mpr hf0)).symm
  obtain ⟨-, hface⟩ := (isFirstBreak_newtonPolygon_iff_isFiniteFace ha
    (v.ne_top_iff.mpr (order_eq_nat.mp ha).1)).mp hbr
  exact forall_mem_newtonSlopes_eq_of_isFiniteFace_of_order_eq v hb hv
    (isRestricted_of_isFirstBreak_newtonPolygon v hb hv hbr) hface ha hu hPdeg hmul

end NormedDivisionRing

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {f : K⟦X⟧}
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **First-segment factorisation.** Over a complete ultrametric normed field, suppose the Newton
polygon of `f` has its first break at `j` with slope `m`. Then `f` is in exactly one way a unit of
the ring of series restricted at `b ^ m` times a monic polynomial of degree `j`. Purity of
this polynomial follows from `forall_mem_newtonSlopes_eq_of_isFirstBreak`. The series
is automatically restricted at `b ^ m`, since its polygon has a supporting line of strictly larger
slope after the break. -/
theorem existsUnique_isUnit_isMonicOfDegree_mul_eq_of_isFirstBreak {m : ℝ} {j : ℕ}
    (hbr : IsFirstBreak (f.newtonPolygon v) m j) :
    ∃! p : IsRestricted.subring (R := K) (b ^ m) × Polynomial K,
      IsUnit p.1 ∧ p.2.IsMonicOfDegree j ∧ (p.1 : K⟦X⟧) * (p.2 : K⟦X⟧) = f := by
  obtain ⟨a, -, -, hface⟩ :=
    (f.isConvexSeq_newtonPolygon v).isFirstBreak_iff_isFiniteFace.mp hbr
  have hfr := isRestricted_of_isFiniteFace_newtonPolygon f v hb hv hface
  have hfd := isDistinguished_of_isFiniteFace v hb hv hfr hface
  exact hfd.existsUnique_isUnit_isMonicOfDegree_mul_eq hfd.coeff_ne_zero.isUnit
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) m) hfr

end NormedField

end PowerSeries

namespace Polynomial

variable {R : Type*} [Ring R] {f : R[X]} {v : AddValuation R (WithTop ℝ)}

/-- **Coefficient-line criterion for the first break of the Newton polygon of a polynomial.** Let
`a` be the order of vanishing of `f`, with `v` finite on the trailing coefficient. The Newton
polygon of `f` has its first break at `j` with slope `m` exactly when `a < j` and some line of
slope `m` supports the coefficient heights, passes through the coefficient points at `a` and `j`,
and lies strictly below every coefficient point after `j`. Unlike for power series, no line of
strictly larger slope needs to be exhibited. -/
theorem isFirstBreak_newtonPolygon_iff (htr : v f.trailingCoeff ≠ ⊤) {m : ℝ} {j : ℕ} :
    IsFirstBreak (f.newtonPolygon v) m j ↔ f.natTrailingDegree < j ∧ ∃ c : ℝ,
      IsSupportingLine (fun n ↦ v (f.coeff n)) m c ∧
      v f.trailingCoeff = ((c + m * f.natTrailingDegree : ℝ) : WithTop ℝ) ∧
      v (f.coeff j) = ((c + m * j : ℝ) : WithTop ℝ) ∧
      ∀ n, j < n → ((c + m * n : ℝ) : WithTop ℝ) < v (f.coeff n) := by
  rw [(f.isLowerConvexEnvelope_newtonPolygon v).isFirstBreak_iff_of_finite
    (f.finite_setOf_addValuation_coeff_ne_top v) htr fun n hn ↦ by
      rw [coeff_eq_zero_of_lt_natTrailingDegree hn, AddValuation.map_zero]]
  simp only [mem_supportingFace, trailingCoeff]

/-- A polynomial has its first break at `j` of slope `m` exactly when its face of slope `m`
runs from its trailing degree to `j`, with positive width. -/
theorem isFirstBreak_newtonPolygon_iff_isFiniteFace (htr : v f.trailingCoeff ≠ ⊤)
    {m : ℝ} {j : ℕ} :
    IsFirstBreak (f.newtonPolygon v) m j ↔
      f.natTrailingDegree < j ∧ IsFiniteFace (f.newtonPolygon v) m f.natTrailingDegree j := by
  rw [(f.isConvexSeq_newtonPolygon v).isFirstBreak_iff_isFiniteFace]
  refine ⟨fun ⟨a, haj, hpre, hface⟩ ↦ ?_, fun ⟨haj, hface⟩ ↦
    ⟨f.natTrailingDegree, haj, fun n hn ↦ f.newtonPolygon_eq_top_of_lt_natTrailingDegree v hn,
      hface⟩⟩
  obtain rfl : a = f.natTrailingDegree := le_antisymm
    (not_lt.mp fun h ↦ htr (by simpa using hpre f.natTrailingDegree h))
    (not_lt.mp fun h ↦ hface.left_ne_top (f.newtonPolygon_eq_top_of_lt_natTrailingDegree v h))
  exact ⟨haj, hface⟩

/-- The terminal endpoint is a first break of slope `m` exactly when the Newton polygon has
positive width and all its finite slopes equal `m`. -/
theorem isFirstBreak_newtonPolygon_natDegree_iff (htr : v f.trailingCoeff ≠ ⊤)
    (hld : v f.leadingCoeff ≠ ⊤) {m : ℝ} :
    IsFirstBreak (f.newtonPolygon v) m f.natDegree ↔
      f.natTrailingDegree < f.natDegree ∧ ∀ s ∈ f.newtonSlopes v, s = m := by
  constructor
  · intro hbr
    obtain ⟨haj, hface⟩ := (isFirstBreak_newtonPolygon_iff_isFiniteFace htr).mp hbr
    refine ⟨haj, fun s hs ↦ ?_⟩
    obtain ⟨i, hi, rfl⟩ := (f.mem_newtonSlopes v).mp hs
    rw [f.finiteEdges_newtonPolygon_of_ne_top v htr hld] at hi
    exact hface.unitSlope_eq hi.1 hi.2
  · rintro ⟨haj, hpure⟩
    refine isFirstBreak_iff.mpr ⟨f.natTrailingDegree, haj,
      fun n hn ↦ f.newtonPolygon_eq_top_of_lt_natTrailingDegree v hn, fun i hi ↦ ?_, ?_⟩
    · have hedge : i ∈ finiteEdges (f.newtonPolygon v) := by
        rwa [f.finiteEdges_newtonPolygon_of_ne_top v htr hld]
      exact ⟨hedge, hpure _ ((f.mem_newtonSlopes v).mpr ⟨i, hedge, rfl⟩)⟩
    · intro hedge
      rw [f.finiteEdges_newtonPolygon_of_ne_top v htr hld] at hedge
      exact (lt_irrefl _ hedge.2).elim

/-- At every radius, a polynomial has its first break at `j` of slope `m` exactly when the
trailing degree is strictly below `j` and these are its first and last active indices. -/
theorem isFirstBreak_newtonPolygon_iff_isLowestDominant_and_isDistinguished
    {K : Type*} [NormedDivisionRing K] (f : K[X]) (v : AddValuation K (WithTop ℝ))
    {b : ℝ} (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {m : ℝ} {j : ℕ} :
    IsFirstBreak (f.newtonPolygon v) m j ↔ f.natTrailingDegree < j ∧
      TauCeti.PowerSeries.IsLowestDominant (b ^ m) f.natTrailingDegree (f : K⟦X⟧) ∧
      TauCeti.PowerSeries.IsDistinguished (b ^ m) j (f : K⟦X⟧) := by
  by_cases hf : f = 0
  · subst f
    constructor
    · intro hbr
      exact (hbr.ne_top (by simp)).elim
    · rintro ⟨-, hl, -⟩
      exact (hl.ne_zero (by simp)).elim
  rw [isFirstBreak_newtonPolygon_iff_isFiniteFace
    (v.ne_top_iff.mpr (trailingCoeff_ne_zero.mpr hf)),
    isFiniteFace_newtonPolygon_iff f v hb hv]

end Polynomial
