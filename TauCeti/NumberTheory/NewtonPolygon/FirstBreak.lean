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

The Newton polygon of a power series `f = ∑ aₙ Xⁿ` of order `i` begins at the point
`(i, v aᵢ)`. It has a *first break* at `j` with slope `σ` (`TauCeti.IsFirstBreak`) when its
first segment has slope `σ` and ends at `j`, where the slope genuinely increases or the polygon
ends. This file reads first breaks off the coefficients, in three forms.

* **Coefficient lines.** The polygon has a first break at `j` with slope `σ` exactly when
  `i < j`, every coefficient lies on or above the line of slope `σ` through `(i, v aᵢ)`, the
  coefficient `aⱼ` lies on that line, and the coefficients after `j` lie above a line of some
  strictly larger slope through `(j, v aⱼ)`
  (`PowerSeries.isFirstBreak_newtonPolygon_iff`). For infinitely many points, lying strictly
  above the first line after `j` is not enough for the last condition
  (`TauCeti.exists_supportingFace_eq_Icc_and_not_isFirstBreak`).
* **Gauss norms.** When the norm comes from `v` with base `b > 1`, so that
  `‖x‖ = b ^ (-v x)` for `x ≠ 0`, the polygon has a first break at `j` with slope `σ` exactly when
  `i < j`, the weighted coefficient norms are bounded at some radius larger than `b ^ σ`, and at
  the radius `b ^ σ` the coefficients `aᵢ` and `aⱼ` are the first and the last to attain the Gauss
  norm, that is, `f` is distinguished of degree `j` there
  (`PowerSeries.isFirstBreak_newtonPolygon_iff_isLowestDominant_and_isDistinguished`).
  In particular `f` is restricted at `b ^ σ`.
* **Weierstrass preparation.** Over a complete field, a first break at `j` with slope `σ` splits
  off the first segment: `f = e * ω` with `e` a unit of the ring of series restricted at `b ^ σ`
  and `ω` a monic polynomial of degree `j` all of whose finite Newton slopes equal `σ`
  (`PowerSeries.exists_isUnit_isMonicOfDegree_mul_eq_of_isFirstBreak`).

For a polynomial with `natTrailingDegree < natDegree`, a first break at its degree is the same as
purity: the first segment is the whole polygon
(`Polynomial.isFirstBreak_newtonPolygon_natDegree_iff`).

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

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ)) {f : R⟦X⟧}

/-- For a power series of order `i`, a first break of its Newton polygon at `j` with slope `σ` is a
finite face of slope `σ` from `i` to `j` with `i < j`. Only zero has infinite valuation. -/
theorem isFirstBreak_newtonPolygon_iff_isFiniteFace (hv0 : ∀ x, v x = ⊤ → x = 0) {i : ℕ}
    (hord : f.order = i) {σ : ℝ} {j : ℕ} :
    IsFirstBreak (f.newtonPolygon v) σ j ↔ i < j ∧ IsFiniteFace (f.newtonPolygon v) σ i j := by
  have hfirst : ∀ n < i, f.newtonPolygon v n = ⊤ := fun n hn =>
    f.newtonPolygon_eq_top_of_lt_order v (by rw [hord]; exact_mod_cast hn)
  refine ⟨fun hb => ?_, fun ⟨hij, hface⟩ =>
    ((f.isConvexSeq_newtonPolygon v).isFirstBreak_iff_isFiniteFace hface.left_ne_top
      hfirst).mpr ⟨hij, hface⟩⟩
  have hadm : IsAdmissible fun n => v (coeff n f) :=
    isAdmissible_of_lowerConvexEnvelope_ne_top (f.newtonPolygon_def v ▸ hb.ne_top)
  have hi : f.newtonPolygon v i ≠ ⊤ := by
    rw [newtonPolygon_eq_of_order_eq v hadm hord]
    exact mt (hv0 _) (order_eq_nat.mp hord).1
  exact ((f.isConvexSeq_newtonPolygon v).isFirstBreak_iff_isFiniteFace hi hfirst).mp hb

/-- **First-break criterion for Newton polygons.** Let `f` have order `i`. Its Newton polygon has a
first break at `j` with slope `σ` exactly when `i < j`, every coefficient lies on or above the line
of slope `σ` through `(i, v (coeff i f))`, the coefficient of index `j` lies on that line, and
every coefficient after `j` lies above a line of some strictly larger slope `τ` through
`(j, v (coeff j f))`. Only zero has infinite valuation. -/
theorem isFirstBreak_newtonPolygon_iff (hv0 : ∀ x, v x = ⊤ → x = 0) {i : ℕ}
    (hord : f.order = i) {σ : ℝ} {j : ℕ} :
    IsFirstBreak (f.newtonPolygon v) σ j ↔
      i < j ∧ IsSupportingLine (fun n => v (coeff n f)) σ ((v (coeff i f)).untop₀ - σ * i) ∧
        v (coeff j f) = (((v (coeff i f)).untop₀ + σ * ((j : ℝ) - i) : ℝ) : WithTop ℝ) ∧
        ∃ τ, σ < τ ∧ ∀ n, j ≤ n →
          (((v (coeff j f)).untop₀ + τ * ((n : ℝ) - j) : ℝ) : WithTop ℝ) ≤ v (coeff n f) := by
  obtain ⟨hi, hfirst⟩ := order_eq_nat.mp hord
  rw [newtonPolygon_def]
  exact isFirstBreak_lowerConvexEnvelope_iff (a := fun n => v (coeff n f)) (mt (hv0 _) hi)
    fun n hn => by rw [hfirst n hn, AddValuation.map_zero]

end Ring

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K] (v : AddValuation K (WithTop ℝ)) {b : ℝ}
  (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K⟦X⟧} {σ : ℝ} {j : ℕ}

include hb hv

/-- At a first break of slope `σ`, the weighted coefficient norms are bounded at some radius
strictly larger than `b ^ σ`. -/
theorem exists_lt_hasGaussNorm_of_isFirstBreak (hbrk : IsFirstBreak (f.newtonPolygon v) σ j) :
    ∃ τ, σ < τ ∧ f.HasGaussNorm norm (b ^ τ) := by
  have hadm : IsAdmissible fun n => v (coeff n f) :=
    isAdmissible_of_lowerConvexEnvelope_ne_top (f.newtonPolygon_def v ▸ hbrk.ne_top)
  obtain ⟨τ, hστ, hτ⟩ := hbrk.exists_lt_isSupportingLine (f.isConvexSeq_newtonPolygon v)
  have hcoeff := (isLowerConvexEnvelope_newtonPolygon hadm).isSupportingLine_iff.mp hτ
  exact ⟨τ, hστ, (hasGaussNorm_iff_supportingValue_ne_bot f v hb hv τ).mpr
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (isSupportingLine_iff.mp hcoeff))⟩

/-- A series whose Newton polygon has a first break of slope `σ` is restricted at `b ^ σ`. -/
theorem isRestricted_of_isFirstBreak (hbrk : IsFirstBreak (f.newtonPolygon v) σ j) :
    f.IsRestricted (b ^ σ) := by
  obtain ⟨τ, hστ, hG⟩ := exists_lt_hasGaussNorm_of_isFirstBreak v hb hv hbrk
  exact hG.isRestricted_of_abs_lt
    ((abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ)).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hb hστ))

/-- **First breaks in Gauss form.** Let `f` have order `i`. Its Newton polygon has a first break at
`j` with slope `σ` exactly when `i < j`, the weighted coefficient norms are bounded at some radius
larger than `b ^ σ`, and at the radius `b ^ σ` the coefficients of indices `i` and `j` are the first
and the last to attain the Gauss norm. -/
theorem isFirstBreak_newtonPolygon_iff_isLowestDominant_and_isDistinguished {i : ℕ}
    (hord : f.order = i) :
    IsFirstBreak (f.newtonPolygon v) σ j ↔
      i < j ∧ (∃ τ, σ < τ ∧ f.HasGaussNorm norm (b ^ τ)) ∧
        TauCeti.PowerSeries.IsLowestDominant (b ^ σ) i f ∧
        TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f := by
  rw [isFirstBreak_newtonPolygon_iff_isFiniteFace v (fun _ => v.top_iff.mp) hord]
  constructor
  · rintro ⟨hij, hface⟩
    obtain ⟨τ, hστ, hG⟩ := exists_lt_hasGaussNorm_of_isFirstBreak v hb hv
      (((f.isConvexSeq_newtonPolygon v).isFirstBreak_iff_isFiniteFace hface.left_ne_top
        fun n hn => f.newtonPolygon_eq_top_of_lt_order v (by rw [hord]; exact_mod_cast hn)).mpr
        ⟨hij, hface⟩)
    exact ⟨hij, ⟨τ, hστ, hG⟩, (isFiniteFace_newtonPolygon_iff f v hb hv hG hστ).mp hface⟩
  · rintro ⟨hij, ⟨τ, hστ, hG⟩, hl, hu⟩
    exact ⟨hij, (isFiniteFace_newtonPolygon_iff f v hb hv hG hστ).mpr ⟨hl, hu⟩⟩

end NormedDivisionRing

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Factorisation at the first break.** Over a complete ultrametric field, a series whose Newton
polygon has a first break at `j` with slope `σ` is a unit of the ring of series restricted at
`b ^ σ` times a monic polynomial of degree `j` all of whose finite Newton slopes equal `σ`. -/
theorem exists_isUnit_isMonicOfDegree_mul_eq_of_isFirstBreak {f : K⟦X⟧} {σ : ℝ} {j : ℕ}
    (hbrk : IsFirstBreak (f.newtonPolygon v) σ j) :
    ∃ (e : IsRestricted.subring (R := K) (b ^ σ)) (ω : Polynomial K), IsUnit e ∧
      ω.IsMonicOfDegree j ∧ (e : K⟦X⟧) * (ω : K⟦X⟧) = f ∧ ∀ m ∈ ω.newtonSlopes v, m = σ := by
  have hr := isRestricted_of_isFirstBreak v hb hv hbrk
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hbrk.ne_top (by simp)
  have hord : f.order = f.order.toNat := (ENat.natCast_toNat (order_eq_top.not.mpr hf0)).symm
  obtain ⟨-, hface⟩ :=
    (isFirstBreak_newtonPolygon_iff_isFiniteFace v (fun _ => v.top_iff.mp) hord).mp hbrk
  have hd := isDistinguished_of_isFiniteFace v hb hv hr hface
  have hadm : IsAdmissible fun n => v (coeff n f) :=
    isAdmissible_of_lowerConvexEnvelope_ne_top (f.newtonPolygon_def v ▸ hbrk.ne_top)
  have hj : coeff j f ≠ 0 := by
    have hfin := hface.right_ne_top
    rw [(isLowerConvexEnvelope_newtonPolygon hadm).eq_right_of_isFiniteFace hface] at hfin
    exact v.ne_top_iff.mp hfin
  obtain ⟨e, ω, he, hω, heq⟩ := hd.exists_isUnit_isMonicOfDegree_mul_eq hj.isUnit
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hr
  exact ⟨e, ω, he, hω, heq, forall_mem_newtonSlopes_eq_of_isFiniteFace_of_order_eq v hb hv hr
    hface hord he hω.natDegree_eq.le heq⟩

end NormedField

end PowerSeries

namespace Polynomial

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ))

/-- A polynomial with `natTrailingDegree < natDegree` has a first break at its degree with slope `σ`
exactly when it is pure of slope `σ`: the first segment is then the whole Newton polygon. Only zero
has infinite valuation. -/
theorem isFirstBreak_newtonPolygon_natDegree_iff (hv0 : ∀ x, v x = ⊤ → x = 0) {f : R[X]}
    (hf : f.natTrailingDegree < f.natDegree) {σ : ℝ} :
    IsFirstBreak (f.newtonPolygon v) σ f.natDegree ↔ ∀ m ∈ f.newtonSlopes v, m = σ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  have hdom (n : ℕ) := f.newtonPolygon_ne_top_iff v hv0 hf0 (n := n)
  rw [isFirstBreak_iff]
  constructor
  · rintro ⟨i, -, hfirst, hseg, -⟩ m hm
    obtain ⟨n, hn, rfl⟩ := (f.mem_newtonSlopes v).mp hm
    have hn' := mem_finiteEdges.mp hn
    exact (hseg n (le_of_not_gt fun hni => hn'.1 (hfirst n hni))
      (by have := ((hdom (n + 1)).mp hn'.2).2; omega)).2
  · intro hpure
    refine ⟨f.natTrailingDegree, hf,
      fun n hn => not_ne_iff.mp fun hn' => ((hdom n).mp hn').1.not_gt hn,
      fun n hn hnd => ?_, fun hd => ?_⟩
    · have hedge : n ∈ finiteEdges (f.newtonPolygon v) :=
        mem_finiteEdges.mpr ⟨(hdom n).mpr ⟨hn, hnd.le⟩, (hdom (n + 1)).mpr ⟨by omega, hnd⟩⟩
      exact ⟨hedge, hpure _ ((f.mem_newtonSlopes v).mpr ⟨n, hedge, rfl⟩)⟩
    · have := ((hdom (f.natDegree + 1)).mp (mem_finiteEdges.mp hd).2).2
      omega

end Polynomial
