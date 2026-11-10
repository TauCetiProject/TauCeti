/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.GaussNorm
public import TauCeti.NumberTheory.NewtonPolygon.Mul
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
import TauCeti.Analysis.Convex.Sequence.Vertex
import TauCeti.RingTheory.PowerSeries.Weierstrass.Polynomial

/-!
# Newton polygons under Weierstrass preparation

Let `K` be an ultrametric normed division ring (or field) whose norm comes from a real additive
valuation `v` with base `b > 1`, so `‖x‖ = b ^ (-v x)` for `x ≠ 0`. Weierstrass preparation on the
closed disc of radius `b ^ σ` relates the Newton polygon of a series `f` up to its distinguished
degree `j` to the Newton polygon of its polynomial factor `P`.

When `f` is distinguished of degree `j` at `b ^ σ`, `u` is a unit of the ring of series restricted
at `b ^ σ`, and `u * P = f` for a polynomial `P` of degree at most `j`, the polynomial `P` has
exact degree `j`, no outgoing finite edge at `j`, and up to the vertical shift `v (u.coeff 0)` the
same Newton polygon as `f` at every index `n ≤ j`:
`f.newtonPolygon v n = P.newtonPolygon v n + v (u.coeff 0)`.
Consequently the finite unit edges of `P` are the finite unit edges of `f` strictly below `j`, with
identical unit slopes, and every finite Newton slope of `P` is at most `σ`. Global Minkowski
additivity need not hold for a series restricted on only a single disc, so heights up to `j` are
reconstructed from supporting values at slopes `τ ≤ σ`, where `u` remains distinguished of degree
`0`.

Conversely, a series restricted at `b ^ σ` whose Newton polygon has a finite face of slope `σ`
ending at `j` touches its supporting line at the right endpoint `j` and is therefore distinguished
of degree `j` at `b ^ σ`. When that face begins at the order of vanishing of `f`, every finite
slope of `P` equals `σ`, giving the first-segment pure-polynomial case.

## Main results

* `Polynomial.Monic.isDistinguished_iff_forall_mem_newtonSlopes_le`: a monic polynomial `ω` is
  distinguished in its full degree at `b ^ σ` if and only if all of its finite Newton slopes are at
  most `σ`.
* `PowerSeries.isDistinguished_of_isFiniteFace`: a series restricted at `b ^ σ` whose Newton
  polygon has a finite face of slope `σ` ending at `j` is distinguished of degree `j` at `b ^ σ`.
* `PowerSeries.newtonPolygon_eq_add_of_isUnit_mul` and
  `PowerSeries.newtonPolygon_eq_of_mul_isUnit`: `f.newtonPolygon v n = P.newtonPolygon v n +
  v (u.coeff 0)` for `n ≤ j`, reducing to equality when `v (u.coeff 0) = 0`.
* `PowerSeries.notMem_finiteEdges_newtonPolygon_of_isUnit_mul`,
  `PowerSeries.mem_finiteEdges_newtonPolygon_iff_of_isUnit_mul` and
  `PowerSeries.unitSlope_newtonPolygon_eq_of_isUnit_mul`: `P` has no outgoing finite edge at `j`
  and matches the finite unit edges and slopes of `f` strictly below `j`.
* `PowerSeries.forall_mem_newtonSlopes_eq_of_isFiniteFace_of_order_eq` and
  `Polynomial.newtonSlopes_eq_filter_le_of_isFiniteFace`: when a finite face of slope `σ` runs from
  the order of vanishing of `f` to `j`, any prepared polynomial factor `P` of degree at most `j` is
  pure of slope `σ`; for a polynomial `f`, any factor `P` prepared at a finite face `(l, j)` of
  slope `σ` has finite slope multiset `(f.newtonSlopes v).filter (· ≤ σ)`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer, 1984,
  §5.2.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 3.
-/

public section

open scoped PowerSeries
open TauCeti

namespace Polynomial

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- Every finite Newton slope of a polynomial `P` distinguished in its full degree at `b ^ σ` is at
most `σ`. -/
theorem le_of_mem_newtonSlopes_of_isDistinguished {P : K[X]} {σ : ℝ}
    (hPd : TauCeti.PowerSeries.IsDistinguished (b ^ σ) P.natDegree (P : K⟦X⟧))
    {m : ℝ} (hm : m ∈ P.newtonSlopes v) : m ≤ σ := by
  have hP0 : (P : K⟦X⟧) ≠ 0 := hPd.ne_zero
  have hfn := hPd.hasGaussNorm
  set c := -Real.logb b ((P : K⟦X⟧).gaussNorm norm (b ^ σ))
  have hc_coeff : IsSupportingLine (fun n => v ((P : K⟦X⟧).coeff n)) σ c :=
    isSupportingLine_iff.mpr (PowerSeries.supportingValue_addValuation_coeff_eq_neg_logb_gaussNorm
      (P : K⟦X⟧) v hb hv hfn hP0).ge
  have hj_coeff : P.natDegree ∈ supportingFace (fun n => v ((P : K⟦X⟧).coeff n)) σ c :=
    ((PowerSeries.isDistinguished_iff_isGreatest_supportingFace (P : K⟦X⟧) v hb hv hfn
      P.natDegree).mp hPd).1
  have henv := P.isLowerConvexEnvelope_newtonPolygon v
  have hc_poly : IsSupportingLine (P.newtonPolygon v) σ c := by
    rw [isSupportingLine_iff, P.supportingValue_newtonPolygon v]
    exact isSupportingLine_iff.mp (by simpa only [coeff_coe] using hc_coeff)
  have hj_poly : P.natDegree ∈ supportingFace (P.newtonPolygon v) σ c :=
    henv.supportingFace_subset (by simpa only [coeff_coe] using hc_coeff)
      (by simpa only [coeff_coe] using hj_coeff)
  obtain ⟨i, hi, rfl⟩ := (P.mem_newtonSlopes v).mp hm
  have hij : i < P.natDegree := lt_of_not_ge fun h =>
    (mem_finiteEdges.mp hi).2 (P.newtonPolygon_eq_top_of_natDegree_lt v (by omega))
  have hj_ne : P.newtonPolygon v P.natDegree ≠ ⊤ := by
    rw [mem_supportingFace.mp hj_poly]
    exact WithTop.coe_ne_top
  have hprev : P.newtonPolygon v (P.natDegree - 1) ≠ ⊤ :=
    (P.isConvexSeq_newtonPolygon v).ne_top_of_le_of_le (mem_finiteEdges.mp hi).1 hj_ne
      (by omega) (by omega)
  have hlast : unitSlope (P.newtonPolygon v) (P.natDegree - 1) ≤ σ := by
    have hline : IsSupportingLine (P.newtonPolygon v) σ
        ((P.newtonPolygon v P.natDegree).untop₀ - σ * P.natDegree) := by
      rw [mem_supportingFace.mp hj_poly, WithTop.untop₀_coe, add_sub_cancel_right]
      exact hc_poly
    exact (((P.isConvexSeq_newtonPolygon v).isSupportingLine_iff_unitSlope hj_ne σ).mp hline).1
      (P.natDegree - 1) (by omega) hprev
  exact ((P.isConvexSeq_newtonPolygon v).monotoneOn hi (mem_finiteEdges.mpr
    ⟨hprev, by rwa [Nat.sub_add_cancel (by omega)]⟩) (by omega)).trans hlast

/-- A monic polynomial `ω` is distinguished of degree `ω.natDegree` at `b ^ σ` if and only if all of
its finite Newton slopes are at most `σ`. -/
theorem Monic.isDistinguished_iff_forall_mem_newtonSlopes_le {ω : K[X]} (hω : ω.Monic) {σ : ℝ} :
    TauCeti.PowerSeries.IsDistinguished (b ^ σ) ω.natDegree (ω : K⟦X⟧) ↔
      ∀ s ∈ ω.newtonSlopes v, s ≤ σ := by
  refine ⟨fun h _ hs => le_of_mem_newtonSlopes_of_isDistinguished v hb hv h hs, fun hslopes => ?_⟩
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos hb0 σ
  rw [TauCeti.PowerSeries.isDistinguished_iff_of_isMonicOfDegree hc ⟨rfl, hω⟩]
  intro k _
  have hn_top : ω.newtonPolygon v ω.natDegree ≠ ⊤ := by
    rw [ω.newtonPolygon_natDegree v, hω.leadingCoeff, v.map_one]
    exact WithTop.zero_ne_top
  have hline : IsSupportingLine (ω.newtonPolygon v) σ (-σ * ω.natDegree) := by
    have h0 : (ω.newtonPolygon v ω.natDegree).untop₀ - σ * ω.natDegree = -σ * ω.natDegree := by
      rw [ω.newtonPolygon_natDegree v, hω.leadingCoeff, v.map_one, WithTop.untop₀_zero, zero_sub,
        neg_mul]
    rw [← h0, (ω.isConvexSeq_newtonPolygon v).isSupportingLine_iff_unitSlope hn_top σ]
    exact ⟨fun i hi hif => hslopes _ ((ω.mem_newtonSlopes v).mpr
      ⟨i, mem_finiteEdges.mpr ⟨hif, hi ▸ hn_top⟩, rfl⟩),
      fun hn' => False.elim (hn' (ω.newtonPolygon_eq_top_of_natDegree_lt v (by omega)))⟩
  have hk_le : (((-σ * ω.natDegree + σ * k : ℝ) : WithTop ℝ)) ≤ v ((ω : K⟦X⟧).coeff k) := by
    rw [coeff_coe]
    exact (isSupportingLine_iff_forall.mp hline k).trans (ω.newtonPolygon_le v k)
  have hbound :=
    (PowerSeries.norm_coeff_mul_rpow_pow_le_iff (ω : K⟦X⟧) v hb hv k σ (-σ * ω.natDegree)).mpr
      hk_le
  rwa [coeff_coe, neg_mul, neg_neg, Real.rpow_mul hb0.le, Real.rpow_natCast] at hbound

end NormedDivisionRing

end Polynomial

namespace PowerSeries

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

/-- A polynomial factor `P` prepared at distinguished degree `j` has no outgoing finite edge at
`j`. -/
theorem notMem_finiteEdges_newtonPolygon_of_isUnit_mul [IsUltrametricDist K] {f : K⟦X⟧} {c : ℝ}
    (hc : 0 < c) {j : ℕ} (hf : TauCeti.PowerSeries.IsDistinguished c j f)
    {u : IsRestricted.subring (R := K) c} (hu : IsUnit u) {P : Polynomial K}
    (hPdeg : P.natDegree ≤ j) (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) :
    j ∉ finiteEdges (P.newtonPolygon v) := by
  intro hj
  have hdeg := TauCeti.PowerSeries.natDegree_eq_of_isUnit_mul hc hf hu hPdeg hmul
  exact (mem_finiteEdges.mp hj).2 (P.newtonPolygon_eq_top_of_natDegree_lt v (by omega))

section Valuation

include hb hv

/-- A power series restricted at `b ^ σ` whose Newton polygon has a finite face of slope `σ` ending
at `j` is distinguished of degree `j` at `b ^ σ`. -/
theorem isDistinguished_of_isFiniteFace {f : K⟦X⟧} {σ : ℝ} {l j : ℕ}
    (hfr : f.IsRestricted (b ^ σ)) (hface : IsFiniteFace (f.newtonPolygon v) σ l j) :
    TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hface.right_ne_top (by simp)
  have hfn := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hfr
  have hadm : IsAdmissible (fun n => v (f.coeff n)) :=
    isAdmissible_iff_exists_supportingValue_ne_bot.mpr
      ⟨σ, (hasGaussNorm_iff_supportingValue_ne_bot f v hb hv σ).mp hfn⟩
  have henv := f.isLowerConvexEnvelope_newtonPolygon hadm
  obtain ⟨c, hc_poly, hset⟩ := hface.exists_intercept
  have hc_coeff : IsSupportingLine (fun n => v (f.coeff n)) σ c :=
    isSupportingLine_iff_forall.mpr fun n =>
      (isSupportingLine_iff_forall.mp hc_poly n).trans (henv.le n)
  have hj_poly : j ∈ supportingFace (f.newtonPolygon v) σ c :=
    hset.symm.subset ⟨hface.left_le_right, le_rfl⟩
  have hj_coeff : j ∈ supportingFace (fun n => v (f.coeff n)) σ c := by
    rw [mem_supportingFace, ← henv.eq_right_of_isFiniteFace hface]
    exact mem_supportingFace.mp hj_poly
  have hc_eq : c = -Real.logb b (f.gaussNorm norm (b ^ σ)) := EReal.coe_injective <| by
    rw [← supportingValue_eq_coe_of_mem_supportingFace hc_coeff hj_coeff,
      supportingValue_addValuation_coeff_eq_neg_logb_gaussNorm f v hb hv hfn hf0]
  rw [isDistinguished_iff_isGreatest_supportingFace f v hb hv hfn, ← hc_eq]
  exact ⟨hj_coeff, fun m hm => (Set.mem_Icc.mp (hset ▸ henv.supportingFace_subset hc_coeff hm)).2⟩

/-- When `f` is distinguished of degree `j` at `b ^ σ`, slopes `τ > σ` contribute at most the
slope-`σ` value to the Legendre reconstruction at any index `n ≤ j`. -/
private theorem supportingValue_add_le_of_isDistinguished_of_lt {f : K⟦X⟧} {σ τ : ℝ} {j n : ℕ}
    (hf : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f) (hστ : σ < τ) (hn : n ≤ j) :
    supportingValue (f.newtonPolygon v) τ + ((τ * n : ℝ) : EReal) ≤
      supportingValue (f.newtonPolygon v) σ + ((σ * n : ℝ) : EReal) := by
  have hfn := hf.hasGaussNorm
  set cf := -Real.logb b (f.gaussNorm norm (b ^ σ))
  have hj_coeff :=
    ((isDistinguished_iff_isGreatest_supportingFace f v hb hv hfn j).mp hf).1
  have hcf : IsSupportingLine (fun k => v (f.coeff k)) σ cf :=
    isSupportingLine_iff.mpr (supportingValue_addValuation_coeff_eq_neg_logb_gaussNorm
      f v hb hv hfn hf.ne_zero).ge
  have hj_poly : f.newtonPolygon v j = ((cf + σ * j : ℝ) : WithTop ℝ) :=
    mem_supportingFace.mp
      ((f.isLowerConvexEnvelope_newtonPolygon hcf.isAdmissible).supportingFace_subset
        hcf hj_coeff)
  have hSf : supportingValue (f.newtonPolygon v) σ = (cf : EReal) := by
    rw [supportingValue_newtonPolygon_eq_neg_logb_gaussNorm f v hb hv hfn hf.ne_zero]
  have hlin : cf + σ * j - τ * j + τ * n ≤ cf + σ * n := by
    have hjn : (0 : ℝ) ≤ (j : ℝ) - n := sub_nonneg.mpr (Nat.cast_le.mpr hn)
    nlinarith
  have hsub : supportingValue (f.newtonPolygon v) τ ≤ ((cf + σ * j - τ * j : ℝ) : EReal) := by
    simpa only [hj_poly, WithTop.toEReal_coe, EReal.coe_sub] using
      supportingValue_le (f.newtonPolygon v) τ j
  calc supportingValue (f.newtonPolygon v) τ + ((τ * n : ℝ) : EReal)
      ≤ ((cf + σ * j - τ * j : ℝ) : EReal) + ((τ * n : ℝ) : EReal) := add_le_add hsub le_rfl
    _ = ((cf + σ * j - τ * j + τ * n : ℝ) : EReal) := by rw [← EReal.coe_add]
    _ ≤ ((cf + σ * n : ℝ) : EReal) := EReal.coe_le_coe hlin
    _ = supportingValue (f.newtonPolygon v) σ + ((σ * n : ℝ) : EReal) := by
        rw [hSf, EReal.coe_add]

/-- At every active index `n ∈ [P.natTrailingDegree, P.natDegree]`, a polynomial `P` distinguished
in its full degree at `b ^ σ` touches a supporting line of slope `τ ≤ σ`. -/
private theorem exists_le_and_isSupportingLine_of_isDistinguished {P : Polynomial K} {σ : ℝ}
    (hPd : TauCeti.PowerSeries.IsDistinguished (b ^ σ) P.natDegree (P : K⟦X⟧)) {n : ℕ}
    (han : P.natTrailingDegree ≤ n) (hn : n ≤ P.natDegree) :
    ∃ τ ≤ σ, IsSupportingLine (P.newtonPolygon v) τ ((P.newtonPolygon v n).untop₀ - τ * n) := by
  have hP0 : P ≠ 0 := Polynomial.coe_eq_zero_iff.not.mp hPd.ne_zero
  have hPn : P.newtonPolygon v n ≠ ⊤ :=
    (P.newtonPolygon_ne_top_iff v (fun _ => v.top_iff.mp) hP0).mpr ⟨han, hn⟩
  rcases eq_or_lt_of_le hn with rfl | hnj
  · refine ⟨σ, le_rfl, ?_⟩
    rw [(P.isConvexSeq_newtonPolygon v).isSupportingLine_iff_unitSlope hPn σ]
    refine ⟨fun i hi hif => P.le_of_mem_newtonSlopes_of_isDistinguished v hb hv hPd
      ((P.mem_newtonSlopes v).mpr ⟨i, mem_finiteEdges.mpr ⟨hif, hi ▸ hPn⟩, rfl⟩),
      fun hn' => False.elim (hn' (P.newtonPolygon_eq_top_of_natDegree_lt v (by omega)))⟩
  · have hedge : n ∈ finiteEdges (P.newtonPolygon v) := mem_finiteEdges.mpr
      ⟨hPn, (P.newtonPolygon_ne_top_iff v (fun _ => v.top_iff.mp) hP0).mpr ⟨by omega, by omega⟩⟩
    refine ⟨unitSlope (P.newtonPolygon v) n,
      P.le_of_mem_newtonSlopes_of_isDistinguished v hb hv hPd
        ((P.mem_newtonSlopes v).mpr ⟨n, hedge, rfl⟩), ?_⟩
    rw [(P.isConvexSeq_newtonPolygon v).isSupportingLine_iff_unitSlope hPn]
    exact ⟨fun i hi hif => (P.isConvexSeq_newtonPolygon v).monotoneOn
      (mem_finiteEdges.mpr ⟨hif, hi ▸ hPn⟩) hedge (by omega), fun _ => le_rfl⟩

variable [IsUltrametricDist K]

/-- At any slope `τ ≤ σ`, a unit `u` of the ring of series restricted at `b ^ σ` remains
distinguished of degree `0` at `b ^ τ` and its Newton polygon has constant supporting value
`v (u.coeff 0)`. -/
private theorem supportingValue_newtonPolygon_eq_of_isUnit_subring {σ τ : ℝ} (hτσ : τ ≤ σ)
    {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u) :
    supportingValue ((u : K⟦X⟧).newtonPolygon v) τ = (v ((u : K⟦X⟧).coeff 0)).toEReal := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hcσ : 0 < b ^ σ := Real.rpow_pos_of_pos hb0 σ
  have hcτ : 0 < b ^ τ := Real.rpow_pos_of_pos hb0 τ
  have : Nontrivial K :=
    nontrivial_of_ne _ _ (TauCeti.PowerSeries.isDistinguished_zero_of_isUnit hcσ hu).coeff_ne_zero
  have hle : |b ^ τ| ≤ |b ^ σ| := by
    rw [abs_of_pos hcτ, abs_of_pos hcσ]
    exact Real.rpow_le_rpow_of_exponent_le hb.le hτσ
  let φ := Subring.inclusion (TauCeti.PowerSeries.isRestrictedSubring_le_of_abs_le (R := K) hle)
  have hi : TauCeti.PowerSeries.IsDistinguished (b ^ τ) 0 (u : K⟦X⟧) := by
    simpa [φ] using TauCeti.PowerSeries.isDistinguished_zero_of_isUnit hcτ (hu.map φ)
  have hgauss : (u : K⟦X⟧).gaussNorm norm (b ^ τ) = b ^ (-(v ((u : K⟦X⟧).coeff 0)).untop₀) := by
    rw [← hi.norm_coeff_mul_pow_eq, pow_zero, mul_one, hv _ hi.coeff_ne_zero]
  rw [supportingValue_newtonPolygon_eq_neg_logb_gaussNorm (u : K⟦X⟧) v hb hv hi.hasGaussNorm
    hi.ne_zero, hgauss, Real.logb_rpow hb0 hb.ne', neg_neg, ← WithTop.toEReal_coe,
    WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.mpr hi.coeff_ne_zero)]

/-- At every slope `τ ≤ σ`, the supporting value of `f = u * P` is `v (u.coeff 0)` plus that of
`P`. -/
theorem supportingValue_newtonPolygon_eq_of_isUnit_mul {f : K⟦X⟧} {σ τ : ℝ} (hτσ : τ ≤ σ)
    {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u) {P : Polynomial K} (hP : P ≠ 0)
    (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) :
    supportingValue (f.newtonPolygon v) τ =
      (v ((u : K⟦X⟧).coeff 0)).toEReal + supportingValue (P.newtonPolygon v) τ := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hcσ : 0 < b ^ σ := Real.rpow_pos_of_pos hb0 σ
  have hcτ : 0 < b ^ τ := Real.rpow_pos_of_pos hb0 τ
  have huσ := TauCeti.PowerSeries.isDistinguished_zero_of_isUnit hcσ hu
  have hurτ : (u : K⟦X⟧).IsRestricted (b ^ τ) :=
    TauCeti.PowerSeries.isRestricted_of_abs_le u.2 <| by
      rw [abs_of_pos hcτ, abs_of_pos hcσ]
      exact Real.rpow_le_rpow_of_exponent_le hb.le hτσ
  obtain ⟨cu, iu, hcu, hiu⟩ :=
    exists_isSupportingLine_mem_supportingFace_of_isRestricted (u : K⟦X⟧) v hb hv hurτ huσ.ne_zero
  obtain ⟨cP, iP, hcP, hiP⟩ := exists_isSupportingLine_mem_supportingFace_of_isRestricted
    (P : K⟦X⟧) v hb hv (TauCeti.PowerSeries.isRestricted_polynomial P)
    (Polynomial.coe_eq_zero_iff.not.mpr hP)
  rw [← hmul, supportingValue_newtonPolygon_mul v hcu hiu hcP hiP,
    supportingValue_newtonPolygon_eq_of_isUnit_subring v hb hv hτσ hu, P.newtonPolygon_coe]

/-- The upper bound in `newtonPolygon_eq_add_of_isUnit_mul`, stated for the constant term `c₀` of
the unit. -/
private theorem newtonPolygon_le_add_of_isUnit_mul {f : K⟦X⟧} {σ : ℝ} {j : ℕ}
    (hf : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f)
    {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u) {P : Polynomial K} (hP0 : P ≠ 0)
    (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) {n : ℕ} (hn : n ≤ j) {c₀ : ℝ}
    (hc₀ : v ((u : K⟦X⟧).coeff 0) = (c₀ : WithTop ℝ)) :
    (f.newtonPolygon v n).toEReal ≤ (P.newtonPolygon v n + (c₀ : WithTop ℝ)).toEReal := by
  rw [← (f.isConvexSeq_newtonPolygon v).iSup_supportingValue_add n]
  have hstep (τ : ℝ) (hτσ : τ ≤ σ) :
      supportingValue (f.newtonPolygon v) τ + ((τ * n : ℝ) : EReal) ≤
        (P.newtonPolygon v n + (c₀ : WithTop ℝ)).toEReal := by
    rw [supportingValue_newtonPolygon_eq_of_isUnit_mul v hb hv hτσ hu hP0 hmul, hc₀,
      WithTop.toEReal_coe, add_assoc]
    refine (add_le_add le_rfl (EReal.add_le_of_le_sub
      (supportingValue_le (P.newtonPolygon v) τ n))).trans ?_
    induction P.newtonPolygon v n using WithTop.recTopCoe with
    | top => simp
    | coe r =>
      rw [← WithTop.coe_add, WithTop.toEReal_coe, WithTop.toEReal_coe, ← EReal.coe_add,
        add_comm c₀ r]
  exact iSup_le fun τ => (le_or_gt τ σ).elim (hstep τ) fun hστ =>
    (supportingValue_add_le_of_isDistinguished_of_lt v hb hv hf hστ hn).trans (hstep σ le_rfl)

/-- The lower bound in `newtonPolygon_eq_add_of_isUnit_mul`, stated for the constant term `c₀` of
the unit. -/
private theorem add_le_newtonPolygon_of_isUnit_mul {f : K⟦X⟧} {σ : ℝ} {j : ℕ}
    {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u) {P : Polynomial K} (hP0 : P ≠ 0)
    (hPd : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j (P : K⟦X⟧)) (hdeg : P.natDegree = j)
    (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) {n : ℕ} (hn : n ≤ j) {c₀ : ℝ}
    (hc₀ : v ((u : K⟦X⟧).coeff 0) = (c₀ : WithTop ℝ)) :
    (P.newtonPolygon v n + (c₀ : WithTop ℝ)).toEReal ≤ (f.newtonPolygon v n).toEReal := by
  by_cases han : P.natTrailingDegree ≤ n
  · have hPn : P.newtonPolygon v n ≠ ⊤ :=
      (P.newtonPolygon_ne_top_iff v (fun _ => v.top_iff.mp) hP0).mpr ⟨han, hn.trans_eq hdeg.symm⟩
    obtain ⟨τ, hτσ, hline⟩ := exists_le_and_isSupportingLine_of_isDistinguished v hb hv
      (hdeg ▸ hPd) han (hn.trans_eq hdeg.symm)
    have hSP : supportingValue (P.newtonPolygon v) τ =
        (((P.newtonPolygon v n).untop₀ - τ * n : ℝ) : EReal) :=
      supportingValue_eq_coe_of_mem_supportingFace hline
        (by rw [mem_supportingFace, sub_add_cancel, WithTop.coe_untop₀_of_ne_top hPn])
    have hle_f := EReal.add_le_of_le_sub (supportingValue_le (f.newtonPolygon v) τ n)
    rw [supportingValue_newtonPolygon_eq_of_isUnit_mul v hb hv hτσ hu hP0 hmul, hc₀,
      WithTop.toEReal_coe, hSP] at hle_f
    rw [← WithTop.coe_untop₀_of_ne_top hPn, ← WithTop.coe_add, WithTop.toEReal_coe]
    refine le_trans ?_ hle_f
    rw [← EReal.coe_add, ← EReal.coe_add]
    exact EReal.coe_le_coe (by linarith)
  · have hordP : (P.natTrailingDegree : ℕ∞) ≤ (P : K⟦X⟧).order :=
      nat_le_order _ _ fun k hk => by
        rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk]
    have hlt : (n : ℕ∞) < f.order :=
      (Nat.cast_lt.mpr (lt_of_not_ge han)).trans_le
        (hordP.trans (le_add_self.trans (hmul ▸ le_order_mul _ _)))
    rw [f.newtonPolygon_eq_top_of_lt_order v hlt, WithTop.toEReal_top]
    exact le_top

/-- **Newton polygon of a prepared polynomial factor.** Suppose `f` is distinguished of degree `j`
at `b ^ σ`, `u` is a unit of the ring of series restricted at `b ^ σ`, and `u * P = f` for a
polynomial `P` of degree at most `j`. Then for every `n ≤ j`,
`f.newtonPolygon v n = P.newtonPolygon v n + v (u.coeff 0)`. -/
theorem newtonPolygon_eq_add_of_isUnit_mul {f : K⟦X⟧} {σ : ℝ} {j : ℕ}
    (hf : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f)
    {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u) {P : Polynomial K}
    (hPdeg : P.natDegree ≤ j) (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) {n : ℕ} (hn : n ≤ j) :
    f.newtonPolygon v n = P.newtonPolygon v n + v ((u : K⟦X⟧).coeff 0) := by
  have hcσ : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hdeg : P.natDegree = j := TauCeti.PowerSeries.natDegree_eq_of_isUnit_mul hcσ hf hu hPdeg hmul
  have hPd : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j (P : K⟦X⟧) :=
    TauCeti.PowerSeries.IsDistinguished.of_isUnit_mul (hmul.symm ▸ hf) hcσ hu
  have hP0 : P ≠ 0 := Polynomial.coe_eq_zero_iff.not.mp hPd.ne_zero
  have hu0 : v ((u : K⟦X⟧).coeff 0) ≠ ⊤ :=
    v.ne_top_iff.mpr (TauCeti.PowerSeries.isDistinguished_zero_of_isUnit hcσ hu).coeff_ne_zero
  set c₀ := (v ((u : K⟦X⟧).coeff 0)).untop₀
  have hc₀ : v ((u : K⟦X⟧).coeff 0) = (c₀ : WithTop ℝ) :=
    (WithTop.coe_untop₀_of_ne_top hu0).symm
  rw [hc₀]
  refine le_antisymm (WithTop.toEReal_le_toEReal_iff.mp ?_)
    (WithTop.toEReal_le_toEReal_iff.mp ?_)
  · exact newtonPolygon_le_add_of_isUnit_mul v hb hv hf hu hP0 hmul hn hc₀
  · exact add_le_newtonPolygon_of_isUnit_mul v hb hv hu hP0 hPd hdeg hmul hn hc₀

/-- The finite unit edges of `P` are precisely the finite unit edges of `f` strictly below `j`. -/
theorem mem_finiteEdges_newtonPolygon_iff_of_isUnit_mul {f : K⟦X⟧} {σ : ℝ} {j : ℕ}
    (hf : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f)
    {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u) {P : Polynomial K}
    (hPdeg : P.natDegree ≤ j) (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) (i : ℕ) :
    i ∈ finiteEdges (P.newtonPolygon v) ↔ i ∈ finiteEdges (f.newtonPolygon v) ∧ i < j := by
  have hcσ : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hdeg := TauCeti.PowerSeries.natDegree_eq_of_isUnit_mul hcσ hf hu hPdeg hmul
  have hu0 : v ((u : K⟦X⟧).coeff 0) ≠ ⊤ :=
    v.ne_top_iff.mpr (TauCeti.PowerSeries.isDistinguished_zero_of_isUnit hcσ hu).coeff_ne_zero
  constructor
  · intro hi
    have hij : i < j := lt_of_not_ge fun h =>
      (mem_finiteEdges.mp hi).2 (P.newtonPolygon_eq_top_of_natDegree_lt v (by omega))
    obtain ⟨hi1, hi2⟩ := mem_finiteEdges.mp hi
    refine ⟨mem_finiteEdges.mpr ⟨?_, ?_⟩, hij⟩
    · rw [newtonPolygon_eq_add_of_isUnit_mul v hb hv hf hu hPdeg hmul hij.le]
      exact WithTop.add_ne_top.mpr ⟨hi1, hu0⟩
    · rw [newtonPolygon_eq_add_of_isUnit_mul v hb hv hf hu hPdeg hmul (by omega)]
      exact WithTop.add_ne_top.mpr ⟨hi2, hu0⟩
  · rintro ⟨hi, hij⟩
    obtain ⟨hi1, hi2⟩ := mem_finiteEdges.mp hi
    rw [newtonPolygon_eq_add_of_isUnit_mul v hb hv hf hu hPdeg hmul hij.le] at hi1
    rw [newtonPolygon_eq_add_of_isUnit_mul v hb hv hf hu hPdeg hmul (by omega)] at hi2
    exact mem_finiteEdges.mpr ⟨(WithTop.add_ne_top.mp hi1).1, (WithTop.add_ne_top.mp hi2).1⟩

/-- Every finite unit edge of `f` strictly below `j` has the same slope in `P` and in `f`. -/
theorem unitSlope_newtonPolygon_eq_of_isUnit_mul {f : K⟦X⟧} {σ : ℝ} {j : ℕ}
    (hf : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f)
    {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u) {P : Polynomial K}
    (hPdeg : P.natDegree ≤ j) (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) {i : ℕ}
    (hi : i ∈ finiteEdges (f.newtonPolygon v)) (hij : i < j) :
    unitSlope (P.newtonPolygon v) i = unitSlope (f.newtonPolygon v) i := by
  have hcσ : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hu0 : v ((u : K⟦X⟧).coeff 0) ≠ ⊤ :=
    v.ne_top_iff.mpr (TauCeti.PowerSeries.isDistinguished_zero_of_isUnit hcσ hu).coeff_ne_zero
  have hiP := (mem_finiteEdges_newtonPolygon_iff_of_isUnit_mul v hb hv hf hu hPdeg hmul i).mpr
    ⟨hi, hij⟩
  obtain ⟨hPi, hPi1⟩ := mem_finiteEdges.mp hiP
  rw [unitSlope_def, unitSlope_def,
    newtonPolygon_eq_add_of_isUnit_mul v hb hv hf hu hPdeg hmul hij.le,
    newtonPolygon_eq_add_of_isUnit_mul v hb hv hf hu hPdeg hmul (by omega),
    WithTop.untop₀_add hPi1 hu0, WithTop.untop₀_add hPi hu0]
  ring

/-- Every finite slope of a polynomial factor `P` prepared at `b ^ σ` is at most `σ`. -/
theorem le_of_mem_newtonSlopes_of_isUnit_mul {f : K⟦X⟧} {σ : ℝ} {j : ℕ}
    (hf : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f)
    {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u) {P : Polynomial K}
    (hPdeg : P.natDegree ≤ j) (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f)
    {m : ℝ} (hm : m ∈ P.newtonSlopes v) : m ≤ σ := by
  have hcσ : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hdeg := TauCeti.PowerSeries.natDegree_eq_of_isUnit_mul hcσ hf hu hPdeg hmul
  have hPd : TauCeti.PowerSeries.IsDistinguished (b ^ σ) P.natDegree (P : K⟦X⟧) :=
    hdeg ▸ TauCeti.PowerSeries.IsDistinguished.of_isUnit_mul (hmul.symm ▸ hf) hcσ hu
  exact P.le_of_mem_newtonSlopes_of_isDistinguished v hb hv hPd hm

/-- **First-segment pure-polynomial factorisation.** If `f` is restricted at `b ^ σ` and its Newton
polygon has a finite face of slope `σ` from its order of vanishing `l` (`f.order = l`) to `j`, then
any polynomial factor `P` of degree at most `j` in `u * P = f`, with `u` a restricted unit at
`b ^ σ`, is pure of slope `σ`. -/
theorem forall_mem_newtonSlopes_eq_of_isFiniteFace_of_order_eq {f : K⟦X⟧} {σ : ℝ} {l j : ℕ}
    (hfr : f.IsRestricted (b ^ σ)) (hface : IsFiniteFace (f.newtonPolygon v) σ l j)
    (hord : f.order = l) {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u)
    {P : Polynomial K} (hPdeg : P.natDegree ≤ j) (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) :
    ∀ m ∈ P.newtonSlopes v, m = σ := by
  have hf := isDistinguished_of_isFiniteFace v hb hv hfr hface
  rintro m hm
  obtain ⟨i, hiP, rfl⟩ := (P.mem_newtonSlopes v).mp hm
  obtain ⟨hif, hij⟩ :=
    (mem_finiteEdges_newtonPolygon_iff_of_isUnit_mul v hb hv hf hu hPdeg hmul i).mp hiP
  have hli : l ≤ i := by
    by_contra hil
    refine (mem_finiteEdges.mp hif).1 (f.newtonPolygon_eq_top_of_lt_order v ?_)
    rw [hord]
    exact_mod_cast lt_of_not_ge hil
  rw [unitSlope_newtonPolygon_eq_of_isUnit_mul v hb hv hf hu hPdeg hmul hif hij]
  exact hface.unitSlope_eq hli hij

end Valuation

end NormedDivisionRing

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Newton polygon of a constant-normalised disc polynomial.** When `P * u = f` with `u` a unit of
the ring of series restricted at `b ^ σ` satisfying `v (u.coeff 0) = 0` (for instance
`u.coeff 0 = 1`), the Newton polygon of `P` equals that of `f` at every index `n ≤ j`. -/
theorem newtonPolygon_eq_of_mul_isUnit {f : K⟦X⟧} {σ : ℝ} {j : ℕ}
    (hf : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j f)
    {u : IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u)
    (hu0 : v ((u : K⟦X⟧).coeff 0) = 0) {P : Polynomial K} (hPdeg : P.natDegree ≤ j)
    (hmul : (P : K⟦X⟧) * (u : K⟦X⟧) = f) {n : ℕ} (hn : n ≤ j) :
    P.newtonPolygon v n = f.newtonPolygon v n := by
  have h := newtonPolygon_eq_add_of_isUnit_mul v hb hv hf hu hPdeg (mul_comm (u : K⟦X⟧) _ ▸ hmul) hn
  rw [hu0, add_zero] at h
  exact h.symm

end NormedField

end PowerSeries

namespace Polynomial

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Slopes of a polynomial factor prepared at a finite face.** If `f : K[X]` has a finite face
`(l, j)` of slope `σ` and `(u : K⟦X⟧) * (P : K⟦X⟧) = (f : K⟦X⟧)` for a restricted unit `u` at
`b ^ σ` and a polynomial `P` of degree at most `j`, then the finite Newton slopes of `P` are
precisely the finite Newton slopes of `f` that are at most `σ`. -/
theorem newtonSlopes_eq_filter_le_of_isFiniteFace {f P : K[X]} {σ : ℝ} {l j : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l j)
    {u : PowerSeries.IsRestricted.subring (R := K) (b ^ σ)} (hu : IsUnit u)
    (hPdeg : P.natDegree ≤ j) (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = (f : K⟦X⟧)) :
    P.newtonSlopes v = (f.newtonSlopes v).filter (· ≤ σ) := by
  have hfd : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j (f : K⟦X⟧) :=
    PowerSeries.isDistinguished_of_isFiniteFace v hb hv
      (TauCeti.PowerSeries.isRestricted_polynomial f) (f.newtonPolygon_coe v ▸ hface)
  rw [newtonSlopes_def, newtonSlopes_def, Multiset.filter_map, ← Finset.filter_val]
  have hfin_eq : (P.finite_finiteEdges_newtonPolygon v).toFinset =
      (f.finite_finiteEdges_newtonPolygon v).toFinset.filter
        (fun i => unitSlope (f.newtonPolygon v) i ≤ σ) := by
    ext i
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
    rw [PowerSeries.mem_finiteEdges_newtonPolygon_iff_of_isUnit_mul v hb hv hfd hu hPdeg hmul i,
      f.newtonPolygon_coe]
    refine and_congr_right fun hif => ⟨fun hij => ?_, fun hle => ?_⟩
    · by_cases hil : i < l
      · exact (hface.unitSlope_lt (f.isConvexSeq_newtonPolygon v) hif hil).le
      · exact (hface.unitSlope_eq (le_of_not_gt hil) hij).le
    · by_contra hij
      exact hle.not_gt (hface.lt_unitSlope (f.isConvexSeq_newtonPolygon v) hif (le_of_not_gt hij))
  rw [hfin_eq]
  refine Multiset.map_congr rfl fun i hi => ?_
  have hi' := Finset.mem_filter.mp hi
  rw [Set.Finite.mem_toFinset] at hi'
  have hij : i < j := by
    by_contra hge
    exact hi'.2.not_gt (hface.lt_unitSlope (f.isConvexSeq_newtonPolygon v) hi'.1
      (le_of_not_gt hge))
  simpa only [f.newtonPolygon_coe] using
    PowerSeries.unitSlope_newtonPolygon_eq_of_isUnit_mul v hb hv hfd hu hPdeg hmul
      (by rw [f.newtonPolygon_coe]; exact hi'.1) hij

end NormedDivisionRing

end Polynomial
