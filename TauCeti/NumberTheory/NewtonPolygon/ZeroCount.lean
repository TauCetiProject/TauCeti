/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Entire
public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.NumberTheory.NewtonPolygon.Weierstrass
public import TauCeti.RingTheory.PowerSeries.Restricted.GoodZero
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.RingTheory.PowerSeries.RootBound

/-!
# Counting zeros with multiplicity by Newton polygons

Let `K` be a complete ultrametric normed field whose norm comes from a real additive valuation `v`
with base `b > 1`, so `‖x‖ = b ^ (-v x)` for `x ≠ 0`. Let `f` be a series restricted at `b ^ σ`,
prepared there as `f = u * P` with `u` a unit of the ring of series restricted at `b ^ σ` and `P`
a polynomial. The multiplicity of a zero `a` of `f` in the closed disc `‖a‖ ≤ b ^ σ`, the order of
the good zero `PowerSeries.IsGoodZero f a h`, is the root multiplicity of `a` in `P`
(`PowerSeries.isGoodZero_iff_rootMultiplicity_eq_of_isUnit_mul`). Reading the roots of `P` off
its Newton polygon turns this into exact counts with multiplicity:

* every root of `P` lies in the closed disc of radius `b ^ σ`
  (`TauCeti.PowerSeries.IsDistinguished.norm_le_of_mem_roots_of_isUnit_mul`, at any radius
  `c > 0`), so when `P` splits, the zeros of `f` in that disc, counted with multiplicity, are the
  roots of `P` and there are exactly as many as the degree in which `f` is distinguished there
  (`TauCeti.PowerSeries.IsDistinguished.exists_card_eq_isGoodZero`);
* when the Newton polygon of `f` has a finite face of slope `σ` and `P` splits, the multiplicity
  of the slope `σ` is the number of roots of `P` on the sphere `‖a‖ = b ^ σ`, counted with
  multiplicity (`PowerSeries.newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul`). Over an
  algebraically closed `K` it is therefore the number of zeros of `f` of norm `b ^ σ`, counted
  with multiplicity (`PowerSeries.exists_card_eq_newtonSlopeMultiplicity_isGoodZero`). If that
  face runs from `l` to `j` and `P` splits, then `P` has exactly `l` roots in the open disc
  `‖a‖ < b ^ σ` (`PowerSeries.card_filter_roots_norm_lt_of_isUnit_mul`), so over an algebraically
  closed `K` the zeros of `f` there number `l`, counted with multiplicity
  (`PowerSeries.exists_card_eq_isGoodZero_of_isFiniteFace`).

A nonzero entire series has a finite face of every slope, so over an algebraically closed field
the multiplicity of each slope `σ` of its Newton polygon is the number of its zeros of norm
`b ^ σ`, counted with multiplicity
(`PowerSeries.IsEntire.exists_card_eq_newtonSlopeMultiplicity_isGoodZero`). For the Fredholm
series `det (1 - T u)` of a compact operator, a zero `a` gives the eigenvalue `a⁻¹`, so this is
the count by which the slopes of the Fredholm polygon describe the valuations of eigenvalues with
their algebraic multiplicities.

## Main results

* `TauCeti.PowerSeries.IsDistinguished.norm_le_of_mem_roots_of_isUnit_mul`: the prepared
  polynomial has its roots in the closed disc.
* `TauCeti.PowerSeries.IsDistinguished.exists_card_eq_isGoodZero`: over an algebraically closed
  field, a series distinguished of degree `s` at `c > 0` has exactly `s` zeros in the closed disc,
  counted with multiplicity.
* `PowerSeries.newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul`: when the prepared
  polynomial splits, the multiplicity of a slope is the number of its roots on the corresponding
  sphere.
* `PowerSeries.card_filter_roots_norm_lt_of_isUnit_mul`: when the prepared polynomial splits, the
  left endpoint of a finite face is the number of its roots in the corresponding open disc.
* `PowerSeries.exists_card_eq_newtonSlopeMultiplicity_isGoodZero`,
  `PowerSeries.IsEntire.exists_card_eq_newtonSlopeMultiplicity_isGoodZero`: over an
  algebraically closed field, the multiplicity of a slope `σ` is the number of zeros of norm
  `b ^ σ`, counted with multiplicity.
* `PowerSeries.exists_card_eq_isGoodZero_of_isFiniteFace`: over an algebraically closed field,
  the left endpoint of the finite face of slope `σ` is the number of zeros of norm less than
  `b ^ σ`, counted with multiplicity.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer,
  1984, §5.2.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §3.
-/

public section

open TauCeti

namespace TauCeti.PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {c : ℝ} {s : ℕ}
  {f : _root_.PowerSeries K}

/-- **The prepared polynomial has its roots in the closed disc.** If `f` is distinguished of degree
`s` at `c > 0` and `f = u * P` with `u` a unit of the ring of series restricted at `c` and `P` a
polynomial of degree at most `s`, then every root of `P` has norm at most `c`. -/
theorem IsDistinguished.norm_le_of_mem_roots_of_isUnit_mul (hf : IsDistinguished c s f)
    (hc : 0 < c) {u : _root_.PowerSeries.IsRestricted.subring (R := K) c} (hu : IsUnit u)
    {P : Polynomial K} (hPdeg : P.natDegree ≤ s)
    (hmul : (u : _root_.PowerSeries K) * (P : _root_.PowerSeries K) = f) {α : K}
    (hα : α ∈ P.roots) : ‖α‖ ≤ c := by
  have ha : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.2 (Polynomial.ne_zero_of_mem_roots hα)
  -- normalise `P` to the monic `Q = P.leadingCoeff⁻¹ • P`, which is still distinguished
  set Q := Polynomial.C P.leadingCoeff⁻¹ * P
  have hQm : Q.IsMonicOfDegree s :=
    ⟨by rw [Polynomial.natDegree_C_mul (inv_ne_zero ha),
        natDegree_eq_of_isUnit_mul hc hf hu hPdeg hmul],
      by rw [Polynomial.Monic, Polynomial.leadingCoeff_C_mul_of_isUnit (inv_ne_zero ha).isUnit,
        inv_mul_cancel₀ ha]⟩
  have hPQ : ((algebraMap K (_root_.PowerSeries.IsRestricted.subring (R := K) c)
      P.leadingCoeff : _) : _root_.PowerSeries K) * (Q : _root_.PowerSeries K) = P := by
    rw [coe_algebraMap_isRestrictedSubring, Algebra.algebraMap_self_apply,
      Polynomial.coe_mul, Polynomial.coe_C, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one,
      one_mul]
  have hQd : IsDistinguished c s (Q : _root_.PowerSeries K) :=
    IsDistinguished.of_isUnit_mul (hPQ ▸ IsDistinguished.of_isUnit_mul (hmul ▸ hf) hc hu) hc
      (ha.isUnit.map _)
  refine hQd.norm_le_of_eval_eq_zero hc hQm ?_
  rw [Polynomial.eval_mul, (Polynomial.isRoot_of_mem_roots hα).eq_zero, mul_zero]

/-- **Zeros in a closed disc, with multiplicity.** Over an algebraically closed field, the zeros
of a series `f` restricted at `c > 0` and distinguished of degree `s` there, in the closed disc of
radius `c` and counted with multiplicity, form a multiset `Z` with exactly `s` elements: `f` has a
good zero of order `Z.count a` at every `a` of norm at most `c`. -/
theorem IsDistinguished.exists_card_eq_isGoodZero [CompleteSpace K] [IsAlgClosed K]
    [DecidableEq K] (hfd : IsDistinguished c s f) (hc : 0 < c) (hfr : f.IsRestricted c) :
    ∃ Z : Multiset K, Multiset.card Z = s ∧ (∀ a ∈ Z, ‖a‖ ≤ c) ∧
      ∀ a, ‖a‖ ≤ c → f.IsGoodZero a (Z.count a) := by
  obtain ⟨u, P, hu, hP, hmul⟩ :=
    hfd.exists_isUnit_isMonicOfDegree_mul_eq hfd.coeff_ne_zero.isUnit hc hfr
  refine ⟨P.roots, ?_, fun a ha ↦ (IsDistinguished.of_isUnit_mul (hmul ▸ hfd) hc hu
      ).norm_le_of_eval_eq_zero hc hP (Polynomial.isRoot_of_mem_roots ha), fun a ha ↦ ?_⟩
  · rw [← hP.natDegree_eq]
    exact Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits P)
  · exact _root_.PowerSeries.isGoodZero_count_roots_of_isUnit_mul hu hmul hfd.ne_zero ha

end TauCeti.PowerSeries

namespace PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
  {f : K⟦X⟧} {σ : ℝ} {j : ℕ} {u : IsRestricted.subring (R := K) (b ^ σ)} {P : Polynomial K}

include hb hv

/-- **Slope multiplicity and roots on a sphere.** Suppose the Newton polygon of a series `f`
restricted at `b ^ σ` has a finite face of slope `σ` ending at `j`, and `f = u * P` with `u` a
unit of the ring of series restricted at `b ^ σ` and `P` a polynomial of degree at most `j` which
splits. Then the multiplicity of the slope `σ` is the number of roots of `P` of norm `b ^ σ`,
counted with multiplicity. -/
theorem newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul
    (hfr : f.IsRestricted (b ^ σ)) {l : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l j)
    (hu : IsUnit u) (hPdeg : P.natDegree ≤ j) (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f)
    (hP : P.Splits) :
    f.newtonSlopeMultiplicity v σ = (P.roots.filter fun α ↦ ‖α‖ = b ^ σ).card := by
  classical
  have hfd := isDistinguished_of_isFiniteFace v hb hv hfr hface
  -- The finite unit edges of slope `σ` of `f` lie below `j`, where they are those of `P`.
  have hedges : {i | i ∈ finiteEdges (P.newtonPolygon v) ∧ unitSlope (P.newtonPolygon v) i = σ} =
      {i | i ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) i = σ} := by
    ext i
    simp only [Set.mem_ofPred_eq, mem_finiteEdges_newtonPolygon_iff_of_isUnit_mul v hb hv hfd hu
      hPdeg hmul]
    refine ⟨fun ⟨⟨hi, hij⟩, hσ⟩ ↦ ?_, fun ⟨hi, hσ⟩ ↦ ?_⟩
    · rw [unitSlope_newtonPolygon_eq_of_isUnit_mul v hb hv hfd hu hPdeg hmul hi hij] at hσ
      exact ⟨hi, hσ⟩
    · have hij : i < j := ((hface.setOf_unitSlope_eq (f.isConvexSeq_newtonPolygon v)).subset
        ⟨hi, hσ⟩).2
      rw [unitSlope_newtonPolygon_eq_of_isUnit_mul v hb hv hfd hu hPdeg hmul hi hij]
      exact ⟨⟨hi, hij⟩, hσ⟩
  rw [newtonSlopeMultiplicity_def, ← hedges, ← Polynomial.card_filter_newtonSlopes P v (· = σ),
    Polynomial.card_filter_newtonSlopes_eq (fun _ ↦ v.top_iff.mp) hP]
  -- a point has norm `b ^ σ` exactly when it is nonzero of valuation `-σ`
  refine congrArg _ (Multiset.filter_congr fun α _ ↦ ⟨fun ⟨hα, hσ⟩ ↦ ?_, fun h ↦ ?_⟩)
  · rw [hv α hα]
    exact congrArg _ hσ
  · have hα : α ≠ 0 := by
      rintro rfl
      exact (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ).ne (by simpa using h)
    exact ⟨hα, (Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne').mp ((hv α hα).symm.trans h)⟩

/-- **Roots in the open disc.** Under the hypotheses of
`PowerSeries.newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul`, with the finite face of
slope `σ` running from `l` to `j`, the polynomial `P` has exactly `l` roots of norm less than
`b ^ σ`, counted with multiplicity. -/
theorem card_filter_roots_norm_lt_of_isUnit_mul (hfr : f.IsRestricted (b ^ σ)) {l : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l j) (hu : IsUnit u) (hPdeg : P.natDegree ≤ j)
    (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) (hP : P.Splits) :
    (P.roots.filter fun α ↦ ‖α‖ < b ^ σ).card = l := by
  have hfd := isDistinguished_of_isFiniteFace v hb hv hfr hface
  have hsphere := newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul v hb hv hfr hface hu
    hPdeg hmul hP
  rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface] at hsphere
  -- the roots not in the open disc are those on the sphere, since all lie in the closed disc
  have hnot : (P.roots.filter fun α ↦ ¬‖α‖ < b ^ σ) = P.roots.filter fun α ↦ ‖α‖ = b ^ σ :=
    Multiset.filter_congr fun α hα ↦ ⟨fun h ↦ le_antisymm
      (hfd.norm_le_of_mem_roots_of_isUnit_mul (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hu
        hPdeg hmul hα) (not_lt.1 h),
      fun h ↦ h.not_lt⟩
  have hcard : Multiset.card P.roots = j := by
    rw [Polynomial.splits_iff_card_roots.1 hP, TauCeti.PowerSeries.natDegree_eq_of_isUnit_mul
      (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hfd hu hPdeg hmul]
  have h := congrArg Multiset.card (Multiset.filter_add_not (fun α ↦ ‖α‖ < b ^ σ) P.roots)
  rw [Multiset.card_add, hnot, ← hsphere, hcard] at h
  have := hface.left_le_right
  omega

variable [CompleteSpace K] [IsAlgClosed K] [DecidableEq K]

/-- **Zeros on a sphere, with multiplicity.** Over an algebraically closed field, if the Newton
polygon of a series `f` restricted at `b ^ σ` has a finite face of slope `σ`, the zeros of `f` of
norm `b ^ σ`, counted with multiplicity, form a multiset `Z` with as many elements as the
multiplicity of the slope `σ`: `f` has a good zero of order `Z.count a` at every `a` of norm
`b ^ σ`. -/
theorem exists_card_eq_newtonSlopeMultiplicity_isGoodZero (hfr : f.IsRestricted (b ^ σ)) {l : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l j) :
    ∃ Z : Multiset K, Multiset.card Z = f.newtonSlopeMultiplicity v σ ∧
      (∀ a ∈ Z, ‖a‖ = b ^ σ) ∧ ∀ a, ‖a‖ = b ^ σ → f.IsGoodZero a (Z.count a) := by
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hfd := isDistinguished_of_isFiniteFace v hb hv hfr hface
  obtain ⟨u, P, hu, hP, hmul⟩ :=
    hfd.exists_isUnit_isMonicOfDegree_mul_eq hfd.coeff_ne_zero.isUnit hc hfr
  refine ⟨P.roots.filter fun α ↦ ‖α‖ = b ^ σ,
    (newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul v hb hv hfr hface hu
      hP.natDegree_eq.le hmul (IsAlgClosed.splits P)).symm,
    fun a ha ↦ (Multiset.mem_filter.1 ha).2, fun a ha ↦ ?_⟩
  rw [Multiset.count_filter_of_pos (p := fun α ↦ ‖α‖ = b ^ σ) ha]
  exact isGoodZero_count_roots_of_isUnit_mul hu hmul hfd.ne_zero ha.le

/-- **Zeros in an open disc, with multiplicity.** Over an algebraically closed field, if the Newton
polygon of a series `f` restricted at `b ^ σ` has a finite face of slope `σ` from `l` to `j`, the
zeros of `f` of norm less than `b ^ σ`, counted with multiplicity, form a multiset `Z` with exactly
`l` elements: `f` has a good zero of order `Z.count a` at every `a` of norm less than `b ^ σ`. -/
theorem exists_card_eq_isGoodZero_of_isFiniteFace (hfr : f.IsRestricted (b ^ σ)) {l : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l j) :
    ∃ Z : Multiset K, Multiset.card Z = l ∧ (∀ a ∈ Z, ‖a‖ < b ^ σ) ∧
      ∀ a, ‖a‖ < b ^ σ → f.IsGoodZero a (Z.count a) := by
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hfd := isDistinguished_of_isFiniteFace v hb hv hfr hface
  obtain ⟨u, P, hu, hP, hmul⟩ :=
    hfd.exists_isUnit_isMonicOfDegree_mul_eq hfd.coeff_ne_zero.isUnit hc hfr
  refine ⟨P.roots.filter fun α ↦ ‖α‖ < b ^ σ,
    card_filter_roots_norm_lt_of_isUnit_mul v hb hv hfr hface hu hP.natDegree_eq.le hmul
      (IsAlgClosed.splits P),
    fun a ha ↦ (Multiset.mem_filter.1 ha).2, fun a ha ↦ ?_⟩
  rw [Multiset.count_filter_of_pos (p := fun α ↦ ‖α‖ < b ^ σ) ha]
  exact isGoodZero_count_roots_of_isUnit_mul hu hmul hfd.ne_zero ha.le

/-- **Zeros of an entire series on a sphere, with multiplicity.** Over an algebraically closed
field, for every real `σ` the zeros of a nonzero entire series `f` of norm `b ^ σ`, counted with
multiplicity, form a multiset with as many elements as the multiplicity of the slope `σ` of the
Newton polygon of `f`. -/
theorem IsEntire.exists_card_eq_newtonSlopeMultiplicity_isGoodZero (hf : f.IsEntire)
    (hf0 : f ≠ 0) (σ : ℝ) :
    ∃ Z : Multiset K, Multiset.card Z = f.newtonSlopeMultiplicity v σ ∧
      (∀ a ∈ Z, ‖a‖ = b ^ σ) ∧ ∀ a, ‖a‖ = b ^ σ → f.IsGoodZero a (Z.count a) := by
  obtain ⟨l, j, hface⟩ := hf.exists_isFiniteFace_newtonPolygon v hb hv hf0 σ
  exact PowerSeries.exists_card_eq_newtonSlopeMultiplicity_isGoodZero v hb hv (hf.isRestricted _)
    hface

end PowerSeries
