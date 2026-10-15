/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.DiscPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import Mathlib.Topology.Order.IsLUB
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Closed discs inside the closed unit disc

For `a, c ∈ K`, the *closed subdisc* `D(a, |c|)` of the closed unit disc `Spa (K⟨T⟩, K⟨T⟩°)` is
the rational subset

```text
D(a, |c|) = {v : v(T - a) ≤ v(c) ≠ 0} = R({T - a, c} / c).
```

These are the basic rational subdomains of the closed unit disc. This file locates the classical
points, the points `η_{b,r}` and the rank-two points `η_{r±}` relative to them. Over a complete
nonarchimedean field `K`:

* a classical point `x_b` lies in `D(a, |c|)` exactly when `‖b - a‖ ≤ ‖c‖` and `c ≠ 0`, whatever
  point of `Spa (K, K°)` it is built from. Every point of `Spa (K, K°)` compares elements of `K`
  by their norms (`TauCeti.ValuationSpectrum.vle_iff_norm_le_of_mem_spa`), and so does every point
  of the closed polydisc on constants
  (`TauCeti.ValuationSpectrum.closedPolydisc_vle_weightedC_iff`);
* the point `η_{b,r}` lies in `D(a, |c|)` exactly when `‖b - a‖ ≤ ‖c‖` and `r ≤ ‖c‖`;
* about the origin, `η_{r⁻}` lies in `D(0, |c|)` exactly when `r ≤ ‖c‖`, while `η_{r⁺}` does
  exactly when `r < ‖c‖`. At `‖c‖ = r` the disc contains `η_r` and `η_{r⁻}` but not `η_{r⁺}`,
  although `η_{r⁺}` is a specialization of `η_r`: the rank-two point `η_{r⁺}` lies outside the
  closed disc of radius `r`. The same holds about every centre: `η_{b,r⁻}` lies in `D(a, |c|)`
  exactly when `‖b - a‖ ≤ ‖c‖` and `r ≤ ‖c‖`, and `η_{b,r⁺}` exactly when `‖b - a‖ ≤ ‖c‖` and
  `r < ‖c‖`.

The points `η_{b,r}` also determine the discs themselves. For `‖a‖ ≤ 1` and `0 < ‖c‖ ≤ 1`,
`D(a, |c|) ⊆ D(b, |d|)` exactly when `‖a - b‖ ≤ ‖d‖` and `‖c‖ ≤ ‖d‖`, and two such discs are
equal exactly when their radii agree and each centre lies in the other disc. If
`max ‖c‖ ‖d‖ < ‖a - b‖`, the discs `D(a, |c|)` and `D(b, |d|)` are disjoint.

## Main definitions

* `TauCeti.ValuationSpectrum.closedSubdisc`: the rational subset `D(a, |c|)` of the closed unit
  disc.

## Main results

* `TauCeti.ValuationSpectrum.closedSubdisc_eq_rationalSubset`,
  `TauCeti.ValuationSpectrum.isOpen_closedSubdisc`,
  `TauCeti.ValuationSpectrum.closedSubdisc_mem_spaRationalFamily` and
  `TauCeti.ValuationSpectrum.isCompact_closedSubdisc`: `D(a, |c|)` is the rational subset
  `R({T - a, c} / c)`, hence open and, when `T - a` and `c` generate an open ideal (for instance
  when `c` is a unit), a member of the rational family and quasi-compact.
* `TauCeti.ValuationSpectrum.closedSubdisc_zero_one`: `D(0, 1)` is the whole closed unit disc,
  and `TauCeti.ValuationSpectrum.closedSubdisc_zero_right`: `D(a, |0|)` is empty.
* `TauCeti.ValuationSpectrum.closure_closedSubdisc_subset_closedSubdisc`: strictly enlarging
  a radius contains the closure of the smaller disc.
* `TauCeti.ValuationSpectrum.isClosed_iInter_closedSubdisc`: an intersection of discs is closed
  when every disc contains a member of the family with strictly smaller radius.
* `TauCeti.ValuationSpectrum.isClosed_iInter_closedSubdisc_of_no_common_point`: a decreasing
  sequence with no common point in `K` has closed intersection in the adic unit disc.
* `TauCeti.ValuationSpectrum.classicalPoint_mem_closedSubdisc_iff`,
  `TauCeti.ValuationSpectrum.gaussPoint_mem_closedSubdisc_iff`,
  `TauCeti.ValuationSpectrum.discPoint_mem_closedSubdisc_iff`,
  `TauCeti.ValuationSpectrum.gaussPointBelow_mem_closedSubdisc_zero_iff` and
  `TauCeti.ValuationSpectrum.gaussPointAbove_mem_closedSubdisc_zero_iff`,
  `TauCeti.ValuationSpectrum.discPointBelow_mem_closedSubdisc_iff` and
  `TauCeti.ValuationSpectrum.discPointAbove_mem_closedSubdisc_iff`: which points of the closed
  unit disc lie in `D(a, |c|)`.
* `TauCeti.ValuationSpectrum.closedSubdisc_subset_closedSubdisc_iff`,
  `TauCeti.ValuationSpectrum.closedSubdisc_eq_closedSubdisc_iff` and
  `TauCeti.ValuationSpectrum.disjoint_closedSubdisc`: inclusion, equality and disjointness of
  discs.
* `TauCeti.ValuationSpectrum.valuation_weightedX_sub_weightedC_of_mem_closedSubdisc`: a point
  of `D(a, |c|)` takes the value of the constant `a - b` on `T - b` for every `b` outside the disc.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §7.2, for rational subdomains
  of affinoid spaces.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), Example 2.20, for the points of
  type (5).
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

local notation "𝒯" K => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set _)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set _)) isWeightFamily_one_weight

/-! ### The discs as rational subsets -/

section TopologicalRing

variable {K : Type*} [CommRing K] [TopologicalSpace K] [NonarchimedeanRing K]

/-- **The closed subdisc `D(a, |c|)`** of the closed unit disc: the rational subset
`{v : v(T - a) ≤ v(c) ≠ 0}`. For a nonarchimedean normed field `K`, `‖a‖ ≤ 1` and
`0 < ‖c‖ ≤ 1`, this is the closed disc of radius `‖c‖` about `a`. -/
def closedSubdisc (a c : K) : Set (closedPolydisc 1 K) :=
  Subtype.val ⁻¹' basicOpen (T - C a) (C c)

/-- Membership in `D(a, |c|)` is the defining valuation inequality and nonvanishing. -/
@[simp]
theorem mem_closedSubdisc (a c : K) (v : closedPolydisc 1 K) :
    v ∈ closedSubdisc a c ↔
      v.1.toValuativeRel.vle (T - C a) (C c) ∧ ¬ v.1.toValuativeRel.vle (C c) 0 := by
  rw [closedSubdisc, Set.mem_preimage, mem_basicOpen_iff]

/-- Each disc `D(a, |c|)` is open in the closed unit disc. -/
theorem isOpen_closedSubdisc (a c : K) : IsOpen (closedSubdisc a c) :=
  (isOpen_basicOpen _ _).preimage continuous_subtype_val

open scoped Classical in
/-- **`D(a, |c|)` is the rational subset `R({T - a, c} / c)`.** Including the denominator among
the numerators makes the admissibility of the presentation explicit when `c` is a unit. -/
theorem closedSubdisc_eq_rationalSubset (a c : K) :
    closedSubdisc a c = Subtype.val ⁻¹'
      rationalSubset (powerBoundedSubring (𝒯 K)) {T - C a, C c} (C c) := by
  ext v
  rw [mem_closedSubdisc, Set.mem_preimage, mem_rationalSubset_iff]
  have hv : v.1 ∈ spa (powerBoundedSubring (𝒯 K)) := closedPolydisc_def 1 K ▸ v.2
  simp [hv]

/-- **`D(a, |c|)` belongs to the rational family** of `Spa (K⟨T⟩, K⟨T⟩°)` when the numerators
`T - a` and `c` of `R({T - a, c} / c)` generate an open ideal, for instance when `c` is a unit. -/
theorem closedSubdisc_mem_spaRationalFamily (a c : K)
    (hT : IsOpen (Ideal.span ({T - C a, C c} : Set (𝒯 K)) : Set (𝒯 K))) :
    (Homeomorph.setCongr (closedPolydisc_def 1 K)).symm ⁻¹' closedSubdisc a c ∈
      spaRationalFamily (powerBoundedSubring (𝒯 K)) := by
  classical
  rw [closedSubdisc_eq_rationalSubset]
  exact mem_spaRationalFamily_iff.mpr
    ⟨_, _, by rwa [Finset.coe_insert, Finset.coe_singleton], rfl⟩

/-- `D(a, |c|)` is quasi-compact over a Huber ring when `T - a` and `c` generate an open ideal,
for instance when `c` is a unit. -/
theorem isCompact_closedSubdisc [IsHuberRing K] (a c : K)
    (hT : IsOpen (Ideal.span ({T - C a, C c} : Set (𝒯 K)) : Set (𝒯 K))) :
    IsCompact (closedSubdisc a c) := by
  have h := isCompact_of_mem_spaRationalFamily (closedSubdisc_mem_spaRationalFamily a c hT)
  rwa [Homeomorph.isCompact_preimage] at h

/-- **`D(0, 1)` is the whole closed unit disc**: the variable is power-bounded, so every point
of the disc has `v(T) ≤ 1`. -/
@[simp]
theorem closedSubdisc_zero_one : closedSubdisc (0 : K) 1 = Set.univ := by
  refine Set.eq_univ_of_forall fun v ↦ (mem_closedSubdisc 0 1 v).mpr ⟨?_, ?_⟩
  · rw [map_zero, sub_zero, map_one]
    exact ((mem_closedPolydisc_iff 1 K v.1).mp v.2).2 T
      (mem_powerBoundedSubring.mpr (isPowerBounded_weightedX_one_weight 0))
  · rw [map_one]
    exact v.1.toValuativeRel.not_vle_one_zero

/-- **`D(a, |0|)` is empty**: no point has `v(0) ≠ 0`. -/
@[simp]
theorem closedSubdisc_zero_right (a : K) : closedSubdisc a 0 = ∅ := by
  ext v
  simp

end TopologicalRing

/-! ### Discs over a normed field -/

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]

/-- **Nested discs**: `D(a, |c|) ⊆ D(b, |d|)` whenever `‖a - b‖ ≤ ‖d‖` and `‖c‖ ≤ ‖d‖`. -/
theorem closedSubdisc_subset_closedSubdisc {a b c d : K} (hab : ‖a - b‖ ≤ ‖d‖)
    (hcd : ‖c‖ ≤ ‖d‖) : closedSubdisc a c ⊆ closedSubdisc b d := by
  intro v hv
  rw [mem_closedSubdisc] at hv ⊢
  have h₁ := (valuation_le_iff _ _ _).mpr hv.1
  have h₂ := (valuation_le_iff _ _ _).mpr ((closedPolydisc_vle_weightedC_iff v c d).mpr hcd)
  have h₃ := (valuation_le_iff _ _ _).mpr ((closedPolydisc_vle_weightedC_iff v _ d).mpr hab)
  refine ⟨?_, fun hd ↦ hv.2 ((valuation_le_iff _ _ _).mp
    (h₂.trans ((valuation_le_iff _ _ _).mpr hd)))⟩
  -- `T - b = (T - a) + (a - b)`, and both summands are dominated by `d`
  rw [← valuation_le_iff, show T - C b = (T - C a) + C (a - b) by rw [map_sub]; ring]
  exact (Valuation.map_add _ _ _).trans (max_le (h₁.trans h₂) h₃)

/-- Strict enlargement of the radius contains the closure of a closed subdisc. -/
theorem closure_closedSubdisc_subset_closedSubdisc {a c d : K} (hcd : ‖c‖ < ‖d‖) :
    closure (closedSubdisc a c) ⊆ closedSubdisc a d := by
  let F : Set (closedPolydisc 1 K) :=
    (Subtype.val ⁻¹' basicOpen (C d) (T - C a))ᶜ
  have hF : IsClosed F :=
    ((isOpen_basicOpen _ _).preimage continuous_subtype_val).isClosed_compl
  have hsub : closedSubdisc a c ⊆ F := by
    intro x hx hmem
    have h₁ := (mem_closedSubdisc a c x).mp hx
    have h₂ := (mem_basicOpen_iff _ _ _).mp hmem
    exact hcd.not_ge ((closedPolydisc_vle_weightedC_iff x d c).mp
      (x.1.toValuativeRel.vle_trans h₂.1 h₁.1))
  intro x hx
  have hxF := closure_minimal hsub hF hx
  have hd : ¬ x.1.toValuativeRel.vle (C d) 0 := by
    rw [← map_zero C, closedPolydisc_vle_weightedC_iff, norm_zero]
    exact not_le.mpr ((norm_nonneg c).trans_lt hcd)
  refine (mem_closedSubdisc a d x).mpr ⟨?_, hd⟩
  by_contra hn
  have hrev := x.1.toValuativeRel.vle_total (T - C a) (C d)
  have hda := hrev.resolve_left hn
  exact hxF ((mem_basicOpen_iff _ _ _).mpr ⟨hda,
    fun hzero ↦ hd (x.1.toValuativeRel.vle_trans hda hzero)⟩)

/-- An intersection of discs is closed if each disc contains a disc of the family with
strictly smaller radius. The centres may vary, and the family need not be a sequence. -/
theorem isClosed_iInter_closedSubdisc {ι : Sort*} (a c : ι → K)
    (hrefine : ∀ i, ∃ j, ‖a j - a i‖ ≤ ‖c i‖ ∧ ‖c j‖ < ‖c i‖) :
    IsClosed (⋂ i, closedSubdisc (a i) (c i)) := by
  refine isClosed_of_closure_subset fun x hx ↦ Set.mem_iInter.mpr fun i ↦ ?_
  obtain ⟨j, hji, hrad⟩ := hrefine i
  exact closedSubdisc_subset_closedSubdisc hji le_rfl
    (closure_closedSubdisc_subset_closedSubdisc hrad
      (closure_mono (Set.iInter_subset _ j) hx))

/-- A decreasing sequence of discs with no common point in the ground field has closed
intersection in the adic unit disc. Its adic intersection need not be empty. -/
theorem isClosed_iInter_closedSubdisc_of_no_common_point (a c : ℕ → K)
    (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖)
    (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖)
    (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) :
    IsClosed (⋂ n, closedSubdisc (a n) (c n)) := by
  -- Use classical closed balls to extract strict refinements, without Gauss points or
  -- completeness. In an ultrametric space every point of a ball is also a centre.
  have hanti : Antitone fun n ↦ Metric.closedBall (a n) ‖c n‖ :=
    antitone_nat_of_succ_le fun n ↦ by
      rw [IsUltrametricDist.closedBall_eq_of_mem (x := a n) (y := a (n + 1))
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hac n)]
      exact Metric.closedBall_subset_closedBall (hcc n)
  apply isClosed_iInter_closedSubdisc
  intro n
  obtain ⟨m, hm⟩ := hempty (a n)
  have hnm : n ≤ m := by
    by_contra! hmn
    have h := hanti hmn.le (Metric.mem_closedBall_self (norm_nonneg (c n)))
    exact hm.not_ge (by simpa only [Metric.mem_closedBall, dist_eq_norm] using h)
  have h := hanti hnm (Metric.mem_closedBall_self (norm_nonneg (c m)))
  have hdist : ‖a m - a n‖ ≤ ‖c n‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using h
  exact ⟨m, hdist, hm.trans_le (by simpa only [norm_sub_rev] using hdist)⟩

/-- A disc whose radius parameter has norm at least one, about a centre in the closed unit disc,
is the whole closed unit disc. -/
theorem closedSubdisc_eq_univ {a c : K} (ha : ‖a‖ ≤ 1) (hc : 1 ≤ ‖c‖) :
    closedSubdisc a c = Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  rw [← closedSubdisc_zero_one (K := K)]
  exact closedSubdisc_subset_closedSubdisc (by rw [zero_sub, norm_neg]; exact ha.trans hc)
    (by rwa [norm_one])

/-- **Far-apart discs are disjoint**: if `max ‖c‖ ‖d‖ < ‖a - b‖`, no point lies in both
`D(a, |c|)` and `D(b, |d|)`, since at such a point `a - b = (T - b) - (T - a)` would be dominated
by `c` or `d`. -/
theorem disjoint_closedSubdisc {a b c d : K} (h : max ‖c‖ ‖d‖ < ‖a - b‖) :
    Disjoint (closedSubdisc a c) (closedSubdisc b d) := by
  rw [Set.disjoint_left]
  intro v hva hvb
  rw [mem_closedSubdisc, ← valuation_le_iff] at hva hvb
  have key : v.1.valuation (C (a - b)) ≤ max (v.1.valuation (C c)) (v.1.valuation (C d)) := by
    rw [show C (a - b) = (T - C b) - (T - C a) by rw [map_sub]; ring]
    exact (Valuation.map_sub _ _ _).trans
      (max_le (hvb.1.trans (le_max_right _ _)) (hva.1.trans (le_max_left _ _)))
  rcases le_max_iff.mp key with hc | hd
  · rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff] at hc
    exact (h.trans_le hc).not_ge (le_max_left _ _)
  · rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff] at hd
    exact (h.trans_le hd).not_ge (le_max_right _ _)

/-- **A point of `D(a, |c|)` takes the value of the constant `a - b` on `T - b`** for every `b`
outside the disc: there `T - b = (T - a) + (a - b)` with `x(T - a) ≤ x(c) < x(a - b)`. -/
theorem valuation_weightedX_sub_weightedC_of_mem_closedSubdisc {x : closedPolydisc 1 K}
    {a c : K} (hx : x ∈ closedSubdisc a c) {b : K} (hb : ‖c‖ < ‖b - a‖) :
    x.1.valuation (T - C b) = x.1.valuation (C (a - b)) := by
  have hsplit : T - C b = (T - C a) + C (a - b) := by
    rw [map_sub]
    ring
  rw [hsplit, Valuation.map_add_eq_of_lt_right]
  refine ((valuation_le_iff _ _ _).mpr ((mem_closedSubdisc a c x).mp hx).1).trans_lt ?_
  rw [← not_le, closedPolydisc_valuation_weightedC_le_iff, norm_sub_rev]
  exact hb.not_ge

/-- **A classical point `x_b` lies in `D(a, |c|)` exactly when `‖b - a‖ ≤ ‖c‖` and `c ≠ 0`**,
whichever point `x` of `Spa (K, K°)` it is built from. -/
theorem classicalPoint_mem_closedSubdisc_iff [CompleteSpace K] (x : spa (powerBoundedSubring K))
    (b : Fin 1 → K) (hb : ∀ i, IsPowerBounded (b i)) (a c : K) :
    classicalPoint x b hb ∈ closedSubdisc a c ↔ ‖b 0 - a‖ ≤ ‖c‖ ∧ c ≠ 0 := by
  rw [mem_closedSubdisc, classicalPoint_vle, classicalPoint_vle, map_sub, evalAtHom_weightedX,
    evalAtHom_weightedC, evalAtHom_weightedC, map_zero, vle_iff_norm_le_of_mem_spa x.2,
    vle_iff_norm_le_of_mem_spa x.2, norm_zero, norm_le_zero_iff]

end NormedField

/-! ### The points of the disc in `D(a, |c|)` -/

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  {r : ℝ}

/-- **The Gauss point `η_r` lies in `D(a, |c|)` exactly when `‖a‖ ≤ ‖c‖` and `r ≤ ‖c‖`**, since
its Gauss norm of `T - a` is `max r ‖a‖`. -/
theorem gaussPoint_mem_closedSubdisc_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1) (a c : K) :
    gaussPoint hr₀ hr₁ ∈ closedSubdisc a c ↔ ‖a‖ ≤ ‖c‖ ∧ r ≤ ‖c‖ := by
  rw [mem_closedSubdisc, gaussPoint_vle_iff, gaussPoint_vle_zero_iff, ← NNReal.coe_le_coe,
    coe_closedDiscGaussValuation_weightedX_sub_weightedC, closedDiscGaussValuation_weightedC,
    coe_nnnorm, max_le_iff, map_eq_zero_iff _ (weightedC_injective _ isWeightFamily_one_weight)]
  exact ⟨fun h ↦ ⟨h.1.2, h.1.1⟩, fun h ↦
    ⟨⟨h.2, h.1⟩, fun hc ↦ hr₀.not_ge (h.2.trans (by rw [hc, norm_zero]))⟩⟩

/-- **`η_{r⁻}` lies in `D(0, |c|)` exactly when `r ≤ ‖c‖`.** At `‖c‖ = r` the constant `c` is
strictly larger than `T` just below radius `r`. -/
theorem gaussPointBelow_mem_closedSubdisc_zero_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1) (c : K) :
    gaussPointBelow hr₀ hr₁ ∈ closedSubdisc 0 c ↔ r ≤ ‖c‖ := by
  rw [mem_closedSubdisc, map_zero, sub_zero, gaussPointBelow_vle_iff, gaussPointBelow_vle_iff,
    map_zero, le_zero_iff, closedDiscGaussValuationBelow_eq_zero_iff,
    map_eq_zero_iff _ (weightedC_injective _ isWeightFamily_one_weight)]
  -- the Gauss norms of radius `r` of `T` and `c` are `r` and `‖c‖`
  have hT := coe_closedDiscGaussValuation_weightedX (R := K) hr₀ hr₁
  have hC := closedDiscGaussValuation_weightedC (R := K) hr₀ hr₁ c
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_, fun hc ↦ hr₀.not_ge (h.trans (by rw [hc, norm_zero]))⟩⟩
  · by_contra! hlt
    refine (closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁ ?_).not_ge h.1
    rwa [← NNReal.coe_lt_coe, hT, hC, coe_nnnorm]
  · rcases h.lt_or_eq with hlt | heq
    · refine (closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁ ?_).le
      rwa [← NNReal.coe_lt_coe, hT, hC, coe_nnnorm]
    · exact le_of_not_ge (not_closedDiscGaussValuationBelow_weightedC_le hr₀ hr₁ heq.symm)

/-- **`η_{r⁺}` lies in `D(0, |c|)` exactly when `r < ‖c‖`.** At `‖c‖ = r` the variable `T` is
strictly larger than `c` just above radius `r`, so the disc of radius `r` contains `η_r` and
`η_{r⁻}` but not `η_{r⁺}`. -/
theorem gaussPointAbove_mem_closedSubdisc_zero_iff (hr₀ : 0 < r) (hr₁ : r < 1) (c : K) :
    gaussPointAbove hr₀ hr₁ ∈ closedSubdisc 0 c ↔ r < ‖c‖ := by
  rw [mem_closedSubdisc, map_zero, sub_zero, gaussPointAbove_vle_iff, gaussPointAbove_vle_iff,
    map_zero, le_zero_iff, closedDiscGaussValuationAbove_eq_zero_iff,
    map_eq_zero_iff _ (weightedC_injective _ isWeightFamily_one_weight)]
  -- the Gauss norms of radius `r` of `T` and `c` are `r` and `‖c‖`
  have hT := coe_closedDiscGaussValuation_weightedX (R := K) hr₀ hr₁.le
  have hC := closedDiscGaussValuation_weightedC (R := K) hr₀ hr₁.le c
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_, fun hc ↦ hr₀.not_gt (h.trans_eq (by rw [hc, norm_zero]))⟩⟩
  · by_contra! hle
    rcases hle.lt_or_eq with hlt | heq
    · refine (closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁.le ?_).not_ge h.1
      rwa [← NNReal.coe_lt_coe, hT, hC, coe_nnnorm]
    · exact not_closedDiscGaussValuationAbove_weightedX_le hr₀ hr₁.le heq h.1
  · refine (closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁.le ?_).le
    rwa [← NNReal.coe_lt_coe, hT, hC, coe_nnnorm]

variable [CompleteSpace K]

/-- **The point `η_{b,r}` lies in `D(a, |c|)` exactly when `‖b - a‖ ≤ ‖c‖` and `r ≤ ‖c‖`.**
Translating by `b` turns `T - a` into `T - (a - b)`, whose Gauss norm of radius `r` is
`max r ‖a - b‖`. -/
theorem discPoint_mem_closedSubdisc_iff (b : K) (hb : ‖b‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (a c : K) : discPoint b hb hr₀ hr₁ ∈ closedSubdisc a c ↔ ‖b - a‖ ≤ ‖c‖ ∧ r ≤ ‖c‖ := by
  rw [mem_closedSubdisc, discPoint_vle_iff, discPoint_vle_zero_iff, taylorHom_weightedC,
    ← NNReal.coe_le_coe, coe_closedDiscGaussValuation_taylorHom_weightedX_sub_weightedC hb,
    closedDiscGaussValuation_weightedC, coe_nnnorm, max_le_iff, norm_sub_rev,
    map_eq_zero_iff _ (weightedC_injective _ isWeightFamily_one_weight)]
  exact ⟨fun h ↦ ⟨h.1.2, h.1.1⟩, fun h ↦
    ⟨⟨h.2, h.1⟩, fun hc ↦ hr₀.not_ge (h.2.trans (by rw [hc, norm_zero]))⟩⟩

/-- **Inclusion of discs**: for `‖a‖ ≤ 1` and `0 < ‖c‖ ≤ 1`, `D(a, |c|) ⊆ D(b, |d|)` exactly
when `‖a - b‖ ≤ ‖d‖` and `‖c‖ ≤ ‖d‖`. The point `η_{a,‖c‖}`
of `D(a, |c|)` witnesses the forward direction. -/
theorem closedSubdisc_subset_closedSubdisc_iff {a c : K} (ha : ‖a‖ ≤ 1) (hc₀ : c ≠ 0)
    (hc₁ : ‖c‖ ≤ 1) (b d : K) :
    closedSubdisc a c ⊆ closedSubdisc b d ↔ ‖a - b‖ ≤ ‖d‖ ∧ ‖c‖ ≤ ‖d‖ := by
  refine ⟨fun h ↦ ?_, fun h ↦ closedSubdisc_subset_closedSubdisc h.1 h.2⟩
  have hc : 0 < ‖c‖ := norm_pos_iff.mpr hc₀
  exact (discPoint_mem_closedSubdisc_iff a ha hc hc₁ b d).mp
    (h ((discPoint_mem_closedSubdisc_iff a ha hc hc₁ a c).mpr (by simp)))

/-- **Equality of discs**: for centres in the closed unit disc and radius parameters of norm in
`(0, 1]`, `D(a, |c|) = D(b, |d|)` exactly when `‖c‖ = ‖d‖` and `‖a - b‖ ≤ ‖c‖`. -/
theorem closedSubdisc_eq_closedSubdisc_iff {a b c d : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hc₀ : c ≠ 0) (hc₁ : ‖c‖ ≤ 1) (hd₀ : d ≠ 0) (hd₁ : ‖d‖ ≤ 1) :
    closedSubdisc a c = closedSubdisc b d ↔ ‖c‖ = ‖d‖ ∧ ‖a - b‖ ≤ ‖c‖ := by
  rw [Set.Subset.antisymm_iff, closedSubdisc_subset_closedSubdisc_iff ha hc₀ hc₁,
    closedSubdisc_subset_closedSubdisc_iff hb hd₀ hd₁, norm_sub_rev b a]
  constructor
  · rintro ⟨⟨-, hcd⟩, hba, hdc⟩
    exact ⟨le_antisymm hcd hdc, hba⟩
  · rintro ⟨hcd, hab⟩
    exact ⟨⟨hcd ▸ hab, hcd.le⟩, hab, hcd.ge⟩

/-- **The point `η_{b,r⁺}` lies in `D(a, |c|)` exactly when `‖b - a‖ ≤ ‖c‖` and `r < ‖c‖`.**
On `T - a` it takes the value of the constant `a - b` when `r < ‖a - b‖`, and otherwise a value
just above the constants of norm `r`. -/
theorem discPointAbove_mem_closedSubdisc_iff (b : K) (hb : ‖b‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1)
    (a c : K) : discPointAbove b hb hr₀ hr₁ ∈ closedSubdisc a c ↔ ‖b - a‖ ≤ ‖c‖ ∧ r < ‖c‖ := by
  rw [mem_closedSubdisc, ← map_zero C, closedPolydisc_vle_weightedC_iff, norm_zero,
    norm_le_zero_iff, ← valuation_le_iff, valuation_weightedX_sub_weightedC_discPointAbove,
    norm_sub_rev b a]
  split_ifs with h
  · rw [valuation_le_iff, discPointAbove_vle_weightedC_iff]
    grind [norm_eq_zero]
  · rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff]
    grind [norm_eq_zero]

/-- **The point `η_{b,r⁻}` lies in `D(a, |c|)` exactly when `‖b - a‖ ≤ ‖c‖` and `r ≤ ‖c‖`**, as
for `η_{b,r}`. On `T - a` it takes the value of the constant `a - b` when `r ≤ ‖a - b‖`, and
otherwise a value just below the constants of norm `r`. -/
theorem discPointBelow_mem_closedSubdisc_iff (b : K) (hb : ‖b‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (a c : K) : discPointBelow b hb hr₀ hr₁ ∈ closedSubdisc a c ↔ ‖b - a‖ ≤ ‖c‖ ∧ r ≤ ‖c‖ := by
  rw [mem_closedSubdisc, ← map_zero C, closedPolydisc_vle_weightedC_iff, norm_zero,
    norm_le_zero_iff, ← valuation_le_iff, valuation_weightedX_sub_weightedC_discPointBelow,
    norm_sub_rev b a]
  split_ifs with h
  · rw [valuation_le_iff, discPointBelow_vle_weightedC_iff]
    grind [norm_eq_zero]
  · rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff]
    grind [norm_eq_zero]

end NontriviallyNormedField

section NoMinimum

open Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]

omit [IsUltrametricDist K] in
/-- If `b ↦ x(T - b)` attains no minimum, then every value `x(T - b)` is the value of a nonzero
constant. -/
private theorem exists_valuation_weightedX_sub_weightedC_eq {x : closedPolydisc 1 K}
    (hmin : ¬ ∃ a₀ : K, ∀ b : K, x.1.toValuativeRel.vle (T - C a₀) (T - C b)) (b : K) :
    ∃ e : K, e ≠ 0 ∧ x.1.valuation (T - C b) = x.1.valuation (C e) := by
  push Not at hmin
  obtain ⟨b', hb'⟩ := hmin b
  rw [← valuation_le_iff, not_le] at hb'
  have he := valuation_weightedX_sub_weightedC_eq_of_lt hb'
  refine ⟨b' - b, fun h0 ↦ ?_, he⟩
  rw [h0, map_zero, map_zero] at he
  exact (zero_le.trans_lt hb').ne' he

/-- For `b` in the unit disc and `b'` off it, `x(T - b) ≤ x(1) < x(b') = x(T - b')`. -/
theorem valuation_weightedX_sub_weightedC_lt_of_one_lt (x : closedPolydisc 1 K)
    {b b' : K} (hb : ‖b‖ ≤ 1) (hb' : 1 < ‖b'‖) :
    x.1.valuation (T - C b) < x.1.valuation (T - C b') := by
  have hmem₀ : x ∈ closedSubdisc 0 1 := by
    rw [closedSubdisc_zero_one]
    exact Set.mem_univ x
  have hmem : x ∈ closedSubdisc b 1 := by
    rw [closedSubdisc_eq_univ hb (by simp)]
    exact Set.mem_univ x
  rw [valuation_weightedX_sub_weightedC_of_mem_closedSubdisc (b := b') hmem₀ (by simpa using hb')]
  refine ((valuation_le_iff _ _ _).mpr ((mem_closedSubdisc _ _ _).mp hmem).1).trans_lt ?_
  rw [← not_le, closedPolydisc_valuation_weightedC_le_iff]
  simpa using hb'

/-- **A point on which `b ↦ x(T - b)` attains no minimum lies in a decreasing sequence of discs
with no common point.** Every value `x(T - b)` is the value `x(e)` of a constant, and the norms
`‖e‖` for `‖b‖ ≤ 1` have an infimum which is not attained, since an `e` attaining it would make `b`
a minimum. The discs `D(b, |e|)` along a sequence of norms decreasing to this infimum work. -/
theorem exists_forall_mem_closedSubdisc {x : closedPolydisc 1 K}
    (hmin : ¬ ∃ a₀ : K, ∀ b : K, x.1.toValuativeRel.vle (T - C a₀) (T - C b)) :
    ∃ a c : ℕ → K, (∀ n, ‖a n‖ ≤ 1) ∧ (∀ n, c n ≠ 0) ∧ (∀ n, ‖c n‖ ≤ 1) ∧
      (∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖) ∧ (∀ n, ‖c (n + 1)‖ ≤ ‖c n‖) ∧
      (∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) ∧ ∀ n, x ∈ closedSubdisc (a n) (c n) := by
  have hval := exists_valuation_weightedX_sub_weightedC_eq hmin
  have hCle := closedPolydisc_valuation_weightedC_le_iff x
  have hClt (u w : K) : x.1.valuation (C u) < x.1.valuation (C w) ↔ ‖u‖ < ‖w‖ := by
    rw [← not_le, ← not_le, hCle]
  -- the norms `‖e‖` with `x(T - b) = x(e)` for some `b` in the unit disc
  set S : Set ℝ :=
    {t | ∃ b e : K, ‖b‖ ≤ 1 ∧ x.1.valuation (T - C b) = x.1.valuation (C e) ∧ ‖e‖ = t}
  have hS : S.Nonempty :=
    let ⟨e, _, he⟩ := hval 0
    ⟨‖e‖, 0, e, by simp, he, rfl⟩
  have hbdd : BddBelow S := ⟨0, by rintro _ ⟨-, e, -, -, rfl⟩; exact norm_nonneg e⟩
  -- the infimum of `S` is not attained: if `‖e‖ ≤ sInf S` then `b` is a minimum
  have hlt {b e : K} (hb : ‖b‖ ≤ 1) (he : x.1.valuation (T - C b) = x.1.valuation (C e)) :
      sInf S < ‖e‖ := by
    refine lt_of_not_ge fun hinf ↦ hmin ⟨b, fun b' ↦ ?_⟩
    rw [← valuation_le_iff]
    rcases le_or_gt ‖b'‖ 1 with hb' | hb'
    · obtain ⟨e', -, he'⟩ := hval b'
      rw [he, he', hCle]
      exact hinf.trans (csInf_le hbdd ⟨b', e', hb', he', rfl⟩)
    · exact (valuation_weightedX_sub_weightedC_lt_of_one_lt x hb hb').le
  obtain ⟨u, hu, hlim, huS⟩ := exists_seq_tendsto_sInf hS hbdd
  choose a c ha hac hcu using huS
  have hc₀ (n : ℕ) : c n ≠ 0 := by
    obtain ⟨e, he, hxe⟩ := hval (a n)
    refine (closedPolydisc_valuation_weightedC_eq_zero_iff x _).not.mp ?_
    rw [← hac n, hxe]
    exact (closedPolydisc_valuation_weightedC_eq_zero_iff x e).not.mpr he
  have hc₁ (n : ℕ) : ‖c n‖ ≤ 1 := by
    have hmem : x ∈ closedSubdisc (a n) 1 := by
      rw [closedSubdisc_eq_univ (ha n) (by simp)]
      exact Set.mem_univ x
    have := ((mem_closedSubdisc _ _ _).mp hmem).1
    rwa [← valuation_le_iff, hac n, hCle, norm_one] at this
  have hcc (n : ℕ) : ‖c (n + 1)‖ ≤ ‖c n‖ := by
    rw [hcu, hcu]
    exact hu n.le_succ
  refine ⟨a, c, ha, hc₀, hc₁, fun n ↦ norm_sub_le_of_valuation_eq (hac n) (hac (n + 1)) (hcc n),
    hcc, fun b ↦ ?_, fun n ↦ ?_⟩
  · -- some `x(T - aₙ)` is below `x(T - b)`; then `x(T - b) = x(aₙ - b)`, so `‖cₙ‖ < ‖aₙ - b‖`
    obtain ⟨n, hn⟩ : ∃ n, x.1.valuation (T - C (a n)) < x.1.valuation (T - C b) := by
      rcases le_or_gt ‖b‖ 1 with hb | hb
      · obtain ⟨e, -, he⟩ := hval b
        obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (hlt hb he))).exists
        rw [← hcu, ← hClt, ← hac n, ← he] at hn
        exact ⟨n, hn⟩
      · exact ⟨0, valuation_weightedX_sub_weightedC_lt_of_one_lt x (ha 0) hb⟩
    refine ⟨n, ?_⟩
    rw [norm_sub_rev, ← hClt, ← hac n, ← valuation_weightedX_sub_weightedC_eq_of_lt hn]
    exact hn
  · rw [mem_closedSubdisc, ← valuation_le_iff, ← valuation_le_iff, map_zero, le_zero_iff]
    exact ⟨(hac n).le, fun h ↦ hc₀ n ((closedPolydisc_valuation_weightedC_eq_zero_iff x _).mp h)⟩

end NoMinimum

end TauCeti.ValuationSpectrum
