/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.DiscPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

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
  closed disc of radius `r`.

The points `η_{b,r}` also determine the discs themselves. For `‖a‖ ≤ 1` and `0 < ‖c‖ ≤ 1`,
`D(a, |c|) ⊆ D(b, |d|)` exactly when `‖a - b‖ ≤ ‖d‖` and `‖c‖ ≤ ‖d‖`, and two such discs are
equal exactly when their radii agree and each centre lies in the other disc. If
`max ‖c‖ ‖d‖ < ‖a - b‖`, the discs `D(a, |c|)` and `D(b, |d|)` are disjoint.

## Main definitions

* `TauCeti.ValuationSpectrum.closedSubdisc`: the rational subset `D(a, |c|)` of the closed unit
  disc.

## Main results

* `TauCeti.ValuationSpectrum.closedSubdisc_eq_rationalSubset`,
  `TauCeti.ValuationSpectrum.isOpen_closedSubdisc` and
  `TauCeti.ValuationSpectrum.isCompact_closedSubdisc`: `D(a, |c|)` is the rational subset
  `R({T - a, c} / c)`, hence open and, for `c` a unit, quasi-compact.
* `TauCeti.ValuationSpectrum.closedSubdisc_zero_one`: `D(0, 1)` is the whole closed unit disc,
  and `TauCeti.ValuationSpectrum.closedSubdisc_zero_right`: `D(a, |0|)` is empty.
* `TauCeti.ValuationSpectrum.classicalPoint_mem_closedSubdisc_iff`,
  `TauCeti.ValuationSpectrum.gaussPoint_mem_closedSubdisc_iff`,
  `TauCeti.ValuationSpectrum.discPoint_mem_closedSubdisc_iff`,
  `TauCeti.ValuationSpectrum.gaussPointBelow_mem_closedSubdisc_zero_iff` and
  `TauCeti.ValuationSpectrum.gaussPointAbove_mem_closedSubdisc_zero_iff`: which points of the
  closed unit disc lie in `D(a, |c|)`.
* `TauCeti.ValuationSpectrum.closedSubdisc_subset_closedSubdisc_iff`,
  `TauCeti.ValuationSpectrum.closedSubdisc_eq_closedSubdisc_iff` and
  `TauCeti.ValuationSpectrum.disjoint_closedSubdisc`: inclusion, equality and disjointness of
  discs.

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

/-- `D(a, |c|)` is quasi-compact over a Huber ring when `c` is a unit. -/
theorem isCompact_closedSubdisc [IsHuberRing K] (a : K) {c : K} (hc : IsUnit c) :
    IsCompact (closedSubdisc a c) := by
  classical
  have hspan : Ideal.span (({T - C a, C c} : Finset (𝒯 K)) : Set (𝒯 K)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) (hc.map C)
  have hcompact := isCompact_of_mem_spaRationalFamily (Aplus := powerBoundedSubring (𝒯 K))
    (mem_spaRationalFamily_iff.mpr ⟨{T - C a, C c}, C c, by rw [hspan]; simp, rfl⟩)
  rw [closedSubdisc_eq_rationalSubset]
  exact (Homeomorph.setCongr (closedPolydisc_def 1 K)).isClosedEmbedding.isCompact_preimage
    hcompact

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
  rw [mem_closedSubdisc, discPoint_vle_iff, discPoint_vle_zero_iff, map_sub, taylorHom_weightedX,
    taylorHom_weightedC, taylorHom_weightedC,
    show T + C b - C a = T - C (a - b) by rw [map_sub]; ring, ← NNReal.coe_le_coe,
    coe_closedDiscGaussValuation_weightedX_sub_weightedC, closedDiscGaussValuation_weightedC,
    coe_nnnorm, max_le_iff, norm_sub_rev,
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

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
