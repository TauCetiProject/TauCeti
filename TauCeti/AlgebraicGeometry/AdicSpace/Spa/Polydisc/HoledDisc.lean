/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Subdisc

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Holed discs in the closed unit disc

For `a, c ∈ K` and finitely many pairs `(bᵢ, dᵢ)`, the *holed disc* in the closed unit disc
`Spa (K⟨T⟩, K⟨T⟩°)` is the closed subdisc `D(a, |c|)` with the open discs `D⁻(bᵢ, |dᵢ|)` removed:

```text
D(a, |c|) ∖ ⋃ᵢ D⁻(bᵢ, |dᵢ|) = {v : v(T - a) ≤ v(c) ≠ 0 and v(dᵢ) ≤ v(T - bᵢ) for every i}.
```

With no holes this is the closed subdisc `TauCeti.ValuationSpectrum.closedSubdisc`; with the single
hole `(a, d)` it is the closed annulus `{|d| ≤ |T - a| ≤ |c|}`. When the `dᵢ` are units the holed
disc is open, and when moreover `T - a` and `c` generate an open ideal (for instance when `c` is a
unit) it is the intersection of the rational subsets `R({T - a, c} / c)` and `R({dᵢ} / (T - bᵢ))`,
so it is rational and quasi-compact. Holed discs are the shapes that rational subdomains of the
closed unit disc are made of: over an algebraically closed field, a connected affinoid subset of
the projective line is the complement of finitely many open discs (Fresnel–van der Put,
Chapter 2).

Over a complete nonarchimedean field this file decides which points of Wedhorn's description of
the closed unit disc (Example 7.57) lie in a holed disc:

* the classical point `x_y` lies in it exactly when `y` does, that is when `‖y - a‖ ≤ ‖c‖`,
  `c ≠ 0` and `‖dᵢ‖ ≤ ‖y - bᵢ‖` for every `i`;
* the point `η_{e,r}` exactly when `‖e - a‖ ≤ ‖c‖`, `r ≤ ‖c‖` and `‖dᵢ‖ ≤ max r ‖e - bᵢ‖`;
* the point `η_{e,r⁺}` exactly when `‖e - a‖ ≤ ‖c‖`, `r < ‖c‖` and `‖dᵢ‖ ≤ max r ‖e - bᵢ‖`;
* the point `η_{e,r⁻}` exactly when `‖e - a‖ ≤ ‖c‖`, `r ≤ ‖c‖` and, for every `i`, `‖dᵢ‖ < r` or
  `‖dᵢ‖ ≤ ‖e - bᵢ‖`.

In particular a holed disc about a centre `‖a‖ ≤ 1` of radius `0 < ‖c‖ ≤ 1` is empty exactly when
one of its holes swallows the whole of `D(a, |c|)`, that is when `max ‖c‖ ‖a - bᵢ‖ < ‖dᵢ‖` for some
`i`; otherwise it contains the Gauss point `η_{a,‖c‖}` of its outer disc.

## Main definitions

* `TauCeti.ValuationSpectrum.holedDisc`: the holed disc `D(a, |c|) ∖ ⋃ᵢ D⁻(bᵢ, |dᵢ|)`.

## Main results

* `TauCeti.ValuationSpectrum.isOpen_holedDisc`: a holed disc whose holes have unit radius
  parameters is open.
* `TauCeti.ValuationSpectrum.holedDisc_mem_spaRationalFamily` and
  `TauCeti.ValuationSpectrum.isCompact_holedDisc`: if moreover `T - a` and `c` generate an open
  ideal, the holed disc is a rational subset, hence quasi-compact.
* `TauCeti.ValuationSpectrum.classicalPoint_mem_holedDisc_iff`,
  `TauCeti.ValuationSpectrum.discPoint_mem_holedDisc_iff`,
  `TauCeti.ValuationSpectrum.discPointAbove_mem_holedDisc_iff` and
  `TauCeti.ValuationSpectrum.discPointBelow_mem_holedDisc_iff`: which points lie in a holed disc.
* `TauCeti.ValuationSpectrum.holedDisc_eq_empty_iff`: a holed disc is empty exactly when its
  outer radius vanishes or one of its holes contains its outer disc.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* J. Fresnel, M. van der Put, *Rigid Analytic Geometry and Its Applications*, Progress in
  Mathematics 218, Birkhäuser (2004), Chapter 2, for the affinoid subsets of the projective line.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §7.2, for rational and Laurent
  subdomains of affinoid spaces.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

local notation "𝒯" K => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set _)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set _)) isWeightFamily_one_weight

variable {ι : Type*}

/-! ### Holed discs as rational subsets -/

section TopologicalRing

variable {K : Type*} [CommRing K] [TopologicalSpace K] [NonarchimedeanRing K]

/-- **The holed disc `D(a, |c|) ∖ ⋃ᵢ D⁻(bᵢ, |dᵢ|)`** in the closed unit disc: the points of the
closed subdisc `D(a, |c|)` with `v(dᵢ) ≤ v(T - bᵢ)` for every `i`. For a nonarchimedean normed
field `K` this removes from `D(a, |c|)` the open discs of radius `‖dᵢ‖` about the `bᵢ`. -/
def holedDisc (a c : K) (b d : ι → K) : Set (closedPolydisc 1 K) :=
  closedSubdisc a c ∩ ⋂ i, {v | v.1.toValuativeRel.vle (C (d i)) (T - C (b i))}

/-- Membership in a holed disc is membership in its outer disc together with the defining
inequality of each hole. -/
@[simp]
theorem mem_holedDisc (a c : K) (b d : ι → K) (v : closedPolydisc 1 K) :
    v ∈ holedDisc a c b d ↔
      v ∈ closedSubdisc a c ∧ ∀ i, v.1.toValuativeRel.vle (C (d i)) (T - C (b i)) := by
  simp [holedDisc]

/-- A holed disc lies in its outer disc. -/
theorem holedDisc_subset_closedSubdisc (a c : K) (b d : ι → K) :
    holedDisc a c b d ⊆ closedSubdisc a c :=
  Set.inter_subset_left

/-- **A holed disc without holes is its outer disc.** -/
@[simp]
theorem holedDisc_of_isEmpty [IsEmpty ι] (a c : K) (b d : ι → K) :
    holedDisc a c b d = closedSubdisc a c := by
  ext v
  simp

/-- A hole whose radius parameter is a unit `d` is the basic open `{v : v(d) ≤ v(T - b) ≠ 0}`: the
inequality `v(d) ≤ v(T - b)` already forces `v(T - b) ≠ 0`. -/
private theorem setOf_vle_eq_basicOpen (b : K) {d : K} (hd : IsUnit d) :
    {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C d) (T - C b)} =
      Subtype.val ⁻¹' basicOpen (C d) (T - C b) := by
  ext v
  have hd₀ : v.1.valuation (C d) ≠ 0 := ((hd.map C).map v.1.valuation).ne_zero
  rw [Set.mem_ofPred_eq, Set.mem_preimage, mem_basicOpen_iff, iff_self_and,
    ← valuation_le_iff, ← valuation_le_iff, map_zero, le_zero_iff]
  exact fun h h₀ ↦ hd₀ (le_zero_iff.mp (h₀ ▸ h))

/-- A hole whose radius parameter is a unit `d` is the rational subset `R({d} / (T - b))`: the
inequality `v(d) ≤ v(T - b)` already forces `v(T - b) ≠ 0`. -/
private theorem setOf_vle_eq_rationalSubset (b : K) {d : K} (hd : IsUnit d) :
    {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C d) (T - C b)} =
      Subtype.val ⁻¹' rationalSubset (powerBoundedSubring (𝒯 K)) {C d} (T - C b) := by
  ext v
  have hv : v.1 ∈ spa (powerBoundedSubring (𝒯 K)) := closedPolydisc_def 1 K ▸ v.2
  have hd₀ : v.1.valuation (C d) ≠ 0 := ((hd.map C).map v.1.valuation).ne_zero
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_rationalSubset_iff, hv, Finset.mem_singleton,
    forall_eq, true_and, iff_self_and]
  rw [← valuation_le_iff, ← valuation_le_iff, map_zero, le_zero_iff]
  exact fun h h₀ ↦ hd₀ (le_zero_iff.mp (h₀ ▸ h))

/-- **A holed disc whose holes have unit radius parameters is open** in the closed unit disc: it
is the intersection of the open subset `closedSubdisc a c` with the finitely many basic opens
`{v : v(dᵢ) ≤ v(T - bᵢ) ≠ 0}`. -/
theorem isOpen_holedDisc [Finite ι] (a c : K) (b : ι → K) {d : ι → K} (hd : ∀ i, IsUnit (d i)) :
    IsOpen (holedDisc a c b d) :=
  (isOpen_closedSubdisc a c).inter <| isOpen_iInter_of_finite fun i ↦
    setOf_vle_eq_basicOpen (b i) (hd i) ▸ (isOpen_basicOpen _ _).preimage continuous_subtype_val

/-- **A holed disc is a rational subset** of the closed unit disc over a Huber ring when `T - a`
and `c` generate an open ideal and the holes have unit radius parameters: it is the intersection
of the rational subsets `R({T - a, c} / c)` and `R({dᵢ} / (T - bᵢ))`, and rational subsets are
closed under finite intersection (Wedhorn, Remark 7.30(5)). -/
theorem holedDisc_mem_spaRationalFamily [IsHuberRing K] [Finite ι] (a c : K)
    (hT : IsOpen (Ideal.span ({T - C a, C c} : Set (𝒯 K)) : Set (𝒯 K))) (b : ι → K) {d : ι → K}
    (hd : ∀ i, IsUnit (d i)) :
    (Homeomorph.setCongr (closedPolydisc_def 1 K)).symm ⁻¹' holedDisc a c b d ∈
      spaRationalFamily (powerBoundedSubring (𝒯 K)) := by
  classical
  have hhole (i : ι) : (Homeomorph.setCongr (closedPolydisc_def 1 K)).symm ⁻¹'
      {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C (d i)) (T - C (b i))} ∈
      spaRationalFamily (powerBoundedSubring (𝒯 K)) := by
    have hspan : Ideal.span (({C (d i)} : Finset (𝒯 K)) : Set (𝒯 K)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) ((hd i).map C)
    rw [setOf_vle_eq_rationalSubset _ (hd i)]
    exact mem_spaRationalFamily_iff.mpr ⟨_, _, by rw [hspan]; simp, rfl⟩
  rw [holedDisc, Set.preimage_inter, Set.preimage_iInter]
  exact inter_mem_spaRationalFamily (closedSubdisc_mem_spaRationalFamily a c hT)
    (iInter_mem_spaRationalFamily hhole)

/-- **A holed disc is quasi-compact** when `T - a` and `c` generate an open ideal and the holes
have unit radius parameters, being rational. -/
theorem isCompact_holedDisc [IsHuberRing K] [Finite ι] (a c : K)
    (hT : IsOpen (Ideal.span ({T - C a, C c} : Set (𝒯 K)) : Set (𝒯 K))) (b : ι → K) {d : ι → K}
    (hd : ∀ i, IsUnit (d i)) : IsCompact (holedDisc a c b d) := by
  have h := isCompact_of_mem_spaRationalFamily (holedDisc_mem_spaRationalFamily a c hT b hd)
  rwa [Homeomorph.isCompact_preimage] at h

end TopologicalRing

/-! ### Holed discs over a normed field -/

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]

/-- **A hole that swallows the outer disc empties the holed disc**: if
`max ‖c‖ ‖a - bᵢ‖ < ‖dᵢ‖`, then on `D(a, |c|)` the value of `T - bᵢ = (T - a) + (a - bᵢ)` stays
below `dᵢ`. -/
theorem holedDisc_eq_empty_of_lt {a c : K} {b d : ι → K} (i : ι)
    (h : max ‖c‖ ‖a - b i‖ < ‖d i‖) : holedDisc a c b d = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun v hv ↦ ?_
  rw [mem_holedDisc, mem_closedSubdisc] at hv
  have hT := (valuation_le_iff _ _ _).mpr hv.1.1
  have hd := (valuation_le_iff _ _ _).mpr (hv.2 i)
  have hsplit : T - C (b i) = (T - C a) + C (a - b i) := by
    rw [map_sub]
    ring
  have key : v.1.valuation (C (d i)) ≤ max (v.1.valuation (C c)) (v.1.valuation (C (a - b i))) := by
    refine hd.trans ?_
    rw [hsplit]
    exact (Valuation.map_add _ _ _).trans (max_le_max hT le_rfl)
  rcases le_max_iff.mp key with hc | hab
  · rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff] at hc
    exact (h.trans_le hc).not_ge (le_max_left _ _)
  · rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff] at hab
    exact (h.trans_le hab).not_ge (le_max_right _ _)

/-- **A classical point `x_y` lies in a holed disc exactly when `y` does**: `‖y - a‖ ≤ ‖c‖` with
`c ≠ 0`, and `‖dᵢ‖ ≤ ‖y - bᵢ‖` for every `i`. This holds whichever point `x` of `Spa (K, K°)` the
classical point is built from. -/
theorem classicalPoint_mem_holedDisc_iff [CompleteSpace K] (x : spa (powerBoundedSubring K))
    (y : Fin 1 → K) (hy : ∀ i, IsPowerBounded (y i)) (a c : K) (b d : ι → K) :
    classicalPoint x y hy ∈ holedDisc a c b d ↔
      (‖y 0 - a‖ ≤ ‖c‖ ∧ c ≠ 0) ∧ ∀ i, ‖d i‖ ≤ ‖y 0 - b i‖ := by
  rw [mem_holedDisc, classicalPoint_mem_closedSubdisc_iff]
  refine and_congr_right' (forall_congr' fun i ↦ ?_)
  rw [classicalPoint_vle, map_sub, evalAtHom_weightedX, evalAtHom_weightedC, evalAtHom_weightedC,
    vle_iff_norm_le_of_mem_spa x.2]

end NormedField

/-! ### The points `η_{e,r}` and `η_{e,r±}` in a holed disc -/

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K] {r : ℝ}

/-- **The point `η_{e,r}` lies in a holed disc exactly when `‖e - a‖ ≤ ‖c‖`, `r ≤ ‖c‖` and
`‖dᵢ‖ ≤ max r ‖e - bᵢ‖` for every `i`**: its value on `T - bᵢ` is the Gauss norm
`max r ‖e - bᵢ‖`. -/
theorem discPoint_mem_holedDisc_iff (e : K) (he : ‖e‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (a c : K) (b d : ι → K) :
    discPoint e he hr₀ hr₁ ∈ holedDisc a c b d ↔
      (‖e - a‖ ≤ ‖c‖ ∧ r ≤ ‖c‖) ∧ ∀ i, ‖d i‖ ≤ max r ‖e - b i‖ := by
  rw [mem_holedDisc, discPoint_mem_closedSubdisc_iff]
  refine and_congr_right' (forall_congr' fun i ↦ ?_)
  rw [discPoint_vle_iff, taylorHom_weightedC, ← NNReal.coe_le_coe,
    coe_closedDiscGaussValuation_taylorHom_weightedX_sub_weightedC he,
    closedDiscGaussValuation_weightedC, coe_nnnorm, norm_sub_rev]

/-- **The point `η_{e,r⁺}` lies in a holed disc exactly when `‖e - a‖ ≤ ‖c‖`, `r < ‖c‖` and
`‖dᵢ‖ ≤ max r ‖e - bᵢ‖` for every `i`.** Only the outer disc distinguishes it from `η_{e,r}`:
the rank-two point `η_{e,r⁺}` lies outside the disc of radius `r` about `e`. -/
theorem discPointAbove_mem_holedDisc_iff (e : K) (he : ‖e‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1)
    (a c : K) (b d : ι → K) :
    discPointAbove e he hr₀ hr₁ ∈ holedDisc a c b d ↔
      (‖e - a‖ ≤ ‖c‖ ∧ r < ‖c‖) ∧ ∀ i, ‖d i‖ ≤ max r ‖e - b i‖ := by
  rw [mem_holedDisc, discPointAbove_mem_closedSubdisc_iff]
  refine and_congr_right' (forall_congr' fun i ↦ ?_)
  rw [← valuation_le_iff, valuation_weightedX_sub_weightedC_discPointAbove, norm_sub_rev e]
  split_ifs with h
  · rw [valuation_le_iff, discPointAbove_weightedC_vle_iff, max_eq_left h]
  · rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff, max_eq_right (not_le.mp h).le]

/-- **The point `η_{e,r⁻}` lies in a holed disc exactly when `‖e - a‖ ≤ ‖c‖`, `r ≤ ‖c‖` and, for
every `i`, `‖dᵢ‖ < r` or `‖dᵢ‖ ≤ ‖e - bᵢ‖`.** Only the holes distinguish it from `η_{e,r}`: the
rank-two point `η_{e,r⁻}` lies inside the open disc of radius `r` about `e`. -/
theorem discPointBelow_mem_holedDisc_iff (e : K) (he : ‖e‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (a c : K) (b d : ι → K) :
    discPointBelow e he hr₀ hr₁ ∈ holedDisc a c b d ↔
      (‖e - a‖ ≤ ‖c‖ ∧ r ≤ ‖c‖) ∧ ∀ i, ‖d i‖ < r ∨ ‖d i‖ ≤ ‖e - b i‖ := by
  rw [mem_holedDisc, discPointBelow_mem_closedSubdisc_iff]
  refine and_congr_right' (forall_congr' fun i ↦ ?_)
  rw [← valuation_le_iff, valuation_weightedX_sub_weightedC_discPointBelow, norm_sub_rev e]
  split_ifs with h
  · rw [valuation_le_iff, discPointBelow_weightedC_vle_iff]
    grind
  · rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff]
    grind

/-- **Emptiness of holed discs**: for a centre `‖a‖ ≤ 1` and `‖c‖ ≤ 1`, the holed disc
`D(a, |c|) ∖ ⋃ᵢ D⁻(bᵢ, |dᵢ|)` is empty exactly when `c = 0` or some hole contains the whole of
`D(a, |c|)`, that is `max ‖c‖ ‖a - bᵢ‖ < ‖dᵢ‖`. Otherwise the Gauss point `η_{a,‖c‖}` of the
outer disc lies in it. -/
theorem holedDisc_eq_empty_iff {a c : K} (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1) (b d : ι → K) :
    holedDisc a c b d = ∅ ↔ c = 0 ∨ ∃ i, max ‖c‖ ‖a - b i‖ < ‖d i‖ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra! hne
    have hc₀ : 0 < ‖c‖ := norm_pos_iff.mpr hne.1
    refine (Set.eq_empty_iff_forall_notMem.mp h) (discPoint a ha hc₀ hc) ?_
    rw [discPoint_mem_holedDisc_iff]
    exact ⟨⟨by simp, le_rfl⟩, hne.2⟩
  · rintro (rfl | ⟨i, hi⟩)
    · exact Set.subset_eq_empty (holedDisc_subset_closedSubdisc a 0 b d)
        (closedSubdisc_zero_right a)
    · exact holedDisc_eq_empty_of_lt i hi

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
