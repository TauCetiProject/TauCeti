/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Subdisc

import TauCeti.RingTheory.Huber.Normed
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

Over every nontrivially normed ultrametric field, complete or not, every finite union of holed
discs is a rational subset. A holed disc is the intersection of its outer disc with the
complements of its holes, and rational subsets are closed under finite intersections, so by
distributivity it suffices that a finite union of discs and of complements of open discs is
rational. Among the complements only the one of a smallest removed open disc `D⁻(b, |s|)`
matters, and among the discs only those inside it. That case is proved by induction on the number
of discs, from one observation: for units `r`, `σ` with `|r| < |σ|` and any `f`, the complement
`{|f| ≤ |r|} ∪ {|σ| ≤ |f|}` of an open annulus is the rational subset
`R({σ f, f² - r σ} / (f² - r σ))`
(`TauCeti.ValuationSpectrum.setOf_vle_or_vle_mem_spaRationalFamily`).
With `f = T - a` this handles one disc `D(a, |c|) ⊆ D⁻(b, |s|)`. With `f` the product of the
linear factors `T - a` over the centres, it separates the discs, as a group, from the points of
`D⁻(b, |s|)` far from all centres, and the discs near each centre are handled by induction.

## Main definitions

* `TauCeti.ValuationSpectrum.holedDisc`: the holed disc `D(a, |c|) ∖ ⋃ᵢ D⁻(bᵢ, |dᵢ|)`.
* `TauCeti.ValuationSpectrum.IsHoledDiscUnion`: finite unions of holed discs.

## Main results

* `TauCeti.ValuationSpectrum.holedDisc_insert` and
  `TauCeti.ValuationSpectrum.exists_holedDisc_inter_closedSubdisc_eq`: adding a hole, or cutting
  by a disc, gives again a holed disc.
* `TauCeti.ValuationSpectrum.IsHoledDiscUnion.union` and
  `TauCeti.ValuationSpectrum.IsHoledDiscUnion.inter`: finite unions of holed discs are closed
  under finite unions and intersections; `TauCeti.ValuationSpectrum.isHoledDiscUnion_biInter`
  gives closure under finite intersections indexed by a finite set.
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
* `TauCeti.ValuationSpectrum.IsHoledDiscUnion.mem_spaRationalFamily`: every finite union of holed
  discs is a rational subset of the closed unit disc.

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
noncomputable def holedDisc (a c : K) (b d : ι → K) : Set (closedPolydisc 1 K) :=
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

/-- **Adding a hole to a holed disc** intersects it with the hole's defining inequality: for holes
indexed by a finset `s`, adding the index `i` cuts out `{v : v(dᵢ) ≤ v(T - bᵢ)}`. -/
theorem holedDisc_insert [DecidableEq ι] (a c : K) (b d : ι → K) (i : ι) (s : Finset ι) :
    holedDisc a c (fun j : ↥(insert i s) ↦ b j) (fun j ↦ d j) =
      holedDisc a c (fun j : ↥s ↦ b j) (fun j ↦ d j) ∩
        {v | v.1.toValuativeRel.vle (C (d i)) (T - C (b i))} := by
  ext v
  simp only [mem_holedDisc, Subtype.forall, Finset.mem_insert, forall_eq_or_imp, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  tauto

/-! ### Finite unions of holed discs -/

/-- **A finite union of holed discs**: a subset of the closed unit disc of the form
`⋃_{(a, c, H) ∈ P} D(a, |c|) ∖ ⋃_{(b, d) ∈ H} D⁻(b, |d|)` for a finite set `P` of triples. -/
def IsHoledDiscUnion (S : Set (closedPolydisc 1 K)) : Prop :=
  ∃ P : Finset (K × K × Finset (K × K)),
    S = ⋃ p ∈ P, holedDisc p.1 p.2.1 (fun q : p.2.2 ↦ q.1.1) (fun q ↦ q.1.2)

/-- Unfolding `IsHoledDiscUnion`: `S` is a finite union of holed discs exactly when it is
`⋃_{(a, c, H) ∈ P} D(a, |c|) ∖ ⋃_{(b, d) ∈ H} D⁻(b, |d|)` for some finite set `P` of triples. -/
theorem isHoledDiscUnion_iff {S : Set (closedPolydisc 1 K)} :
    IsHoledDiscUnion S ↔ ∃ P : Finset (K × K × Finset (K × K)),
      S = ⋃ p ∈ P, holedDisc p.1 p.2.1 (fun q : p.2.2 ↦ q.1.1) (fun q ↦ q.1.2) :=
  Iff.rfl

/-- The empty set is a finite union of holed discs. -/
@[simp] theorem isHoledDiscUnion_empty : IsHoledDiscUnion (∅ : Set (closedPolydisc 1 K)) :=
  ⟨∅, by simp⟩

/-- The whole closed unit disc is a finite union of holed discs, namely the disc `D(0, |1|)`. -/
@[simp] theorem isHoledDiscUnion_univ : IsHoledDiscUnion (Set.univ : Set (closedPolydisc 1 K)) :=
  ⟨{(0, 1, ∅)}, by simp⟩

/-- A finite union of finite unions of holed discs is a finite union of holed discs. -/
theorem isHoledDiscUnion_biUnion {ι : Type*} (s : Finset ι)
    {S : ι → Set (closedPolydisc 1 K)} (hS : ∀ i ∈ s, IsHoledDiscUnion (S i)) :
    IsHoledDiscUnion (⋃ i ∈ s, S i) := by
  classical
  choose! P hP using hS
  exact ⟨s.biUnion P, by rw [Finset.set_biUnion_biUnion]; exact Set.iUnion₂_congr hP⟩

/-- The union of two finite unions of holed discs is a finite union of holed discs. -/
theorem IsHoledDiscUnion.union {S S' : Set (closedPolydisc 1 K)} (hS : IsHoledDiscUnion S)
    (hS' : IsHoledDiscUnion S') : IsHoledDiscUnion (S ∪ S') := by
  classical
  obtain ⟨P, rfl⟩ := hS
  obtain ⟨P', rfl⟩ := hS'
  exact ⟨P ∪ P', by rw [Finset.set_biUnion_union]⟩

/-- **Cutting out a hole** from a finite union of holed discs gives a finite union of holed discs:
add the hole to each of them. -/
theorem IsHoledDiscUnion.inter_setOf_vle {S : Set (closedPolydisc 1 K)}
    (hS : IsHoledDiscUnion S) (b d : K) :
    IsHoledDiscUnion (S ∩ {v | v.1.toValuativeRel.vle (C d) (T - C b)}) := by
  classical
  obtain ⟨P, rfl⟩ := hS
  refine ⟨P.image fun p ↦ (p.1, p.2.1, insert (b, d) p.2.2), ?_⟩
  rw [Finset.set_biUnion_finset_image, Set.iUnion₂_inter]
  exact Set.iUnion₂_congr fun p _ ↦ (holedDisc_insert p.1 p.2.1 Prod.fst Prod.snd (b, d) p.2.2).symm

/-- Cutting out finitely many holes from a finite union of holed discs gives a finite union of
holed discs. -/
theorem IsHoledDiscUnion.inter_biInter_setOf_vle {ι : Type*} {S : Set (closedPolydisc 1 K)}
    (hS : IsHoledDiscUnion S) (s : Finset ι) (b d : ι → K) :
    IsHoledDiscUnion (S ∩ ⋂ i ∈ s, {v | v.1.toValuativeRel.vle (C (d i)) (T - C (b i))}) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hS
  | insert i s _ ih =>
    rw [Finset.set_biInter_insert, ← Set.inter_assoc, Set.inter_right_comm]
    exact ih.inter_setOf_vle (b i) (d i)

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

/-- **A holed disc cut by a disc is a holed disc with the same holes**: the intersection of the
outer disc `D(a, |c|)` with `D(a', |c'|)` is a disc, possibly the empty disc. -/
theorem exists_holedDisc_inter_closedSubdisc_eq (a c a' c' : K) (b d : ι → K) :
    ∃ e r : K, holedDisc a c b d ∩ closedSubdisc a' c' = holedDisc e r b d := by
  obtain ⟨e, r, h⟩ := exists_closedSubdisc_inter_closedSubdisc_eq a a' c c'
  exact ⟨e, r, by rw [holedDisc, holedDisc, ← h, Set.inter_right_comm]⟩

/-- **Cutting by a disc** a finite union of holed discs gives a finite union of holed discs. -/
theorem IsHoledDiscUnion.inter_closedSubdisc {S : Set (closedPolydisc 1 K)}
    (hS : IsHoledDiscUnion S) (a c : K) : IsHoledDiscUnion (S ∩ closedSubdisc a c) := by
  classical
  obtain ⟨P, rfl⟩ := hS
  choose e r h using fun p : K × K × Finset (K × K) ↦
    exists_holedDisc_inter_closedSubdisc_eq p.1 p.2.1 a c (fun q : p.2.2 ↦ q.1.1) (fun q ↦ q.1.2)
  refine ⟨P.image fun p ↦ (e p, r p, p.2.2), ?_⟩
  rw [Finset.set_biUnion_finset_image, Set.iUnion₂_inter]
  exact Set.iUnion₂_congr fun p _ ↦ h p

/-- Cutting by finitely many discs a finite union of holed discs gives a finite union of holed
discs. -/
theorem IsHoledDiscUnion.inter_biInter_closedSubdisc {ι : Type*}
    {S : Set (closedPolydisc 1 K)} (hS : IsHoledDiscUnion S) (s : Finset ι) (a c : ι → K) :
    IsHoledDiscUnion (S ∩ ⋂ i ∈ s, closedSubdisc (a i) (c i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hS
  | insert i s _ ih =>
    rw [Finset.set_biInter_insert, ← Set.inter_assoc, Set.inter_right_comm]
    exact ih.inter_closedSubdisc (a i) (c i)

/-- **The intersection of two finite unions of holed discs is a finite union of holed discs**:
cut the first by the outer disc and the holes of each holed disc of the second. -/
theorem IsHoledDiscUnion.inter {S S' : Set (closedPolydisc 1 K)} (hS : IsHoledDiscUnion S)
    (hS' : IsHoledDiscUnion S') : IsHoledDiscUnion (S ∩ S') := by
  obtain ⟨P, rfl⟩ := hS'
  rw [Set.inter_iUnion₂]
  refine isHoledDiscUnion_biUnion P fun p _ ↦ ?_
  have h : S ∩ holedDisc p.1 p.2.1 (fun q : p.2.2 ↦ q.1.1) (fun q ↦ q.1.2) =
      S ∩ closedSubdisc p.1 p.2.1 ∩
        ⋂ q ∈ p.2.2, {v | v.1.toValuativeRel.vle (C q.2) (T - C q.1)} := by
    ext v
    simp [and_assoc]
  rw [h]
  exact (hS.inter_closedSubdisc p.1 p.2.1).inter_biInter_setOf_vle p.2.2 Prod.fst Prod.snd

/-- A finite intersection of finite unions of holed discs is a finite union of holed discs. -/
theorem isHoledDiscUnion_biInter {ι : Type*} (s : Finset ι)
    {S : ι → Set (closedPolydisc 1 K)} (hS : ∀ i ∈ s, IsHoledDiscUnion (S i)) :
    IsHoledDiscUnion (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ ih =>
    rw [Finset.set_biInter_insert]
    exact (hS i (Finset.mem_insert_self i s)).inter
      (ih fun j hj ↦ hS j (Finset.mem_insert_of_mem hj))

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

/-! ### Finite unions of holed discs are rational -/

section Rational

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]

/-- The subsets of the closed unit disc whose transport to `Spa (K⟨T⟩, K⟨T⟩°)` is rational. -/
private def IsRat (S : Set (closedPolydisc 1 K)) : Prop :=
  (Homeomorph.setCongr (closedPolydisc_def 1 K)).symm ⁻¹' S ∈
    spaRationalFamily (powerBoundedSubring (𝒯 K))

omit [IsUltrametricDist K] in
private theorem isRat_univ : IsRat (Set.univ : Set (closedPolydisc 1 K)) :=
  univ_mem_spaRationalFamily _

private theorem IsRat.inter {S S' : Set (closedPolydisc 1 K)} (hS : IsRat S) (hS' : IsRat S') :
    IsRat (S ∩ S') :=
  inter_mem_spaRationalFamily hS hS'

private theorem isRat_biInter {ι : Type*} (s : Finset ι) {S : ι → Set (closedPolydisc 1 K)}
    (hS : ∀ i ∈ s, IsRat (S i)) : IsRat (⋂ i ∈ s, S i) := by
  rw [IsRat, Set.preimage_iInter₂]
  exact biInter_mem_spaRationalFamily s hS

private theorem isRat_iInter {ι : Type*} [Finite ι] {S : ι → Set (closedPolydisc 1 K)}
    (hS : ∀ i, IsRat (S i)) : IsRat (⋂ i, S i) := by
  rw [IsRat, Set.preimage_iInter]
  exact iInter_mem_spaRationalFamily hS

omit [IsUltrametricDist K] in
/-- The complement `{v : v(d) ≤ v(T - b)}` of the open disc `D⁻(b, |d|)` is rational. -/
private theorem isRat_setOf_vle (b d : K) :
    IsRat {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C d) (T - C b)} := by
  classical
  rcases eq_or_ne d 0 with rfl | hd
  · simpa only [map_zero, ValuativeRel.zero_vle, Set.ofPred_true] using isRat_univ
  have hspan : Ideal.span (({C d} : Finset (𝒯 K)) : Set (𝒯 K)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) ((isUnit_iff_ne_zero.mpr hd).map C)
  rw [IsRat, setOf_vle_eq_rationalSubset _ (isUnit_iff_ne_zero.mpr hd)]
  exact mem_spaRationalFamily_iff.mpr ⟨_, _, by rw [hspan]; simp, rfl⟩

/-- The complement `{v : v(f) ≤ v(r) or v(σ) ≤ v(f)}` of an open annulus is rational. -/
private theorem isRat_setOf_vle_or_vle (f : 𝒯 K) {r σ : K} (hr : r ≠ 0) (hrσ : ‖r‖ < ‖σ‖) :
    IsRat {v : closedPolydisc 1 K |
      v.1.toValuativeRel.vle f (C r) ∨ v.1.toValuativeRel.vle (C σ) f} := by
  have hσ : σ ≠ 0 := norm_pos_iff.mp ((norm_nonneg r).trans_lt hrσ)
  refine setOf_vle_or_vle_mem_spaRationalFamily _ f ((isUnit_iff_ne_zero.mpr hr).map C)
    ((isUnit_iff_ne_zero.mpr hσ).map C) fun v hv ↦ ?_
  rw [← valuation_lt_iff]
  exact (closedPolydisc_valuation_weightedC_lt_iff ⟨v, closedPolydisc_def 1 K ▸ hv⟩ r σ).mpr hrσ

omit [NonarchimedeanRing K] in
/-- The ultrametric triangle inequality, measured from a common point `y`. -/
private theorem norm_sub_le_max_norm_sub (x y z : K) : ‖x - z‖ ≤ max ‖x - y‖ ‖z - y‖ := by
  rw [norm_sub_rev z y, ← sub_add_sub_cancel x y z]
  exact IsUltrametricDist.norm_add_le_max _ _

omit [IsUltrametricDist K] in
/-- `T - a = (T - b) + (b - a)`. -/
private theorem weightedX_sub_weightedC_eq_add (a b : K) :
    (T - C a : 𝒯 K) = (T - C b) + C (b - a) := by
  rw [map_sub]
  ring

/-- If `v(s) ≤ v(T - b)` and `‖a - b‖ < ‖s‖`, then `v(T - a) = v(T - b)`. -/
private theorem valuation_weightedX_sub_weightedC_eq_of_le {x : closedPolydisc 1 K} {a b s : K}
    (hab : ‖a - b‖ < ‖s‖) (hx : x.1.valuation (C s) ≤ x.1.valuation (T - C b)) :
    x.1.valuation (T - C a) = x.1.valuation (T - C b) := by
  rw [weightedX_sub_weightedC_eq_add a b, Valuation.map_add_eq_of_lt_left]
  refine lt_of_lt_of_le ?_ hx
  rw [closedPolydisc_valuation_weightedC_lt_iff, norm_sub_rev]
  exact hab

/-- If `v(T - b) < v(s)` and `‖a - b‖ < ‖s‖`, then `v(T - a) < v(s)`. -/
private theorem valuation_weightedX_sub_weightedC_lt_of_lt {x : closedPolydisc 1 K} {a b s : K}
    (hab : ‖a - b‖ < ‖s‖) (hx : x.1.valuation (T - C b) < x.1.valuation (C s)) :
    x.1.valuation (T - C a) < x.1.valuation (C s) := by
  rw [weightedX_sub_weightedC_eq_add a b]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt hx ?_)
  rw [closedPolydisc_valuation_weightedC_lt_iff, norm_sub_rev]
  exact hab

/-- Recentring the complement of an open disc inside it: if `‖a - b‖ < ‖s‖`, then
`{v(s) ≤ v(T - b)} = {v(s) ≤ v(T - a)}`. -/
private theorem setOf_vle_eq_of_norm_sub_lt {a b s : K} (hab : ‖a - b‖ < ‖s‖) :
    {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C s) (T - C b)} =
      {v | v.1.toValuativeRel.vle (C s) (T - C a)} := by
  ext v
  simp only [Set.mem_ofPred_eq, ← valuation_le_iff]
  constructor
  · intro h
    rwa [valuation_weightedX_sub_weightedC_eq_of_le hab h]
  · intro h
    rwa [valuation_weightedX_sub_weightedC_eq_of_le (by rwa [norm_sub_rev]) h]

/-- A disc of nonzero radius is cut out by its defining inequality alone. -/
private theorem closedSubdisc_eq_setOf_vle (a : K) {c : K} (hc : c ≠ 0) :
    closedSubdisc a c = {v | v.1.toValuativeRel.vle (T - C a) (C c)} := by
  ext v
  rw [mem_closedSubdisc, Set.mem_ofPred_eq, and_iff_left_iff_imp, ← map_zero C,
    closedPolydisc_vle_weightedC_iff, norm_zero, norm_le_zero_iff]
  exact fun _ ↦ hc

/-- The complement of an open disc of radius more than one is empty. -/
private theorem setOf_vle_eq_empty {σ : K} (hσ : 1 < ‖σ‖) :
    {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C σ) (T - C 0)} = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun v hv ↦ ?_
  have h₁ := ((mem_closedSubdisc _ _ _).mp (closedSubdisc_zero_one (K := K) ▸ Set.mem_univ v)).1
  have h₂ := (closedPolydisc_vle_weightedC_iff v σ 1).mp (v.1.toValuativeRel.vle_trans hv h₁)
  rw [norm_one] at h₂
  exact h₂.not_gt hσ

omit [IsUltrametricDist K] in
/-- The value at a point of the product of the linear factors `T - a` over a finite family. -/
private theorem valuation_prod_le_of_forall_le (x : closedPolydisc 1 K) {F : Finset (K × K)}
    {q₀ : K × K} (hq₀ : q₀ ∈ F) {ρ τ : K}
    (h₀ : x.1.valuation (T - C q₀.1) ≤ x.1.valuation (C ρ))
    (h : ∀ q ∈ F, x.1.valuation (T - C q.1) ≤ x.1.valuation (C τ)) :
    x.1.valuation (∏ q ∈ F, (T - C q.1)) ≤ x.1.valuation (C (ρ * τ ^ (F.card - 1))) := by
  classical
  rw [map_prod, ← Finset.mul_prod_erase F _ hq₀, map_mul, map_pow, map_mul, map_pow,
    ← Finset.card_erase_of_mem hq₀]
  exact mul_le_mul' h₀ (Finset.prod_le_pow_card _ _ _ fun q hq ↦ h q (Finset.mem_of_mem_erase hq))

/-- **The complement of an open disc as a domain of a product of linear factors.** If every
centre `a` of a nonempty finite family lies in `D⁻(b, |s|)`, then
`v(s)ⁿ ≤ v(∏ (T - a))` exactly when `v(s) ≤ v(T - b)`, where `n` is the size of the family. -/
private theorem vle_prod_iff (x : closedPolydisc 1 K) {F : Finset (K × K)} (hF : F.Nonempty)
    {b s : K} (h : ∀ q ∈ F, ‖q.1 - b‖ < ‖s‖) :
    x.1.toValuativeRel.vle (C (s ^ F.card)) (∏ q ∈ F, (T - C q.1)) ↔
      x.1.toValuativeRel.vle (C s) (T - C b) := by
  classical
  rw [← valuation_le_iff, ← valuation_le_iff, map_pow, map_pow, map_prod]
  constructor
  · -- if `v(T - b) < v(s)`, every factor is below `v(s)`, hence so is the product
    intro hle
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨q₀, hq₀⟩ := hF
    have hs : x.1.valuation (C s) ≠ 0 := by
      rw [Ne, closedPolydisc_valuation_weightedC_eq_zero_iff]
      exact norm_pos_iff.mp ((norm_nonneg _).trans_lt (h q₀ hq₀))
    refine hle.not_gt ?_
    rw [← Finset.mul_prod_erase F _ hq₀, ← Finset.card_erase_add_one hq₀, pow_succ']
    exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
      (valuation_weightedX_sub_weightedC_lt_of_lt (h q₀ hq₀) hlt)
      (Finset.prod_le_pow_card _ _ _ fun q hq ↦
        (valuation_weightedX_sub_weightedC_lt_of_lt (h q (Finset.mem_of_mem_erase hq)) hlt).le)
      zero_le (zero_lt_iff.mpr (pow_ne_zero _ hs))
  · -- if `v(s) ≤ v(T - b)`, every factor is `v(T - b)`
    intro hle
    exact Finset.pow_card_le_prod _ _ _ fun q hq ↦
      (valuation_weightedX_sub_weightedC_eq_of_le (h q hq) hle).ge.trans' hle

/-- A point of the disc `D(a₀, |c₀|)` of a finite family satisfies `v(∏ (T - a)) ≤ v(ρ τⁿ⁻¹)`,
where `n` is the size of the family, provided `|c₀| ≤ |ρ|`, `|c₀| ≤ |τ|` and every centre `a` is
within `|τ|` of `a₀`. -/
private theorem valuation_prod_le_of_mem_closedSubdisc {x : closedPolydisc 1 K}
    {F : Finset (K × K)} {q₀ : K × K} (hq₀ : q₀ ∈ F) {ρ τ : K} (hρ : ‖q₀.2‖ ≤ ‖ρ‖)
    (hτ : ‖q₀.2‖ ≤ ‖τ‖) (hF : ∀ q ∈ F, ‖q.1 - q₀.1‖ ≤ ‖τ‖)
    (hx : x ∈ closedSubdisc q₀.1 q₀.2) :
    x.1.valuation (∏ q ∈ F, (T - C q.1)) ≤ x.1.valuation (C (ρ * τ ^ (F.card - 1))) := by
  have hx₀ := (valuation_le_iff _ _ _).mpr ((mem_closedSubdisc _ _ _).mp hx).1
  refine valuation_prod_le_of_forall_le x hq₀
    (hx₀.trans ((closedPolydisc_valuation_weightedC_le_iff x _ _).mpr hρ)) fun q hq ↦ ?_
  rw [weightedX_sub_weightedC_eq_add q.1 q₀.1]
  refine (Valuation.map_add _ _ _).trans (max_le (hx₀.trans ?_) ?_) <;>
    rw [closedPolydisc_valuation_weightedC_le_iff]
  · exact hτ
  · rw [norm_sub_rev]
    exact hF q hq

/-- If `v(∏ (T - a)) ≤ v(ρ τⁿ⁻¹)` over a nonempty finite family of size `n`, with `|ρ| < |τ|`,
then the point is within `|τ|` of some centre: `v(T - a) < v(τ)` for some `a`. -/
private theorem exists_valuation_weightedX_sub_weightedC_lt (x : closedPolydisc 1 K)
    {F : Finset (K × K)} (hF : F.Nonempty) {ρ τ : K} (hρτ : ‖ρ‖ < ‖τ‖)
    (hx : x.1.valuation (∏ q ∈ F, (T - C q.1)) ≤ x.1.valuation (C (ρ * τ ^ (F.card - 1)))) :
    ∃ q ∈ F, x.1.valuation (T - C q.1) < x.1.valuation (C τ) := by
  by_contra! h
  have hτ₀ : x.1.valuation (C τ) ≠ 0 := by
    rw [Ne, closedPolydisc_valuation_weightedC_eq_zero_iff]
    exact norm_pos_iff.mp ((norm_nonneg _).trans_lt hρτ)
  refine ((Finset.pow_card_le_prod F _ _ h).trans
    ((map_prod x.1.valuation _ F).symm.le.trans hx)).not_gt ?_
  -- split off one factor `v(τ)` to compare with `v(ρ τⁿ⁻¹) = v(ρ) v(τ)ⁿ⁻¹`
  have hτpow : x.1.valuation (C τ) ^ F.card =
      x.1.valuation (C τ) * x.1.valuation (C τ) ^ (F.card - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Finset.card_pos.mpr hF)]
  rw [map_mul, map_mul, map_pow, map_pow, hτpow]
  exact mul_lt_mul_of_pos_right
    ((closedPolydisc_valuation_weightedC_lt_iff x _ _).mpr hρτ)
    (zero_lt_iff.mpr (pow_ne_zero _ hτ₀))

/-- **Separating the discs of a finite family by a product of linear factors.** Let the discs
`D(a, |c|)` of a nonempty finite family have radii at most `|ρ|` and centres pairwise within `|τ|`
inside `D⁻(b, |s|)`, where `|ρ| < |τ| < |s|`. Then `{v(s) ≤ v(T - b)} ∪ ⋃ D(a, |c|)` is the
intersection of `{v(∏ (T - a)) ≤ v(ρ τⁿ⁻¹)} ∪ {v(sⁿ) ≤ v(∏ (T - a))}` with the sets
`{v(τ) ≤ v(T - a)} ∪ ⋃ D(a', |c'|)`, the union over the centres `a'` within `|τ|` of `a`. -/
private theorem setOf_vle_union_biUnion_closedSubdisc_eq {F : Finset (K × K)} (hF : F.Nonempty)
    {b s ρ τ : K} (hb : ∀ q ∈ F, ‖q.1 - b‖ < ‖s‖) (hτs : ‖τ‖ < ‖s‖)
    (hρ : ∀ q ∈ F, ‖q.2‖ ≤ ‖ρ‖) (hρτ : ‖ρ‖ < ‖τ‖)
    (hdist : ∀ q ∈ F, ∀ q' ∈ F, ‖q.1 - q'.1‖ ≤ ‖τ‖) :
    {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C s) (T - C b)} ∪
        ⋃ q ∈ F, closedSubdisc q.1 q.2 =
      {v : closedPolydisc 1 K |
          v.1.toValuativeRel.vle (∏ q ∈ F, (T - C q.1)) (C (ρ * τ ^ (F.card - 1))) ∨
          v.1.toValuativeRel.vle (C (s ^ F.card)) (∏ q ∈ F, (T - C q.1))} ∩
        ⋂ q ∈ F, ({v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C τ) (T - C q.1)} ∪
          ⋃ q'' ∈ F.filter (fun q'' ↦ ‖q''.1 - q.1‖ < ‖τ‖), closedSubdisc q''.1 q''.2) := by
  classical
  ext x
  have hprod := vle_prod_iff x hF hb
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter₂,
    Set.mem_iUnion₂, exists_prop]
  constructor
  · rintro (hx | ⟨q₀, hq₀, hx⟩)
    · -- outside `D⁻(b, |s|)`, hence outside every `D⁻(a, |τ|)`
      refine ⟨Or.inr (hprod.mpr hx), fun q hq ↦ Or.inl ?_⟩
      have hx' : x ∈ {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C s) (T - C q.1)} := by
        rw [← setOf_vle_eq_of_norm_sub_lt (hb q hq)]
        exact hx
      exact x.1.toValuativeRel.vle_trans
        ((closedPolydisc_vle_weightedC_iff x _ _).mpr hτs.le) hx'
    · have hq₀τ : ‖q₀.2‖ < ‖τ‖ := (hρ q₀ hq₀).trans_lt hρτ
      refine ⟨Or.inl ((valuation_le_iff _ _ _).mp (valuation_prod_le_of_mem_closedSubdisc hq₀
        (hρ q₀ hq₀) hq₀τ.le (fun q hq ↦ hdist q hq q₀ hq₀) hx)), fun q hq ↦ ?_⟩
      by_cases hq₀q : ‖q₀.1 - q.1‖ < ‖τ‖
      · exact Or.inr ⟨q₀, Finset.mem_filter.mpr ⟨hq₀, hq₀q⟩, hx⟩
      · -- a disc of another class lies at distance at least `τ` from `q.1`
        refine Or.inl ((valuation_le_iff _ _ _).mp ?_)
        rw [valuation_weightedX_sub_weightedC_of_mem_closedSubdisc hx
            (by rw [norm_sub_rev]; exact hq₀τ.trans_le (not_lt.mp hq₀q)),
          closedPolydisc_valuation_weightedC_le_iff]
        exact not_lt.mp hq₀q
  · rintro ⟨hx | hx, hxq⟩
    · obtain ⟨q, hq, hlt⟩ :=
        exists_valuation_weightedX_sub_weightedC_lt x hF hρτ ((valuation_le_iff _ _ _).mpr hx)
      rcases hxq q hq with hle | ⟨q'', hq'', hx''⟩
      · exact absurd ((valuation_le_iff _ _ _).mpr hle) (not_le.mpr hlt)
      · exact Or.inr ⟨q'', (Finset.mem_filter.mp hq'').1, hx''⟩
    · exact Or.inl (hprod.mp hx)

/-- **The complement of an open disc together with finitely many discs inside it is rational.**
Let `s ≠ 0` and let `D(a, |c|)`, for `(a, c)` in a finite family `F`, be discs of nonzero radius
inside the open disc `D⁻(b, |s|)`. Then `{v(s) ≤ v(T - b)} ∪ ⋃ D(a, |c|)` is rational. -/
private theorem isRat_setOf_vle_union_biUnion_closedSubdisc (F : Finset (K × K)) :
    ∀ b s : K, s ≠ 0 → (∀ q ∈ F, q.2 ≠ 0 ∧ ‖q.1 - b‖ < ‖s‖ ∧ ‖q.2‖ < ‖s‖) →
      IsRat ({v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C s) (T - C b)} ∪
        ⋃ q ∈ F, closedSubdisc q.1 q.2) := by
  -- Induction on `F`. Let `τ` be the largest of the radii `|c|` and of the distances `|a - a₁|`
  -- to a fixed centre `a₁`. If some radius is `|τ|`, that disc contains all the others and the
  -- set is the complement of the open annulus `{|c| < |T - a| < |s|}`. Otherwise all radii are
  -- smaller than `|τ|`, and the centres fall into at least two classes for `|a - a'| < |τ|`.
  -- The union is then the intersection of `{|∏ (T - a)| ≤ |ρ τⁿ⁻¹|} ∪ {|sⁿ| ≤ |∏ (T - a)|}`,
  -- for `|ρ|` the largest radius, with the sets `{|τ| ≤ |T - a|} ∪ ⋃ D(a', |c'|)` over the class
  -- of each `a`, which are rational by induction. The first set contains the discs and excludes
  -- every point with `|τ| ≤ |T - a|` for all centres.
  classical
  induction F using Finset.strongInduction with
  | H F ih =>
  intro b s hs hF
  rcases F.eq_empty_or_nonempty with rfl | ⟨q₁, hq₁⟩
  · simpa using isRat_setOf_vle b s
  -- `τ`: the largest of the radii and of the distances to the centre `q₁.1`
  obtain ⟨τ, hτC, hτ⟩ := (F.image Prod.snd ∪ F.image fun q ↦ q.1 - q₁.1).exists_max_image
    (‖·‖) ⟨q₁.2, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq₁)⟩
  have hτc {q : K × K} (hq : q ∈ F) : ‖q.2‖ ≤ ‖τ‖ :=
    hτ _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq))
  have hτa {q : K × K} (hq : q ∈ F) : ‖q.1 - q₁.1‖ ≤ ‖τ‖ :=
    hτ _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun q ↦ q.1 - q₁.1) hq))
  have hdist {q q' : K × K} (hq : q ∈ F) (hq' : q' ∈ F) : ‖q.1 - q'.1‖ ≤ ‖τ‖ :=
    (norm_sub_le_max_norm_sub q.1 q₁.1 q'.1).trans (max_le (hτa hq) (hτa hq'))
  by_cases hA : ∃ q₀ ∈ F, ‖τ‖ ≤ ‖q₀.2‖
  · -- one of the discs contains all the others
    obtain ⟨q₀, hq₀, hτq₀⟩ := hA
    have hU : ⋃ q ∈ F, closedSubdisc q.1 q.2 = closedSubdisc q₀.1 q₀.2 :=
      subset_antisymm (Set.iUnion₂_subset fun q hq ↦ closedSubdisc_subset_closedSubdisc
          ((hdist hq hq₀).trans hτq₀) ((hτc hq).trans hτq₀))
        (Set.subset_biUnion_of_mem (u := fun q : K × K ↦ closedSubdisc q.1 q.2) hq₀)
    obtain ⟨hc₀, hb₀, hs₀⟩ := hF q₀ hq₀
    rw [hU, closedSubdisc_eq_setOf_vle _ hc₀, setOf_vle_eq_of_norm_sub_lt hb₀, Set.union_comm]
    exact isRat_setOf_vle_or_vle _ hc₀ hs₀
  push Not at hA
  -- otherwise `τ` is the distance `q'.1 - q₁.1` between two centres
  obtain ⟨q', hq', hτq'⟩ : ∃ q' ∈ F, q'.1 - q₁.1 = τ := by
    rcases Finset.mem_union.mp hτC with h | h
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
      exact absurd (hA q hq) (lt_irrefl _)
    · exact Finset.mem_image.mp h
  have hτ₀ : τ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt (hA q₁ hq₁))
  have hτs : ‖τ‖ < ‖s‖ := by
    rw [← hτq']
    exact (norm_sub_le_max_norm_sub q'.1 b q₁.1).trans_lt
      (max_lt (hF q' hq').2.1 (hF q₁ hq₁).2.1)
  -- `ρ`: the largest radius, smaller than `τ`
  obtain ⟨ρ, hρF, hρ⟩ := (F.image Prod.snd).exists_max_image (‖·‖)
    ⟨q₁.2, Finset.mem_image_of_mem _ hq₁⟩
  have hρτ : ‖ρ‖ < ‖τ‖ := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hρF
    exact hA q hq
  have hρ₀ : ρ ≠ 0 := norm_pos_iff.mp ((norm_pos_iff.mpr (hF q₁ hq₁).1).trans_le
    (hρ _ (Finset.mem_image_of_mem _ hq₁)))
  -- the class of each centre is a proper subfamily
  set G : K × K → Finset (K × K) := fun q ↦ F.filter fun q'' ↦ ‖q''.1 - q.1‖ < ‖τ‖
  have hGF {q : K × K} (hq : q ∈ F) : G q ⊂ F := by
    refine Finset.filter_ssubset.mpr ?_
    by_contra! h
    have h' := norm_sub_le_max_norm_sub q'.1 q.1 q₁.1
    rw [hτq'] at h'
    exact (h'.trans_lt (max_lt (h q' hq') (h q₁ hq₁))).false
  have hGrat {q : K × K} (hq : q ∈ F) :
      IsRat ({v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C τ) (T - C q.1)} ∪
        ⋃ q'' ∈ G q, closedSubdisc q''.1 q''.2) :=
    ih (G q) (hGF hq) q.1 τ hτ₀ fun q'' hq'' ↦ by
      obtain ⟨hq''F, hq''τ⟩ := Finset.mem_filter.mp hq''
      exact ⟨(hF q'' hq''F).1, hq''τ, hA q'' hq''F⟩
  -- the radius `ε = ρ τⁿ⁻¹` of the product of the linear factors
  have hn : F.card - 1 + 1 = F.card := Nat.sub_add_cancel (Finset.card_pos.mpr ⟨q₁, hq₁⟩)
  have hεs : ‖ρ * τ ^ (F.card - 1)‖ < ‖s ^ F.card‖ := by
    rw [norm_mul, norm_pow, norm_pow, ← hn, pow_succ']
    calc ‖ρ‖ * ‖τ‖ ^ (F.card - 1) ≤ ‖ρ‖ * ‖s‖ ^ (F.card - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hτs.le _) (norm_nonneg _)
      _ < ‖s‖ * ‖s‖ ^ (F.card - 1) :=
          mul_lt_mul_of_pos_right (hρτ.trans hτs) (pow_pos (norm_pos_iff.mpr hs) _)
  rw [setOf_vle_union_biUnion_closedSubdisc_eq ⟨q₁, hq₁⟩ (fun q hq ↦ (hF q hq).2.1) hτs
    (fun q hq ↦ hρ _ (Finset.mem_image_of_mem _ hq)) hρτ fun q hq q' hq' ↦ hdist hq hq']
  exact (isRat_setOf_vle_or_vle _ (mul_ne_zero hρ₀ (pow_ne_zero _ hτ₀)) hεs).inter
    (isRat_biInter F fun q hq ↦ hGrat hq)

/-- Two complements of open discs cover the disc when the smaller open disc `D⁻(b₀, |d₀|)` lies
outside the larger one `D⁻(b, |d|)`. -/
private theorem setOf_vle_union_setOf_vle_eq_univ {b b₀ d d₀ : K} (hd : ‖d₀‖ ≤ ‖d‖)
    (hb : ‖d‖ ≤ ‖b - b₀‖) :
    {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C d) (T - C b)} ∪
      {v | v.1.toValuativeRel.vle (C d₀) (T - C b₀)} = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  simp only [Set.mem_union, Set.mem_ofPred_eq, ← valuation_le_iff]
  refine or_iff_not_imp_right.mpr fun h ↦ ?_
  rw [not_le] at h
  rw [weightedX_sub_weightedC_eq_add b b₀, Valuation.map_add_eq_of_lt_right, norm_sub_rev] at *
  · rw [closedPolydisc_valuation_weightedC_le_iff]
    exact hb
  · refine h.trans_le ?_
    rw [closedPolydisc_valuation_weightedC_le_iff, norm_sub_rev]
    exact hd.trans hb

/-- The complement of a larger open disc `D⁻(b, |d|)` containing the smaller one `D⁻(b₀, |d₀|)`
lies in the complement of the smaller one. -/
private theorem setOf_vle_subset_setOf_vle {b b₀ d d₀ : K} (hd : ‖d₀‖ ≤ ‖d‖)
    (hb : ‖b - b₀‖ < ‖d‖) :
    {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C d) (T - C b)} ⊆
      {v | v.1.toValuativeRel.vle (C d₀) (T - C b₀)} := by
  intro x hx
  rw [setOf_vle_eq_of_norm_sub_lt (a := b₀) (by rwa [norm_sub_rev])] at hx
  exact x.1.toValuativeRel.vle_trans ((closedPolydisc_vle_weightedC_iff x _ _).mpr hd) hx

/-- A disc `D(a, |c|)` containing the open disc `D⁻(b₀, |d₀|)` covers the disc together with the
complement of `D⁻(b₀, |d₀|)`. -/
private theorem closedSubdisc_union_setOf_vle_eq_univ {a c b₀ d₀ : K} (hc : c ≠ 0)
    (hd : ‖d₀‖ ≤ ‖c‖) (ha : ‖a - b₀‖ ≤ ‖c‖) :
    closedSubdisc a c ∪ {v | v.1.toValuativeRel.vle (C d₀) (T - C b₀)} = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  rw [closedSubdisc_eq_setOf_vle a hc]
  simp only [Set.mem_union, Set.mem_ofPred_eq, ← valuation_le_iff]
  refine or_iff_not_imp_right.mpr fun h ↦ ?_
  rw [not_le] at h
  rw [weightedX_sub_weightedC_eq_add a b₀]
  refine (Valuation.map_add _ _ _).trans (max_le (h.le.trans ?_) ?_) <;>
    rw [closedPolydisc_valuation_weightedC_le_iff]
  · exact hd
  · rwa [norm_sub_rev]

/-- A disc `D(a, |c|)` outside the open disc `D⁻(b₀, |d₀|)` lies in its complement. -/
private theorem closedSubdisc_subset_setOf_vle {a c b₀ d₀ : K} (hc : ‖c‖ < ‖a - b₀‖)
    (hd : ‖d₀‖ ≤ ‖a - b₀‖) :
    closedSubdisc a c ⊆ {v | v.1.toValuativeRel.vle (C d₀) (T - C b₀)} := by
  intro x hx
  rw [Set.mem_ofPred_eq, ← valuation_le_iff, valuation_weightedX_sub_weightedC_of_mem_closedSubdisc
    hx (by rwa [norm_sub_rev]), closedPolydisc_valuation_weightedC_le_iff]
  exact hd

/-- A disc `D(a, |c|)` that neither lies inside the open disc `D⁻(b₀, |d₀|)` nor is at least as
large as it and meets it lies in its complement. -/
private theorem closedSubdisc_subset_setOf_vle_of_not_lt {a c b₀ d₀ : K}
    (hcov : ‖d₀‖ ≤ ‖c‖ → ‖c‖ < ‖a - b₀‖) (hin : ‖a - b₀‖ < ‖d₀‖ → ‖d₀‖ ≤ ‖c‖) :
    closedSubdisc a c ⊆ {v | v.1.toValuativeRel.vle (C d₀) (T - C b₀)} := by
  by_cases h : ‖a - b₀‖ < ‖d₀‖
  · have h' := hin h
    exact absurd (hcov h') (not_lt.mpr (h.le.trans h'))
  rw [not_lt] at h
  exact closedSubdisc_subset_setOf_vle
    ((lt_or_ge ‖c‖ ‖d₀‖).elim (fun h' ↦ h'.trans_le h) hcov) h

/-- **A finite union of discs and of complements of open discs is rational.** -/
private theorem isRat_biUnion_closedSubdisc_union_biUnion_setOf_vle (𝒟 ℰ : Finset (K × K)) :
    IsRat ((⋃ q ∈ 𝒟, closedSubdisc q.1 q.2) ∪
      ⋃ e ∈ ℰ, {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C e.2) (T - C e.1)}) := by
  -- Adding the empty complement of a disc of radius more than one, there is at least one
  -- complement. Let `D⁻(b₀, |d₀|)` be a smallest removed open disc. Any other removed open disc
  -- either contains it, and its complement is absorbed, or lies outside it, and the two
  -- complements cover the disc. Each disc either covers the disc together with the complement of
  -- `D⁻(b₀, |d₀|)`, or lies in that complement, or lies inside `D⁻(b₀, |d₀|)`. What remains is
  -- `isRat_setOf_vle_union_biUnion_closedSubdisc`.
  classical
  set U := (⋃ q ∈ 𝒟, closedSubdisc q.1 q.2) ∪
    ⋃ e ∈ ℰ, {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C e.2) (T - C e.1)} with hU
  obtain ⟨σ, hσ⟩ := NormedField.exists_one_lt_norm K
  set ℰ' := insert (0, σ) ℰ
  have hℰ' {e : K × K} (he : e ∈ ℰ') :
      {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C e.2) (T - C e.1)} ⊆ U := by
    rcases Finset.mem_insert.mp he with rfl | he
    · rw [setOf_vle_eq_empty hσ]
      exact Set.empty_subset _
    · exact (Set.subset_biUnion_of_mem
        (u := fun e : K × K ↦ {v : closedPolydisc 1 K |
          v.1.toValuativeRel.vle (C e.2) (T - C e.1)}) he).trans Set.subset_union_right
  have h𝒟 {q : K × K} (hq : q ∈ 𝒟) : closedSubdisc q.1 q.2 ⊆ U :=
    (Set.subset_biUnion_of_mem (u := fun q : K × K ↦ closedSubdisc q.1 q.2) hq).trans
      Set.subset_union_left
  -- a smallest removed open disc
  obtain ⟨e₀, he₀, hmin⟩ := ℰ'.exists_min_image (fun e ↦ ‖e.2‖) ⟨_, Finset.mem_insert_self _ _⟩
  by_cases hcov : ∃ e ∈ ℰ', ‖e.2‖ ≤ ‖e.1 - e₀.1‖
  · obtain ⟨e, he, hle⟩ := hcov
    have hUuniv : U = Set.univ := Set.eq_univ_of_univ_subset <|
      (setOf_vle_union_setOf_vle_eq_univ (b := e.1) (d := e.2) (hmin e he) hle).ge.trans
        (Set.union_subset (hℰ' he) (hℰ' he₀))
    rw [hUuniv]
    exact isRat_univ
  push Not at hcov
  have hd₀ : e₀.2 ≠ 0 := by
    have h := hcov e₀ he₀
    rw [sub_self, norm_zero] at h
    exact norm_pos_iff.mp h
  by_cases hsw : ∃ q ∈ 𝒟, q.2 ≠ 0 ∧ ‖e₀.2‖ ≤ ‖q.2‖ ∧ ‖q.1 - e₀.1‖ ≤ ‖q.2‖
  · obtain ⟨q, hq, hq₀, hd, ha⟩ := hsw
    have hUuniv : U = Set.univ := Set.eq_univ_of_univ_subset <|
      (closedSubdisc_union_setOf_vle_eq_univ hq₀ hd ha).ge.trans
        (Set.union_subset (h𝒟 hq) (hℰ' he₀))
    rw [hUuniv]
    exact isRat_univ
  push Not at hsw
  -- the discs inside `D⁻(b₀, |d₀|)`
  set 𝒟' := 𝒟.filter fun q ↦ q.2 ≠ 0 ∧ ‖q.1 - e₀.1‖ < ‖e₀.2‖ ∧ ‖q.2‖ < ‖e₀.2‖
  have hEq : U = {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C e₀.2) (T - C e₀.1)} ∪
      ⋃ q ∈ 𝒟', closedSubdisc q.1 q.2 := by
    refine subset_antisymm (Set.union_subset (Set.iUnion₂_subset fun q hq ↦ ?_)
      (Set.iUnion₂_subset fun e he ↦ (setOf_vle_subset_setOf_vle (hmin e
        (Finset.mem_insert_of_mem he)) (hcov e (Finset.mem_insert_of_mem he))).trans
          Set.subset_union_left)) (Set.union_subset (hℰ' he₀) (Set.iUnion₂_subset fun q hq ↦
            h𝒟 (Finset.mem_filter.mp hq).1))
    rcases eq_or_ne q.2 0 with hq₀ | hq₀
    · rw [hq₀, closedSubdisc_zero_right]
      exact Set.empty_subset _
    by_cases hin : q ∈ 𝒟'
    · exact (Set.subset_biUnion_of_mem (u := fun q : K × K ↦ closedSubdisc q.1 q.2) hin).trans
        Set.subset_union_right
    -- a disc neither inside `D⁻(b₀, |d₀|)` nor covering it lies outside it
    simp only [𝒟', Finset.mem_filter, hq, hq₀, ne_eq, not_false_eq_true, true_and, not_and,
      not_lt] at hin
    exact (closedSubdisc_subset_setOf_vle_of_not_lt (hsw q hq hq₀) hin).trans
      Set.subset_union_left
  rw [hEq]
  exact isRat_setOf_vle_union_biUnion_closedSubdisc 𝒟' e₀.1 e₀.2 hd₀ fun q hq ↦
    (Finset.mem_filter.mp hq).2

/-- Finite unions of holed discs together with finitely many discs and complements of open discs
are rational. -/
private theorem isRat_biUnion_holedDisc_union (P : Finset (K × K × Finset (K × K))) :
    ∀ 𝒟 ℰ : Finset (K × K), IsRat
      ((⋃ p ∈ P, holedDisc p.1 p.2.1 (fun q : p.2.2 ↦ q.1.1) (fun q ↦ q.1.2)) ∪
        ((⋃ q ∈ 𝒟, closedSubdisc q.1 q.2) ∪
          ⋃ e ∈ ℰ, {v : closedPolydisc 1 K | v.1.toValuativeRel.vle (C e.2) (T - C e.1)})) := by
  -- Induction on the holed discs: a holed disc is the intersection of its outer disc with the
  -- complements of its holes, and the union distributes over this intersection.
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro 𝒟 ℰ
    simpa using isRat_biUnion_closedSubdisc_union_biUnion_setOf_vle 𝒟 ℰ
  | insert p P _ ih =>
    intro 𝒟 ℰ
    rw [Finset.set_biUnion_insert, Set.union_assoc, holedDisc, Set.inter_union_distrib_right,
      Set.iInter_union]
    refine IsRat.inter ?_ (isRat_iInter fun q ↦ ?_)
    · convert ih (insert (p.1, p.2.1) 𝒟) ℰ using 1
      rw [Finset.set_biUnion_insert]
      ext x
      simp only [Set.mem_union]
      tauto
    · convert ih 𝒟 (insert q.1 ℰ) using 1
      rw [Finset.set_biUnion_insert]
      ext x
      simp only [Set.mem_union]
      tauto

/-- **Every finite union of holed discs is a rational subset of the closed unit disc**, over a
nontrivially normed ultrametric field `K`. This is the converse of
`exists_finset_eq_iUnion_holedDisc_of_mem_spaRationalFamily`, and it needs neither completeness
nor algebraic closedness. The degenerate holed discs are allowed: an outer radius `0` gives the
empty set, and a hole of radius `0` removes nothing. -/
theorem IsHoledDiscUnion.mem_spaRationalFamily {S : Set (closedPolydisc 1 K)}
    (hS : IsHoledDiscUnion S) :
    (Homeomorph.setCongr (closedPolydisc_def 1 K)).symm ⁻¹' S ∈
      spaRationalFamily (powerBoundedSubring (𝒯 K)) := by
  obtain ⟨P, rfl⟩ := hS
  have h := isRat_biUnion_holedDisc_union P ∅ ∅
  simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] at h
  exact h

end Rational

end TauCeti.ValuationSpectrum
