/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.AlgebraicGeometry.AdicSpace.Cont.DominatingUnit
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# The punctured closed disc is not quasi-compact

The complement of the coordinate zero locus in the closed unit disc is the increasing
union of the rational annuli `|c|^(n+1) ≤ |T|`, for any topologically nilpotent unit `c`.
Every compact subset lies in one annulus. The classical point `T = c^(n+2)` escapes the
`n`-th annulus, so no finite subfamily covers the punctured disc and it is not compact.

These statements use arbitrary continuous valuations, including higher-rank points.
Noncompactness holds over every nontrivial complete Hausdorff nonarchimedean Tate ring;
in particular it holds over complete topological Tate fields without choosing a norm.
This explains why the inclusion of a boundary complement into an affinoid need not be
quasi-compact.

## References

* B. Conrad, *Several approaches to non-archimedean geometry*, Exercise 2.4.8(1)–(2).
* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, §1.1,
  for quasi-compact rational opens.

The pointwise exhaustion uses
`IsContinuous.exists_pow_vlt_of_isTopologicallyNilpotent`; its witnesses use
`classicalPoint` and its evaluation formulas.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

section TopologicalRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight

/-- The complement of the coordinate zero locus in the closed unit disc. -/
noncomputable def puncturedDisc (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] : Set (closedPolydisc 1 A) :=
  {v | weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 ∉ v.1.supp}

/-- A point of the closed disc lies in the punctured disc exactly when its coordinate
has nonzero valuation. -/
@[simp]
theorem mem_puncturedDisc (v : closedPolydisc 1 A) :
    v ∈ puncturedDisc A ↔ ¬ v.1.toValuativeRel.vle T 0 := by
  simp [puncturedDisc, mem_supp_iff]

/-- The annulus `|c|^(n+1) ≤ |T| ≠ 0` in the closed unit disc. -/
noncomputable def puncturedDiscAnnulus (c : A) (n : ℕ) : Set (closedPolydisc 1 A) :=
  Subtype.val ⁻¹' basicOpen (C (c ^ (n + 1))) T

/-- The defining inequality and nonvanishing condition of an exhaustion annulus. -/
@[simp]
theorem mem_puncturedDiscAnnulus (c : A) (n : ℕ) (v : closedPolydisc 1 A) :
    v ∈ puncturedDiscAnnulus c n ↔
      v.1.toValuativeRel.vle (C (c ^ (n + 1))) T ∧ ¬ v.1.toValuativeRel.vle T 0 := by
  rw [puncturedDiscAnnulus, Set.mem_preimage, mem_basicOpen_iff]

/-- Every exhaustion annulus is open in the closed unit disc. -/
theorem isOpen_puncturedDiscAnnulus (c : A) (n : ℕ) : IsOpen (puncturedDiscAnnulus c n) :=
  (isOpen_basicOpen _ _).preimage continuous_subtype_val

/-- An exhaustion annulus lies in the punctured disc. -/
theorem puncturedDiscAnnulus_subset (c : A) (n : ℕ) :
    puncturedDiscAnnulus c n ⊆ puncturedDisc A :=
  fun v hv ↦ (mem_puncturedDisc v).mpr ((mem_puncturedDiscAnnulus c n v).mp hv).2

/-- The rational inequalities for an exhaustion annulus have numerator `c^(n+1)` and
denominator `T`; a unit `c` makes this rational datum admissible. -/
theorem puncturedDiscAnnulus_eq_rationalSubset (c : A) (n : ℕ) :
    puncturedDiscAnnulus c n = Subtype.val ⁻¹'
      rationalSubset (powerBoundedSubring 𝒯) {C (c ^ (n + 1))} T := by
  classical
  ext v
  have hv : v.1 ∈ spa (powerBoundedSubring 𝒯) := closedPolydisc_def 1 A ▸ v.2
  simp [mem_puncturedDiscAnnulus, mem_rationalSubset_iff, hv]

/-- Annuli with a unit radius parameter are quasi-compact rational opens. -/
theorem isCompact_puncturedDiscAnnulus [IsHuberRing A] {c : A} (hc : IsUnit c) (n : ℕ) :
    IsCompact (puncturedDiscAnnulus c n) := by
  classical
  have hspan : Ideal.span (({C (c ^ (n + 1))} : Finset 𝒯) : Set 𝒯) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) ((hc.pow (n + 1)).map C)
  have hcompact := isCompact_of_mem_spaRationalFamily (Aplus := powerBoundedSubring 𝒯)
    (mem_spaRationalFamily_iff.mpr ⟨{C (c ^ (n + 1))}, T,
      by rw [hspan]; simp, rfl⟩)
  rw [puncturedDiscAnnulus_eq_rationalSubset]
  exact (Homeomorph.setCongr (closedPolydisc_def 1 A)).isClosedEmbedding.isCompact_preimage
    hcompact

/-- Annuli increase with the exponent of a topologically nilpotent radius parameter. -/
theorem monotone_puncturedDiscAnnulus {c : A} (hc : IsTopologicallyNilpotent c) :
    Monotone (puncturedDiscAnnulus c) := by
  intro n m hnm v hv
  rw [mem_puncturedDiscAnnulus] at hv ⊢
  have hcont := (isContinuous_def v.1).mp ((mem_closedPolydisc_iff 1 A v.1).mp v.2).1
  have hnil : IsTopologicallyNilpotent (C c) :=
    hc.map (continuous_weightedC isWeightFamily_one_weight)
  have hn : v.1.valuation (C c) ^ (n + 1) ≤ v.1.valuation T := by
    simpa only [map_pow] using (valuation_le_iff v.1 _ _).mpr hv.1
  refine ⟨(valuation_le_iff v.1 _ _).mp ?_, hv.2⟩
  simpa only [map_pow] using (pow_le_pow_of_le_one zero_le
    (hcont.lt_one_of_isTopologicallyNilpotent hnil).le
      (Nat.add_le_add_right hnm 1)).trans hn

/-- The annuli exhaust the punctured closed disc. -/
theorem iUnion_puncturedDiscAnnulus {c : A} (hc : IsTopologicallyNilpotent c) :
    (⋃ n, puncturedDiscAnnulus c n) = puncturedDisc A := by
  apply Set.Subset.antisymm (Set.iUnion_subset (puncturedDiscAnnulus_subset c))
  intro v hv
  have hcont := ((mem_closedPolydisc_iff 1 A v.1).mp v.2).1
  have hnil : IsTopologicallyNilpotent (C c) :=
    hc.map (continuous_weightedC isWeightFamily_one_weight)
  obtain ⟨n, hn⟩ := hcont.exists_pow_vlt_of_isTopologicallyNilpotent hnil
    (by simpa only [mem_supp_iff] using (mem_puncturedDisc v).mp hv)
  have hvalcont := (isContinuous_def v.1).mp hcont
  apply Set.mem_iUnion.mpr
  refine ⟨n, (mem_puncturedDiscAnnulus c n v).mpr ⟨?_, (mem_puncturedDisc v).mp hv⟩⟩
  have hnval : v.1.valuation (C c) ^ n < v.1.valuation T := by
    simpa only [map_pow] using (valuation_lt_iff v.1 _ _).mpr hn
  apply (valuation_le_iff v.1 _ _).mp
  simpa only [map_pow] using
    (pow_le_pow_of_le_one zero_le (hvalcont.lt_one_of_isTopologicallyNilpotent hnil).le
      (Nat.le_succ n)).trans hnval.le

/-- Every compact subset of the punctured disc is bounded away from the missing origin. -/
theorem exists_subset_puncturedDiscAnnulus_of_isCompact {c : A}
    (hc : IsTopologicallyNilpotent c) {S : Set (closedPolydisc 1 A)}
    (hS : IsCompact S) (hSp : S ⊆ puncturedDisc A) :
    ∃ n, S ⊆ puncturedDiscAnnulus c n :=
  hS.elim_directed_cover _ (isOpen_puncturedDiscAnnulus c)
    (by rwa [iUnion_puncturedDiscAnnulus hc]) (monotone_puncturedDiscAnnulus hc).directed_le

/-- The complement of the coordinate zero locus is open in the closed disc. -/
theorem isOpen_puncturedDisc : IsOpen (puncturedDisc A) := by
  have h : puncturedDisc A = Subtype.val ⁻¹' basicOpen (0 : 𝒯) T := by
    ext v
    simp [mem_puncturedDisc, mem_basicOpen_iff, ← valuation_le_iff]
  rw [h]
  exact (isOpen_basicOpen _ _).preimage continuous_subtype_val

end TopologicalRing

section CompleteRing

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A] [T2Space A]

local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight

/-- The classical point `T = c^(n+2)` belongs to the punctured disc and escapes the
`n`-th annulus. -/
theorem classicalPoint_pow_mem_puncturedDisc_notMem_annulus
    (x : spa (powerBoundedSubring A)) {c : A} (hc : IsPseudoUniformizer c) (n : ℕ) :
    let ha : ∀ _ : Fin 1, IsPowerBounded (c ^ (n + 2)) :=
      fun _ ↦ (IsPowerBounded.of_isTopologicallyNilpotent hc.isTopologicallyNilpotent).pow _
    classicalPoint x (fun _ : Fin 1 ↦ c ^ (n + 2)) ha ∈ puncturedDisc A ∧
      classicalPoint x (fun _ : Fin 1 ↦ c ^ (n + 2)) ha ∉ puncturedDiscAnnulus c n := by
  dsimp only
  have hcont := (isContinuous_def x.1).mp ((mem_spa_iff _ _).mp x.2).1
  have hcval : x.1.valuation c < 1 :=
    hcont.lt_one_of_isTopologicallyNilpotent hc.isTopologicallyNilpotent
  have hne (k : ℕ) : x.1.valuation (c ^ k) ≠ 0 := ((hc.isUnit.pow k).map x.1.valuation).ne_zero
  have hlt : x.1.valuation (c ^ (n + 2)) < x.1.valuation (c ^ (n + 1)) := by
    have hexp : n + 2 = (n + 1) + 1 := by omega
    rw [hexp, pow_succ, map_mul]
    simpa using mul_lt_mul_of_pos_left hcval (zero_lt_iff.mpr (hne (n + 1)))
  simp only [mem_puncturedDisc, mem_puncturedDiscAnnulus]
  simp only [classicalPoint_vle, evalAtHom_weightedX, evalAtHom_weightedC, map_zero]
  simp only [← valuation_le_iff, map_zero]
  exact ⟨by simpa using hne (n + 2), fun h ↦ hlt.not_ge h.1⟩

section HuberRing

variable [Nontrivial A] [IsHuberRing A]

/-- Each annulus misses a point of the punctured closed disc. -/
theorem exists_mem_puncturedDisc_notMem_annulus {c : A} (hc : IsPseudoUniformizer c) (n : ℕ) :
    ∃ v ∈ puncturedDisc A, v ∉ puncturedDiscAnnulus c n := by
  have hplus : IsRingOfIntegralElements (powerBoundedSubring A) := by
    simpa only [Pair.powerBounded_plus] using (Pair.powerBounded A).isRingOfIntegralElements
  have hne : (spa (powerBoundedSubring A)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ne_eq,
      spa_eq_empty_iff_subsingleton _ hplus]
    exact not_subsingleton A
  obtain ⟨x, hx⟩ := hne
  exact ⟨_, classicalPoint_pow_mem_puncturedDisc_notMem_annulus ⟨x, hx⟩ hc n⟩

/-- No finite family of the rational exhaustion annuli covers the punctured disc. -/
theorem not_subset_biUnion_puncturedDiscAnnulus {c : A} (hc : IsPseudoUniformizer c)
    (s : Finset ℕ) : ¬ puncturedDisc A ⊆ ⋃ n ∈ s, puncturedDiscAnnulus c n := by
  obtain ⟨v, hv, hnot⟩ := exists_mem_puncturedDisc_notMem_annulus hc (s.sup id)
  intro hcover
  obtain ⟨n, hn, hvn⟩ := Set.mem_iUnion₂.mp (hcover hv)
  exact hnot (monotone_puncturedDiscAnnulus hc.isTopologicallyNilpotent
    (Finset.le_sup (f := id) hn) hvn)

end HuberRing

/-- The punctured closed disc over a nontrivial complete Hausdorff Tate ring is not compact. -/
theorem not_isCompact_puncturedDisc [Nontrivial A] [IsTateRing A] :
    ¬ IsCompact (puncturedDisc A) := by
  obtain ⟨c, hc⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  intro h
  obtain ⟨n, hn⟩ := exists_subset_puncturedDiscAnnulus_of_isCompact
    hc.isTopologicallyNilpotent h Set.Subset.rfl
  obtain ⟨v, hv, hnot⟩ := exists_mem_puncturedDisc_notMem_annulus hc n
  exact hnot (hn hv)

end CompleteRing

end TauCeti.ValuationSpectrum
