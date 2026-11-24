/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Radial.Polydisc
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
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

The punctured disc and its annuli are the traces on the closed unit disc of the punctured
closed disc `𝔻^×(A⟨T⟩°, T, 1)` and the closed annuli `𝔸(A⟨T⟩°, T, c^(n+1), 1)` of
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.Radial.Basic`, so the pointwise exhaustion is
`iUnion_closedAnnulus_pow`. The witnesses of noncompactness use `classicalPoint` and its
evaluation formulas.
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

/-- The complement of the coordinate zero locus in the closed unit disc: the trace of the
punctured closed disc `𝔻^×(A⟨T⟩°, T, 1)`. -/
noncomputable def puncturedDisc (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] : Set (closedPolydisc 1 A) :=
  Subtype.val ⁻¹' puncturedClosedDisc
    (powerBoundedSubring (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A))
      isWeightFamily_one_weight))
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0) 1

/-- **The punctured closed unit disc is a punctured closed disc**: `puncturedDisc A` is the
trace on the closed unit disc of `𝔻^×(A⟨T⟩°, T, 1)`. -/
theorem puncturedDisc_eq_val_preimage_puncturedClosedDisc :
    puncturedDisc A = Subtype.val ⁻¹' puncturedClosedDisc (powerBoundedSubring 𝒯) T 1 :=
  (rfl)

/-- A point of the closed disc lies in the punctured disc exactly when its coordinate
has nonzero valuation. -/
@[simp]
theorem mem_puncturedDisc (v : closedPolydisc 1 A) :
    v ∈ puncturedDisc A ↔ ¬ v.val.toValuativeRel.vle T 0 := by
  obtain ⟨hv, hT⟩ := (mem_closedDisc_iff _ _ _ _).mp (val_mem_closedDisc_one v)
  simp [puncturedDisc_eq_val_preimage_puncturedClosedDisc, hv, hT]

/-- The annulus `|c|^(n+1) ≤ |T| ≠ 0` in the closed unit disc: the trace of the closed annulus
`𝔸(A⟨T⟩°, T, c^(n+1), 1)`. -/
noncomputable def puncturedDiscAnnulus (c : A) (n : ℕ) : Set (closedPolydisc 1 A) :=
  Subtype.val ⁻¹' closedAnnulus (powerBoundedSubring 𝒯) T (C (c ^ (n + 1))) 1

/-- **The exhaustion annuli of the punctured unit disc are closed annuli**: the annulus
`|c|^(n+1) ≤ |T|` of `puncturedDiscAnnulus` is the trace on the closed unit disc of
`𝔸(A⟨T⟩°, T, c^(n+1), 1)`. -/
theorem puncturedDiscAnnulus_eq_val_preimage_closedAnnulus (c : A) (n : ℕ) :
    puncturedDiscAnnulus c n =
      Subtype.val ⁻¹' closedAnnulus (powerBoundedSubring 𝒯) T (C (c ^ (n + 1))) 1 :=
  (rfl)

/-- The defining inequality and nonvanishing condition of an exhaustion annulus. -/
@[simp]
theorem mem_puncturedDiscAnnulus (c : A) (n : ℕ) (v : closedPolydisc 1 A) :
    v ∈ puncturedDiscAnnulus c n ↔
      v.val.toValuativeRel.vle (C (c ^ (n + 1))) T ∧ ¬ v.val.toValuativeRel.vle T 0 := by
  obtain ⟨hv, hT⟩ := (mem_closedDisc_iff _ _ _ _).mp (val_mem_closedDisc_one v)
  simp [puncturedDiscAnnulus_eq_val_preimage_closedAnnulus, hv, hT]

/-- Every exhaustion annulus is open in the closed unit disc. -/
theorem isOpen_puncturedDiscAnnulus (c : A) (n : ℕ) : IsOpen (puncturedDiscAnnulus c n) :=
  (isOpen_val_preimage_closedAnnulus _ _ _ _).preimage
    (Homeomorph.setCongr (closedPolydisc_def 1 A)).continuous

/-- An exhaustion annulus lies in the punctured disc. -/
theorem puncturedDiscAnnulus_subset (c : A) (n : ℕ) :
    puncturedDiscAnnulus c n ⊆ puncturedDisc A :=
  Set.preimage_mono (closedAnnulus_subset_puncturedClosedDisc _ _ _ _)

/-- The rational inequalities for an exhaustion annulus have numerator `c^(n+1)` and
denominator `T`; a unit `c` makes this rational datum admissible. -/
theorem puncturedDiscAnnulus_eq_rationalSubset (c : A) (n : ℕ) :
    puncturedDiscAnnulus c n = Subtype.val ⁻¹'
      rationalSubset (powerBoundedSubring 𝒯) {C (c ^ (n + 1))} T := by
  classical
  ext v
  simp [mem_puncturedDiscAnnulus, mem_rationalSubset_iff,
    closedDisc_subset_spa _ _ _ (val_mem_closedDisc_one v)]

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
    Monotone (puncturedDiscAnnulus c) := fun n m hnm ↦ by
  simp only [puncturedDiscAnnulus_eq_val_preimage_closedAnnulus, map_pow]
  exact Set.preimage_mono (monotone_closedAnnulus_pow _ _ _
    (hc.map (continuous_weightedC isWeightFamily_one_weight)) (Nat.succ_le_succ hnm))

/-- The annuli exhaust the punctured closed disc: this is `iUnion_closedAnnulus_pow` for the
radius parameter `C c`, shifted by one exponent. -/
theorem iUnion_puncturedDiscAnnulus {c : A} (hc : IsTopologicallyNilpotent c) :
    (⋃ n, puncturedDiscAnnulus c n) = puncturedDisc A := by
  have hnil : IsTopologicallyNilpotent (C c) :=
    hc.map (continuous_weightedC isWeightFamily_one_weight)
  refine Set.Subset.antisymm (Set.iUnion_subset (puncturedDiscAnnulus_subset c)) fun v hv ↦ ?_
  rw [puncturedDisc_eq_val_preimage_puncturedClosedDisc, Set.mem_preimage,
    ← iUnion_closedAnnulus_pow _ _ _ hnil, Set.mem_iUnion] at hv
  obtain ⟨n, hn⟩ := hv
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  rw [puncturedDiscAnnulus_eq_val_preimage_closedAnnulus, Set.mem_preimage, map_pow]
  exact monotone_closedAnnulus_pow _ _ _ hnil n.le_succ hn

/-- Every compact subset of the punctured disc is bounded away from the missing origin. -/
theorem exists_subset_puncturedDiscAnnulus_of_isCompact {c : A}
    (hc : IsTopologicallyNilpotent c) {S : Set (closedPolydisc 1 A)}
    (hS : IsCompact S) (hSp : S ⊆ puncturedDisc A) :
    ∃ n, S ⊆ puncturedDiscAnnulus c n :=
  hS.elim_directed_cover _ (isOpen_puncturedDiscAnnulus c)
    (by rwa [iUnion_puncturedDiscAnnulus hc]) (monotone_puncturedDiscAnnulus hc).directed_le

/-- The complement of the coordinate zero locus is open in the closed disc. -/
theorem isOpen_puncturedDisc : IsOpen (puncturedDisc A) :=
  (isOpen_val_preimage_puncturedClosedDisc _ _ _).preimage
    (Homeomorph.setCongr (closedPolydisc_def 1 A)).continuous

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
  have hcont := (isContinuous_def x.val).mp ((mem_spa_iff _ _).mp x.property).1
  have hcval : x.val.valuation c < 1 :=
    hcont.lt_one_of_isTopologicallyNilpotent hc.isTopologicallyNilpotent
  have hne (k : ℕ) : x.val.valuation (c ^ k) ≠ 0 := ((hc.isUnit.pow k).map x.val.valuation).ne_zero
  have hlt : x.val.valuation (c ^ (n + 2)) < x.val.valuation (c ^ (n + 1)) := by
    have hexp : n + 2 = (n + 1) + 1 := by omega
    rw [hexp, pow_succ, map_mul]
    simpa using mul_lt_mul_of_pos_left hcval (pos_iff_ne_zero.mpr (hne (n + 1)))
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
    rw [← Set.ne_empty_iff_nonempty, ne_eq,
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
