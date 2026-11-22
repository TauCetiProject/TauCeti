/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.Constructible

/-!
# Constructible stratifications of schemes

Let `X` be a scheme and `U` an open subscheme of `X`. A *constructible stratification* of `U`
consists of finitely many immersions into `X` whose images are pairwise disjoint, cover `U`, and
are constructible subsets of `U` in the sense of `Topology.IsConstructible`.

A sheaf of `Λ`-modules on the small étale site of `X` is constructible when every affine open
`U` of `X` has a constructible stratification on whose pieces the sheaf becomes locally constant
of finite type (Stacks 03RW). This file provides the stratifications, independently of sheaves:
the stratification of `U` by `U` itself, the common refinement of two stratifications, the
restriction to a smaller open, and the pullback along an arbitrary morphism of schemes. No
Noetherian hypothesis on `X` enters, and constructibility is that of Mathlib, so the image of a
piece need not be constructible when `U` is not quasi-compact and quasi-separated.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.ConstructibleStratification X U`: a constructible
  stratification of the open `U` of `X`.
* `TauCeti.AlgebraicGeometry.Scheme.ConstructibleStratification.existsUnique_mem_range`: every
  point of `U` lies in exactly one piece.
* `TauCeti.AlgebraicGeometry.Scheme.ConstructibleStratification.Refines`: every piece of one
  stratification lies in a piece of the other.
* `TauCeti.AlgebraicGeometry.Scheme.ConstructibleStratification.single`: the stratification of
  `U` with the single piece `U`.
* `TauCeti.AlgebraicGeometry.Scheme.ConstructibleStratification.inf`: the common refinement of
  two stratifications of `U`.
* `TauCeti.AlgebraicGeometry.Scheme.ConstructibleStratification.restrict`: the restriction of a
  stratification of `U` to an open `V ≤ U`.
* `TauCeti.AlgebraicGeometry.Scheme.ConstructibleStratification.pullback`: the pullback of a
  stratification of `U` along `f : Y ⟶ X`, a stratification of `f ⁻¹ᵁ U`.

## References

* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Tag 03RW (constructible étale sheaves) and Section 5.15 (constructible
  sets).
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Function Topology

namespace TauCeti.AlgebraicGeometry.Scheme

/-- A *constructible stratification* of an open `U` of a scheme `X`: finitely many immersions
into `X` with pairwise disjoint images covering `U`, each image a constructible subset of `U`. -/
structure ConstructibleStratification (X : Scheme.{u}) (U : X.Opens) where
  /-- The index type of the pieces. -/
  ι : Type u
  [finite_ι : Finite ι]
  /-- The pieces of the stratification. -/
  obj (i : ι) : Scheme.{u}
  /-- The immersion of each piece into `X`. -/
  hom (i : ι) : obj i ⟶ X
  [isImmersion_hom (i : ι) : IsImmersion (hom i)]
  pairwiseDisjoint : _root_.Pairwise (Disjoint on fun i ↦ Set.range (hom i))
  iUnion_range : ⋃ i, Set.range (hom i) = U
  isConstructible (i : ι) : IsConstructible (U.ι ⁻¹' Set.range (hom i))

namespace ConstructibleStratification

attribute [instance] finite_ι isImmersion_hom

variable {X : Scheme.{u}} {U : X.Opens} (𝒮 : ConstructibleStratification X U)

/-- A point of `X` lies in some piece of a stratification of `U` if and only if it lies in `U`. -/
lemma exists_mem_range_iff {x : X} : (∃ i, x ∈ Set.range (𝒮.hom i)) ↔ x ∈ U := by
  rw [← SetLike.mem_coe, ← 𝒮.iUnion_range, Set.mem_iUnion]

lemma range_subset (i : 𝒮.ι) : Set.range (𝒮.hom i) ⊆ U :=
  fun _ hx ↦ 𝒮.exists_mem_range_iff.1 ⟨i, hx⟩

/-- Every point of `U` lies in exactly one piece of a stratification of `U`. -/
lemma existsUnique_mem_range {x : X} (hx : x ∈ U) : ∃! i, x ∈ Set.range (𝒮.hom i) := by
  obtain ⟨i, hi⟩ := 𝒮.exists_mem_range_iff.2 hx
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  by_contra hji
  exact Set.disjoint_left.1 (𝒮.pairwiseDisjoint hji) hj hi

/-- A stratification `𝒯` *refines* `𝒮` if every piece of `𝒯` lies in a piece of `𝒮`. -/
@[expose]
def Refines (𝒯 𝒮 : ConstructibleStratification X U) : Prop :=
  ∀ j, ∃ i, Set.range (𝒯.hom j) ⊆ Set.range (𝒮.hom i)

@[refl]
lemma Refines.refl : 𝒮.Refines 𝒮 :=
  fun i ↦ ⟨i, subset_rfl⟩

lemma Refines.trans {𝒮₁ 𝒮₂ 𝒮₃ : ConstructibleStratification X U} (h₁₂ : 𝒮₁.Refines 𝒮₂)
    (h₂₃ : 𝒮₂.Refines 𝒮₃) : 𝒮₁.Refines 𝒮₃ := fun i ↦
  have ⟨j, hj⟩ := h₁₂ i
  have ⟨k, hk⟩ := h₂₃ j
  ⟨k, hj.trans hk⟩

variable (U) in
/-- The stratification of `U` with the single piece `U`. -/
@[expose]
def single : ConstructibleStratification X U where
  ι := PUnit
  obj _ := U
  hom _ := U.ι
  pairwiseDisjoint i j h := (h (Subsingleton.elim i j)).elim
  iUnion_range := by rw [Set.iUnion_const, Scheme.Opens.range_ι]
  isConstructible _ := by rw [Set.preimage_range]; exact .univ

variable (U) in
@[simp]
lemma range_single_hom (i : (single U).ι) : Set.range ((single U).hom i) = U :=
  Scheme.Opens.range_ι U

/-- Every stratification of `U` refines the stratification with the single piece `U`. -/
lemma refines_single : 𝒮.Refines (single U) :=
  fun i ↦ ⟨.unit, (𝒮.range_subset i).trans (range_single_hom U _).ge⟩

/-- The common refinement of two stratifications of `U`: its pieces are the fibre products over
`X` of the pieces of the two, whose images are the intersections of their images. -/
@[expose]
noncomputable def inf (𝒮 𝒯 : ConstructibleStratification X U) :
    ConstructibleStratification X U where
  ι := 𝒮.ι × 𝒯.ι
  obj i := Limits.pullback (𝒮.hom i.1) (𝒯.hom i.2)
  hom i := Limits.pullback.fst _ _ ≫ 𝒮.hom i.1
  pairwiseDisjoint := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [Function.onFun, Scheme.Pullback.range_fst_comp]
    by_cases hi : i = i'
    · subst hi
      have hj : j ≠ j' := fun hj ↦ h (by rw [hj])
      exact (𝒯.pairwiseDisjoint hj).mono Set.inter_subset_right Set.inter_subset_right
    · exact (𝒮.pairwiseDisjoint hi).mono Set.inter_subset_left Set.inter_subset_left
  iUnion_range := by
    ext x
    simp only [Set.mem_iUnion, Prod.exists, Scheme.Pullback.range_fst_comp, Set.mem_inter_iff,
      SetLike.mem_coe]
    refine ⟨fun ⟨i, _, hi, _⟩ ↦ 𝒮.exists_mem_range_iff.1 ⟨i, hi⟩, fun hx ↦ ?_⟩
    obtain ⟨i, hi⟩ := 𝒮.exists_mem_range_iff.2 hx
    obtain ⟨j, hj⟩ := 𝒯.exists_mem_range_iff.2 hx
    exact ⟨i, j, hi, hj⟩
  isConstructible i := by
    rw [Scheme.Pullback.range_fst_comp, Set.preimage_inter]
    exact (𝒮.isConstructible i.1).inter (𝒯.isConstructible i.2)

/-- The pieces of the common refinement are the intersections of the pieces. -/
@[simp]
lemma range_inf_hom (𝒯 : ConstructibleStratification X U) (i : 𝒮.ι × 𝒯.ι) :
    Set.range ((𝒮.inf 𝒯).hom i) = Set.range (𝒮.hom i.1) ∩ Set.range (𝒯.hom i.2) :=
  Scheme.Pullback.range_fst_comp _ _

lemma inf_refines_left (𝒯 : ConstructibleStratification X U) : (𝒮.inf 𝒯).Refines 𝒮 :=
  fun i ↦ ⟨i.1, (𝒮.range_inf_hom 𝒯 i).trans_subset Set.inter_subset_left⟩

lemma inf_refines_right (𝒯 : ConstructibleStratification X U) : (𝒮.inf 𝒯).Refines 𝒯 :=
  fun i ↦ ⟨i.2, (𝒮.range_inf_hom 𝒯 i).trans_subset Set.inter_subset_right⟩

/-- A stratification refining both `𝒮` and `𝒯` refines their common refinement. -/
lemma Refines.inf {𝒮 𝒯 𝒰 : ConstructibleStratification X U} (h𝒮 : 𝒰.Refines 𝒮)
    (h𝒯 : 𝒰.Refines 𝒯) : 𝒰.Refines (𝒮.inf 𝒯) := fun k ↦
  have ⟨i, hi⟩ := h𝒮 k
  have ⟨j, hj⟩ := h𝒯 k
  ⟨(i, j), (𝒮.range_inf_hom 𝒯 (i, j)).symm ▸ Set.subset_inter hi hj⟩

/-- The restriction of a stratification of `U` to an open `V ≤ U`: its pieces are the fibre
products over `X` of the pieces with `V`. -/
@[expose]
noncomputable def restrict {V : X.Opens} (hVU : V ≤ U) : ConstructibleStratification X V where
  ι := 𝒮.ι
  obj i := Limits.pullback (𝒮.hom i) V.ι
  hom i := Limits.pullback.fst _ _ ≫ 𝒮.hom i
  pairwiseDisjoint i j h := by
    simp only [Function.onFun, Scheme.Pullback.range_fst_comp]
    exact (𝒮.pairwiseDisjoint h).mono Set.inter_subset_left Set.inter_subset_left
  iUnion_range := by
    simp only [Scheme.Pullback.range_fst_comp]
    rw [← Set.iUnion_inter, 𝒮.iUnion_range, Scheme.Opens.range_ι,
      Set.inter_eq_right.2 (by exact hVU)]
  isConstructible i := by
    convert (X.homOfLE hVU).isConstructible_preimage (𝒮.isConstructible i) using 1
    ext x
    simp only [Set.mem_preimage, Scheme.Pullback.range_fst_comp, ← Scheme.Hom.comp_apply,
      Scheme.homOfLE_ι, Set.mem_inter_iff, Set.mem_range_self, and_true]

/-- The pieces of the restriction to `V` are the intersections of the pieces with `V`. -/
@[simp]
lemma range_restrict_hom {V : X.Opens} (hVU : V ≤ U) (i : 𝒮.ι) :
    Set.range ((𝒮.restrict hVU).hom i) = Set.range (𝒮.hom i) ∩ V := by
  rw [← Scheme.Opens.range_ι V]
  exact Scheme.Pullback.range_fst_comp _ _

/-- The restriction to `V` of a refinement is a refinement of the restriction. -/
lemma Refines.restrict {𝒮 𝒯 : ConstructibleStratification X U} (h : 𝒯.Refines 𝒮)
    {V : X.Opens} (hVU : V ≤ U) : (𝒯.restrict hVU).Refines (𝒮.restrict hVU) := fun j ↦
  have ⟨i, hi⟩ := h j
  ⟨i, (𝒯.range_restrict_hom hVU j).trans_subset
    ((Set.inter_subset_inter_left _ hi).trans (𝒮.range_restrict_hom hVU i).ge)⟩

/-- The pullback of a stratification of `U` along a morphism `f : Y ⟶ X`, a stratification of
`f ⁻¹ᵁ U` whose pieces are the fibre products over `X` of the pieces with `Y`. -/
@[expose]
noncomputable def pullback {Y : Scheme.{u}} (f : Y ⟶ X) :
    ConstructibleStratification Y (f ⁻¹ᵁ U) where
  ι := 𝒮.ι
  obj i := Limits.pullback (𝒮.hom i) f
  hom i := Limits.pullback.snd _ _
  pairwiseDisjoint i j h := by
    simpa [Function.onFun, Scheme.Pullback.range_snd] using (𝒮.pairwiseDisjoint h).preimage f
  iUnion_range := by
    simp [Scheme.Pullback.range_snd, ← Set.preimage_iUnion, 𝒮.iUnion_range]
  isConstructible i := by
    convert (f ∣_ U).isConstructible_preimage (𝒮.isConstructible i) using 1
    ext x
    simp only [Set.mem_preimage, Scheme.Pullback.range_snd, ← Scheme.Hom.comp_apply,
      morphismRestrict_ι]

/-- The pieces of the pullback along `f` are the preimages of the pieces. -/
@[simp]
lemma range_pullback_hom {Y : Scheme.{u}} (f : Y ⟶ X) (i : 𝒮.ι) :
    Set.range ((𝒮.pullback f).hom i) = f ⁻¹' Set.range (𝒮.hom i) :=
  Scheme.Pullback.range_snd _ _

/-- The pullback of a refinement is a refinement of the pullback. -/
lemma Refines.pullback {𝒮 𝒯 : ConstructibleStratification X U} (h : 𝒯.Refines 𝒮)
    {Y : Scheme.{u}} (f : Y ⟶ X) : (𝒯.pullback f).Refines (𝒮.pullback f) := fun j ↦
  have ⟨i, hi⟩ := h j
  ⟨i, (𝒯.range_pullback_hom f j).trans_subset
    ((Set.preimage_mono hi).trans (𝒮.range_pullback_hom f i).ge)⟩

end ConstructibleStratification

end TauCeti.AlgebraicGeometry.Scheme
