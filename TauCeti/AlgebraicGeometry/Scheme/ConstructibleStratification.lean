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
public import TauCeti.Topology.Stratification

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
Noetherian hypothesis on `X` enters. Constructibility of the images is imposed as a field, since
the image of an immersion need not be constructible, even when `U` is affine: a non-quasi-compact
open of an affine scheme is the image of an open immersion but is not constructible.

The images of the pieces form a finite locally closed stratification of `U`, and refinement is
the order on `TauCeti.FiniteStratification`, so a piece with empty image plays no role in it.

## Main declarations

* `AlgebraicGeometry.Scheme.ConstructibleStratification X U`: a constructible stratification of
  the open `U` of `X`.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.existsUnique_mem_range`: every point of
  `U` lies in exactly one piece.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.toFiniteStratification`: the finite
  locally closed stratification of `U` by the images of the pieces.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.Refines`: refinement of the images of the
  pieces.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.single`: the stratification of `U` with
  the single piece `U`.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.inf`: the common refinement of two
  stratifications of `U`.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.restrict`: the restriction of a
  stratification of `U` to an open `V ≤ U`.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.pullback`: the pullback of a
  stratification of `U` along `f : Y ⟶ X`, a stratification of `f ⁻¹ᵁ U`.

## References

* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Tag 03RW (constructible étale sheaves) and Section 5.15 (constructible
  sets).
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Function Topology

namespace AlgebraicGeometry.Scheme

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

/-- The finite locally closed stratification of `U` whose strata are the nonempty images of the
pieces of `𝒮`. -/
noncomputable def toFiniteStratification : TauCeti.FiniteStratification U :=
  TauCeti.FiniteStratification.ofErase
    (Set.finite_range fun i ↦ U.ι ⁻¹' Set.range (𝒮.hom i)).toFinset
    (by
      rw [Set.Finite.coe_toFinset]
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
      exact (𝒮.pairwiseDisjoint fun h ↦ hij (by rw [h])).preimage _)
    (by
      rw [Set.Finite.coe_toFinset, Set.sUnion_range, ← Set.preimage_iUnion, 𝒮.iUnion_range,
        ← Scheme.Opens.range_ι, Set.preimage_range])
    (by
      simp only [Set.Finite.mem_toFinset, Set.forall_mem_range]
      exact fun i ↦ (𝒮.hom i).isLocallyClosed_range.preimage U.ι.continuous)

/-- The strata of `𝒮.toFiniteStratification` are the nonempty images of the pieces of `𝒮`. -/
@[simp]
lemma mem_toFiniteStratification_parts {s : Set U} :
    s ∈ 𝒮.toFiniteStratification.parts ↔
      s.Nonempty ∧ ∃ i, U.ι ⁻¹' Set.range (𝒮.hom i) = s := by
  simp [toFiniteStratification]

/-- A stratification `𝒯` *refines* `𝒮` if every nonempty piece of `𝒯` lies in a piece of `𝒮`,
that is, if the stratification of `U` by the images of the pieces of `𝒯` refines that of `𝒮`. -/
def Refines (𝒯 𝒮 : ConstructibleStratification X U) : Prop :=
  𝒯.toFiniteStratification ≤ 𝒮.toFiniteStratification

lemma refines_iff {𝒮 𝒯 : ConstructibleStratification X U} :
    𝒯.Refines 𝒮 ↔ 𝒯.toFiniteStratification ≤ 𝒮.toFiniteStratification :=
  Iff.rfl

/-- Every nonempty piece of a refinement lies in a piece of the coarser stratification. -/
lemma Refines.exists_range_subset {𝒮 𝒯 : ConstructibleStratification X U} (h : 𝒯.Refines 𝒮)
    (j : 𝒯.ι) (hj : (Set.range (𝒯.hom j)).Nonempty) :
    ∃ i, Set.range (𝒯.hom j) ⊆ Set.range (𝒮.hom i) := by
  obtain ⟨_, x, rfl⟩ := hj
  obtain ⟨y, hy⟩ : 𝒯.hom j x ∈ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact 𝒯.range_subset j ⟨x, rfl⟩
  obtain ⟨_, ht, hst⟩ := TauCeti.FiniteStratification.le_def.1 h _
    (𝒯.mem_toFiniteStratification_parts.2 ⟨⟨y, by exact ⟨x, hy.symm⟩⟩, j, rfl⟩)
  obtain ⟨-, i, rfl⟩ := 𝒮.mem_toFiniteStratification_parts.1 ht
  refine ⟨i, fun z hz ↦ ?_⟩
  obtain ⟨w, rfl⟩ : z ∈ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact 𝒯.range_subset j hz
  exact hst (a := w) hz

/-- `𝒯` refines `𝒮` if and only if every nonempty piece of `𝒯` lies in a piece of `𝒮`. -/
lemma refines_iff_range_subset {𝒮 𝒯 : ConstructibleStratification X U} :
    𝒯.Refines 𝒮 ↔ ∀ j, (Set.range (𝒯.hom j)).Nonempty →
      ∃ i, Set.range (𝒯.hom j) ⊆ Set.range (𝒮.hom i) := by
  refine ⟨fun h ↦ h.exists_range_subset, fun h ↦ TauCeti.FiniteStratification.le_def.2 ?_⟩
  intro s hs
  obtain ⟨⟨y, hy⟩, j, rfl⟩ := 𝒯.mem_toFiniteStratification_parts.1 hs
  obtain ⟨i, hi⟩ := h j ⟨_, hy⟩
  exact ⟨_, 𝒮.mem_toFiniteStratification_parts.2 ⟨⟨y, hi hy⟩, i, rfl⟩,
    Set.preimage_mono hi⟩

@[refl]
lemma Refines.refl : 𝒮.Refines 𝒮 :=
  le_rfl

lemma Refines.trans {𝒮₁ 𝒮₂ 𝒮₃ : ConstructibleStratification X U} (h₁₂ : 𝒮₁.Refines 𝒮₂)
    (h₂₃ : 𝒮₂.Refines 𝒮₃) : 𝒮₁.Refines 𝒮₃ :=
  le_trans h₁₂ h₂₃

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
/-- The single piece of `single U` is the open immersion of `U`. -/
lemma single_hom (i : (single U).ι) : (single U).hom i = U.ι :=
  rfl

variable (U) in
@[simp]
lemma range_single_hom (i : (single U).ι) : Set.range ((single U).hom i) = U :=
  Scheme.Opens.range_ι U

variable (U) in
/-- The images of the pieces of `single U` form the single-stratum stratification of `U`. -/
@[simp]
lemma toFiniteStratification_single : (single U).toFiniteStratification = ⊤ := by
  ext s
  simp only [mem_toFiniteStratification_parts, range_single_hom,
    TauCeti.FiniteStratification.mem_top_parts]
  constructor
  · rintro ⟨⟨x, -⟩, -, rfl⟩
    exact ⟨⟨x⟩, Set.eq_univ_of_forall fun y ↦ y.property⟩
  · rintro ⟨⟨x⟩, rfl⟩
    exact ⟨⟨x, trivial⟩, .unit, Set.eq_univ_of_forall fun y ↦ y.property⟩

/-- Every stratification of `U` refines the stratification with the single piece `U`. -/
lemma refines_single : 𝒮.Refines (single U) := by
  rw [Refines, toFiniteStratification_single]
  exact le_top

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

/-- The piece of the common refinement indexed by `i` is the fibre product of the pieces `i.1`
and `i.2`, mapped to `X` through the piece of `𝒮`. -/
lemma inf_hom (𝒯 : ConstructibleStratification X U) (i : 𝒮.ι × 𝒯.ι) :
    (𝒮.inf 𝒯).hom i = Limits.pullback.fst _ _ ≫ 𝒮.hom i.1 :=
  rfl

/-- The piece of the common refinement indexed by `i`, mapped to `X` through the piece of `𝒯`. -/
lemma inf_hom_eq_snd (𝒯 : ConstructibleStratification X U) (i : 𝒮.ι × 𝒯.ι) :
    (𝒮.inf 𝒯).hom i = Limits.pullback.snd _ _ ≫ 𝒯.hom i.2 :=
  Limits.pullback.condition

/-- The piece of the common refinement indexed by `i` is the fibre product of the pieces `i.1`
and `i.2` over `X`. -/
lemma isPullback_inf_hom (𝒯 : ConstructibleStratification X U) (i : 𝒮.ι × 𝒯.ι) :
    IsPullback (Limits.pullback.fst _ _ : (𝒮.inf 𝒯).obj i ⟶ 𝒮.obj i.1)
      (Limits.pullback.snd _ _) (𝒮.hom i.1) (𝒯.hom i.2) :=
  IsPullback.of_hasPullback _ _

/-- The pieces of the common refinement are the intersections of the pieces. -/
@[simp]
lemma range_inf_hom (𝒯 : ConstructibleStratification X U) (i : 𝒮.ι × 𝒯.ι) :
    Set.range ((𝒮.inf 𝒯).hom i) = Set.range (𝒮.hom i.1) ∩ Set.range (𝒯.hom i.2) :=
  Scheme.Pullback.range_fst_comp _ _

/-- The images of the pieces of the common refinement form the common refinement of the
stratifications of `U` by the images of the pieces. -/
@[simp]
lemma toFiniteStratification_inf (𝒯 : ConstructibleStratification X U) :
    (𝒮.inf 𝒯).toFiniteStratification = 𝒮.toFiniteStratification ⊓ 𝒯.toFiniteStratification := by
  ext s
  simp only [mem_toFiniteStratification_parts, TauCeti.FiniteStratification.mem_inf_parts]
  constructor
  · rintro ⟨hs, i, rfl⟩
    rw [𝒮.range_inf_hom 𝒯 i, Set.preimage_inter] at hs ⊢
    exact ⟨hs, _, ⟨hs.mono Set.inter_subset_left, i.1, rfl⟩, _,
      ⟨hs.mono Set.inter_subset_right, i.2, rfl⟩, rfl⟩
  · rintro ⟨hs, _, ⟨-, i, rfl⟩, _, ⟨-, j, rfl⟩, rfl⟩
    exact ⟨hs, (i, j), by rw [𝒮.range_inf_hom 𝒯 (i, j), Set.preimage_inter]⟩

lemma inf_refines_left (𝒯 : ConstructibleStratification X U) : (𝒮.inf 𝒯).Refines 𝒮 := by
  rw [Refines, toFiniteStratification_inf]
  exact inf_le_left

lemma inf_refines_right (𝒯 : ConstructibleStratification X U) : (𝒮.inf 𝒯).Refines 𝒯 := by
  rw [Refines, toFiniteStratification_inf]
  exact inf_le_right

/-- A stratification refining both `𝒮` and `𝒯` refines their common refinement. -/
lemma Refines.inf {𝒮 𝒯 𝒰 : ConstructibleStratification X U} (h𝒮 : 𝒰.Refines 𝒮)
    (h𝒯 : 𝒰.Refines 𝒯) : 𝒰.Refines (𝒮.inf 𝒯) := by
  rw [Refines, toFiniteStratification_inf]
  exact le_inf h𝒮 h𝒯

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

/-- The piece of the restriction to `V` indexed by `i` is the fibre product of the piece `i` with
`V`, mapped to `X` through the piece of `𝒮`. -/
lemma restrict_hom {V : X.Opens} (hVU : V ≤ U) (i : 𝒮.ι) :
    (𝒮.restrict hVU).hom i = Limits.pullback.fst _ _ ≫ 𝒮.hom i :=
  rfl

/-- The piece of the restriction to `V` indexed by `i`, mapped to `X` through `V`. -/
lemma restrict_hom_eq_snd {V : X.Opens} (hVU : V ≤ U) (i : 𝒮.ι) :
    (𝒮.restrict hVU).hom i = Limits.pullback.snd _ _ ≫ V.ι :=
  Limits.pullback.condition

/-- The piece `(𝒮.restrict hVU).obj i` of a restriction to `V`, for any `hVU : V ≤ U`, is the
fibre product of the piece `i` with `V` over `X`. -/
lemma isPullback_restrict_hom (V : X.Opens) (i : 𝒮.ι) :
    IsPullback (Limits.pullback.fst (𝒮.hom i) V.ι) (Limits.pullback.snd _ _) (𝒮.hom i) V.ι :=
  IsPullback.of_hasPullback _ _

/-- The pieces of the restriction to `V` are the intersections of the pieces with `V`. -/
@[simp]
lemma range_restrict_hom {V : X.Opens} (hVU : V ≤ U) (i : 𝒮.ι) :
    Set.range ((𝒮.restrict hVU).hom i) = Set.range (𝒮.hom i) ∩ V := by
  rw [← Scheme.Opens.range_ι V]
  exact Scheme.Pullback.range_fst_comp _ _

/-- The images of the pieces of the restriction to `V` form the pullback of the stratification of
`U` by the images of the pieces along the inclusion of `V` in `U`. -/
@[simp]
lemma toFiniteStratification_restrict {V : X.Opens} (hVU : V ≤ U) :
    (𝒮.restrict hVU).toFiniteStratification =
      𝒮.toFiniteStratification.comap (X.homOfLE hVU) (X.homOfLE hVU).continuous := by
  have h (i : (𝒮.restrict hVU).ι) : V.ι ⁻¹' Set.range ((𝒮.restrict hVU).hom i) =
      X.homOfLE hVU ⁻¹' (U.ι ⁻¹' Set.range (𝒮.hom i)) := by
    ext x
    rw [Set.mem_preimage, 𝒮.range_restrict_hom hVU i, Set.mem_preimage, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Set.mem_inter_iff, SetLike.mem_coe]
    exact and_iff_left x.property
  ext s
  simp only [mem_toFiniteStratification_parts, h, TauCeti.FiniteStratification.mem_comap_parts]
  constructor
  · rintro ⟨hs, i, rfl⟩
    exact ⟨hs, _, ⟨(hs.image _).mono (Set.image_preimage_subset _ _), i, rfl⟩, rfl⟩
  · rintro ⟨hs, _, ⟨-, i, rfl⟩, rfl⟩
    exact ⟨hs, i, rfl⟩

/-- The restriction to `V` of a refinement is a refinement of the restriction. -/
lemma Refines.restrict {𝒮 𝒯 : ConstructibleStratification X U} (h : 𝒯.Refines 𝒮)
    {V : X.Opens} (hVU : V ≤ U) : (𝒯.restrict hVU).Refines (𝒮.restrict hVU) := by
  rw [Refines, toFiniteStratification_restrict, toFiniteStratification_restrict]
  exact TauCeti.FiniteStratification.comap_mono h _ _

/-- Restriction commutes with common refinement: the two stratifications of `V` refine each
other. -/
lemma toFiniteStratification_restrict_inf (𝒯 : ConstructibleStratification X U) {V : X.Opens}
    (hVU : V ≤ U) :
    ((𝒮.inf 𝒯).restrict hVU).toFiniteStratification =
      ((𝒮.restrict hVU).inf (𝒯.restrict hVU)).toFiniteStratification := by
  simp only [toFiniteStratification_restrict, toFiniteStratification_inf,
    TauCeti.FiniteStratification.comap_inf]

/-- The restriction of `single U` to `V` and `single V` refine each other. -/
lemma toFiniteStratification_restrict_single {V : X.Opens} (hVU : V ≤ U) :
    ((single U).restrict hVU).toFiniteStratification = (single V).toFiniteStratification := by
  simp only [toFiniteStratification_restrict, toFiniteStratification_single,
    TauCeti.FiniteStratification.comap_top]

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

/-- The piece of the pullback along `f` indexed by `i` is the fibre product of the piece `i`
with `Y`, mapped to `Y` by the second projection. -/
lemma pullback_hom {Y : Scheme.{u}} (f : Y ⟶ X) (i : 𝒮.ι) :
    (𝒮.pullback f).hom i = Limits.pullback.snd _ _ :=
  rfl

/-- The piece of the pullback along `f` indexed by `i` is the base change of the piece `i`
along `f`. -/
lemma isPullback_pullback_hom {Y : Scheme.{u}} (f : Y ⟶ X) (i : 𝒮.ι) :
    IsPullback (Limits.pullback.fst _ _) ((𝒮.pullback f).hom i) (𝒮.hom i) f :=
  IsPullback.of_hasPullback _ _

/-- The pieces of the pullback along `f` are the preimages of the pieces. -/
@[simp]
lemma range_pullback_hom {Y : Scheme.{u}} (f : Y ⟶ X) (i : 𝒮.ι) :
    Set.range ((𝒮.pullback f).hom i) = f ⁻¹' Set.range (𝒮.hom i) :=
  Scheme.Pullback.range_snd _ _

/-- The images of the pieces of the pullback along `f` form the pullback of the stratification
of `U` by the images of the pieces along `f`. -/
@[simp]
lemma toFiniteStratification_pullback {Y : Scheme.{u}} (f : Y ⟶ X) :
    (𝒮.pullback f).toFiniteStratification =
      𝒮.toFiniteStratification.comap (f ∣_ U) (f ∣_ U).continuous := by
  have h (i : (𝒮.pullback f).ι) : (f ⁻¹ᵁ U).ι ⁻¹' Set.range ((𝒮.pullback f).hom i) =
      (f ∣_ U) ⁻¹' (U.ι ⁻¹' Set.range (𝒮.hom i)) := by
    ext x
    rw [Set.mem_preimage, 𝒮.range_pullback_hom f i]
    simp only [Set.mem_preimage, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  ext s
  simp only [mem_toFiniteStratification_parts, h, TauCeti.FiniteStratification.mem_comap_parts]
  constructor
  · rintro ⟨hs, i, rfl⟩
    exact ⟨hs, _, ⟨(hs.image _).mono (Set.image_preimage_subset _ _), i, rfl⟩, rfl⟩
  · rintro ⟨hs, _, ⟨-, i, rfl⟩, rfl⟩
    exact ⟨hs, i, rfl⟩

/-- The pullback of a refinement is a refinement of the pullback. -/
lemma Refines.pullback {𝒮 𝒯 : ConstructibleStratification X U} (h : 𝒯.Refines 𝒮)
    {Y : Scheme.{u}} (f : Y ⟶ X) : (𝒯.pullback f).Refines (𝒮.pullback f) := by
  rw [Refines, toFiniteStratification_pullback, toFiniteStratification_pullback]
  exact TauCeti.FiniteStratification.comap_mono h _ _

/-- Pullback commutes with common refinement: the two stratifications of `f ⁻¹ᵁ U` refine each
other. -/
lemma toFiniteStratification_pullback_inf (𝒯 : ConstructibleStratification X U)
    {Y : Scheme.{u}} (f : Y ⟶ X) :
    ((𝒮.inf 𝒯).pullback f).toFiniteStratification =
      ((𝒮.pullback f).inf (𝒯.pullback f)).toFiniteStratification := by
  simp only [toFiniteStratification_pullback, toFiniteStratification_inf,
    TauCeti.FiniteStratification.comap_inf]

/-- The pullback of `single U` along `f` and `single (f ⁻¹ᵁ U)` refine each other. -/
lemma toFiniteStratification_pullback_single {Y : Scheme.{u}} (f : Y ⟶ X) :
    ((single U).pullback f).toFiniteStratification =
      (single (f ⁻¹ᵁ U)).toFiniteStratification := by
  simp only [toFiniteStratification_pullback, toFiniteStratification_single,
    TauCeti.FiniteStratification.comap_top]

end ConstructibleStratification

end AlgebraicGeometry.Scheme
