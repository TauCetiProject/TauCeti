/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Constructible stratifications of schemes

For an open subset `U` of a scheme `X`, a *constructible stratification* of `U` is a finite family
of immersions `Z i ⟶ X` whose images are pairwise disjoint, cover `U`, and are constructible
subsets of `U` (SGA 4, Exposé IX, §2). Constructible étale sheaves are the sheaves which,
on every affine open, become locally constant of finite type on the strata of such a
stratification.

This file provides the stratifications themselves and the operations on them needed to show that
such a condition is stable under pullback and can be checked locally on a quasi-compact
quasi-separated open:

* `AlgebraicGeometry.Scheme.ConstructibleStratification`: the structure of a constructible
  stratification of an open `U`.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.single`: the stratification of `U` by the
  single stratum `U`.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.pullback`: the pullback of a stratification
  of `U ⊆ X` along `g : Y ⟶ X`, a stratification of `g ⁻¹ᵁ U`.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.restrict`: the restriction of a
  stratification of `U` to an open `V ≤ U`.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.map`: the image of a stratification under
  an open immersion.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.exists_of_iSup_eq`: stratifications of the
  members of a finite cover of `U` by retrocompact opens glue to a stratification of `U` each of
  whose strata factors through a stratum of one of the given stratifications.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Section 59.71, Constructible sheaves.
-/

public section

universe u

open CategoryTheory Limits Topology Set.Notation

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- A *constructible stratification* of an open `U` of a scheme `X`: a finite family of immersions
`f i : Z i ⟶ X` with pairwise disjoint images covering `U`, each image a constructible subset of
`U`. -/
structure ConstructibleStratification (X : Scheme.{u}) (U : X.Opens) where
  /-- The index type of the strata. -/
  ι : Type
  [finite : Finite ι]
  /-- The strata. -/
  Z : ι → Scheme.{u}
  /-- The immersion of each stratum into `X`. -/
  f (i : ι) : Z i ⟶ X
  [isImmersion (i : ι) : IsImmersion (f i)]
  /-- The images of distinct strata are disjoint. -/
  pairwise_disjoint_range : Pairwise fun i j ↦ Disjoint (Set.range (f i)) (Set.range (f j))
  /-- The images of the strata cover `U`. -/
  iUnion_range : ⋃ i, Set.range (f i) = U
  /-- The image of each stratum is a constructible subset of `U`. -/
  isConstructible_range (i : ι) : IsConstructible ((U : Set X) ↓∩ Set.range (f i))

namespace ConstructibleStratification

attribute [instance] finite isImmersion

variable {U : X.Opens} (S : X.ConstructibleStratification U)

lemma range_subset (i : S.ι) : Set.range (S.f i) ⊆ U :=
  S.iUnion_range ▸ Set.subset_iUnion (fun i ↦ Set.range (S.f i)) i

/-- The stratification of an open `U` by the single stratum `U`. -/
@[expose, simps Z f]
noncomputable def single (U : X.Opens) : X.ConstructibleStratification U where
  ι := Unit
  Z _ := U
  f _ := U.ι
  pairwise_disjoint_range i j h := (h (Subsingleton.elim i j)).elim
  iUnion_range := by simp only [Opens.range_ι, Set.iUnion_const]
  isConstructible_range _ := by simp only [Opens.range_ι, Subtype.coe_preimage_self,
    IsConstructible.univ]

/-- The pullback of a constructible stratification of `U` along `g : Y ⟶ X`: its strata are the
fibre products `Z i ×_X Y`, immersed into `Y` by the second projection. -/
@[expose, simps Z f]
noncomputable def pullback (g : Y ⟶ X) : Y.ConstructibleStratification (g ⁻¹ᵁ U) where
  ι := S.ι
  Z i := Limits.pullback (S.f i) g
  f i := Limits.pullback.snd (S.f i) g
  pairwise_disjoint_range i j h := by
    simpa only [Pullback.range_snd] using (S.pairwise_disjoint_range h).preimage g
  iUnion_range := by
    simp only [Pullback.range_snd, ← Set.preimage_iUnion, S.iUnion_range]
    rfl
  isConstructible_range i := by
    have heq : (g ⁻¹ᵁ U : Set Y) ↓∩ Set.range (Limits.pullback.snd (S.f i) g) =
        (g ∣_ U) ⁻¹' ((U : Set X) ↓∩ Set.range (S.f i)) := by
      ext x
      simp only [Pullback.range_snd, Set.mem_preimage, morphismRestrict_base]
      rfl
    rw [heq]
    exact (g ∣_ U).isConstructible_preimage (S.isConstructible_range i)

/-- The restriction of a constructible stratification of `U` to an open `V ≤ U`: its strata are
the fibre products `Z i ×_X V`. -/
@[expose, simps Z f]
noncomputable def restrict {V : X.Opens} (hVU : V ≤ U) : X.ConstructibleStratification V where
  ι := S.ι
  Z i := Limits.pullback (S.f i) V.ι
  f i := Limits.pullback.fst (S.f i) V.ι ≫ S.f i
  pairwise_disjoint_range i j h := by
    simp only [Pullback.range_fst_comp]
    exact (S.pairwise_disjoint_range h).mono Set.inter_subset_left Set.inter_subset_left
  iUnion_range := by
    simp only [Pullback.range_fst_comp, Opens.range_ι, ← Set.iUnion_inter, S.iUnion_range]
    exact Set.inter_eq_right.mpr hVU
  isConstructible_range i := by
    convert (S.isConstructible_range i).preimage_of_isOpenEmbedding
      (IsOpenEmbedding.inclusion hVU (V.isOpen.preimage continuous_subtypeVal)) using 1
    ext x
    simp only [Set.mem_preimage, Pullback.range_fst_comp, Opens.range_ι, Set.mem_inter_iff,
      x.property, and_true]

/-- The image of a constructible stratification of an open `W` of `Y` under an open immersion
`j : Y ⟶ X`: the same strata, immersed into `X` through `j`, stratify `j ''ᵁ W`. -/
@[expose, simps Z f]
noncomputable def map {W : Y.Opens} (S : Y.ConstructibleStratification W) (j : Y ⟶ X)
    [IsOpenImmersion j] : X.ConstructibleStratification (j ''ᵁ W) where
  ι := S.ι
  Z := S.Z
  f i := S.f i ≫ j
  pairwise_disjoint_range i i' h := by
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (Set.disjoint_image_iff j.isOpenEmbedding.injective).mpr (S.pairwise_disjoint_range h)
  iUnion_range := by
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← Set.image_iUnion,
      S.iUnion_range, Scheme.Hom.coe_image]
  isConstructible_range i := by
    -- Transport along the homeomorphism `W ≃ j '' W` induced by `j`.
    have H : Set.MapsTo j (W : Set Y) (j ''ᵁ W : Set X) := Set.mapsTo_image _ _
    have hrange : IsRetrocompact (Set.range H.restrict) := by
      rw [Set.MapsTo.range_restrict, Scheme.Hom.coe_image, Subtype.coe_preimage_self]
      exact IsRetrocompact.univ
    convert (S.isConstructible_range i).image_of_isOpenEmbedding
      (j.isOpenEmbedding.restrict H W.isOpen) hrange using 1
    ext x
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.mem_preimage]
    refine ⟨fun ⟨y, hy, hyx⟩ ↦ ⟨⟨y, S.range_subset i hy⟩, hy, Subtype.ext hyx⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    exact ⟨y.val, hy, rfl⟩

section Glue

/-! ### Gluing along a finite enumerated cover

For opens `V m` indexed by `Fin n` with stratifications `S m`, the glued strata are the parts of
the strata of `S m` lying outside the earlier members `V l`, `l < m`, with their reduced closed
subscheme structures. -/

variable {n : ℕ} {V : Fin n → X.Opens} (S : ∀ m, X.ConstructibleStratification (V m))

/-- The union of the members of the cover preceding the `m`-th. -/
private def before (V : Fin n → X.Opens) (m : Fin n) : Set X := ⋃ l < m, (V l : Set X)

private lemma isOpen_before (m : Fin n) : IsOpen (before V m) :=
  isOpen_iUnion fun l ↦ isOpen_iUnion fun _ ↦ (V l).isOpen

/-- The closed subset of the stratum `(S m).Z i` lying outside the earlier members of the cover. -/
private def outside (p : Σ m, (S m).ι) : TopologicalSpace.Closeds ((S p.1).Z p.2) :=
  ⟨(S p.1).f p.2 ⁻¹' (before V p.1)ᶜ,
    (isOpen_before p.1).isClosed_compl.preimage ((S p.1).f p.2).continuous⟩

/-- The immersion of the reduced closed subscheme on `outside S p` into `X`. -/
private noncomputable def glueι (p : Σ m, (S m).ι) :
    (IdealSheafData.vanishingIdeal (outside S p)).subscheme ⟶ X :=
  (IdealSheafData.vanishingIdeal (outside S p)).subschemeι ≫ (S p.1).f p.2

private instance (p : Σ m, (S m).ι) : IsImmersion (glueι S p) := by
  unfold glueι
  infer_instance

private lemma range_glueι (p : Σ m, (S m).ι) :
    Set.range (glueι S p) = Set.range ((S p.1).f p.2) \ before V p.1 := by
  have h : ⇑(glueι S p) =
      (S p.1).f p.2 ∘ (IdealSheafData.vanishingIdeal (outside S p)).subschemeι :=
    funext fun _ ↦ Scheme.Hom.comp_apply _ _ _
  rw [h, Set.range_comp, IdealSheafData.range_subschemeι,
    IdealSheafData.coe_support_vanishingIdeal, outside, TopologicalSpace.Closeds.coe_mk,
    Set.preimage_compl]
  exact Set.image_compl_preimage

/-- Strata over the same member are disjoint by assumption; a stratum over a later member avoids
the earlier members. -/
private lemma pairwise_disjoint_range_glueι :
    Pairwise fun p q ↦ Disjoint (Set.range (glueι S p)) (Set.range (glueι S q)) := by
  rintro ⟨m, i⟩ ⟨m', i'⟩ hp
  simp only [range_glueι]
  rcases lt_trichotomy m m' with hm | rfl | hm
  · exact Set.disjoint_left.mpr fun x hx hx' ↦
      hx'.2 (Set.mem_iUnion₂.mpr ⟨m, hm, (S m).range_subset i hx.1⟩)
  · have hi : i ≠ i' := fun h ↦ hp (h ▸ rfl)
    exact ((S m).pairwise_disjoint_range hi).mono Set.sdiff_subset Set.sdiff_subset
  · exact Set.disjoint_left.mpr fun x hx hx' ↦
      hx.2 (Set.mem_iUnion₂.mpr ⟨m', hm, (S m').range_subset i' hx'.1⟩)

/-- A point of `U` lies in a stratum over the first member of the cover containing it. -/
private lemma iUnion_range_glueι (hVU : ⨆ m, V m = U) :
    ⋃ p, Set.range (glueι S p) = U := by
  refine subset_antisymm (Set.iUnion_subset fun p ↦ ?_) fun x hx ↦ ?_
  · rw [range_glueι]
    exact Set.sdiff_subset.trans (((S p.1).range_subset p.2).trans (hVU ▸ le_iSup V p.1))
  · rw [← hVU, TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at hx
    obtain ⟨m, hm, hmin⟩ := WellFounded.has_min wellFounded_lt {m | x ∈ V m} hx
    have hm' : x ∈ (V m : Set X) := hm
    rw [← (S m).iUnion_range, Set.mem_iUnion] at hm'
    obtain ⟨i, hi⟩ := hm'
    refine Set.mem_iUnion.mpr ⟨⟨m, i⟩, ?_⟩
    rw [range_glueι]
    refine ⟨hi, fun hxW ↦ ?_⟩
    obtain ⟨l, hl, hxl⟩ := Set.mem_iUnion₂.mp hxW
    exact hmin l hxl hl

/-- The trace on `U` of each glued stratum is constructible: the trace of the stratum of `S m` is
the image of a constructible subset of the retrocompact open `V m`, and the trace of the earlier
members is a finite union of retrocompact opens. -/
private lemma isConstructible_range_glueι (hVU : ⨆ m, V m = U)
    (hV : ∀ m, IsRetrocompact ((U : Set X) ↓∩ (V m : Set X))) (p : Σ m, (S m).ι) :
    IsConstructible ((U : Set X) ↓∩ Set.range (glueι S p)) := by
  obtain ⟨m, i⟩ := p
  have hVmU : V m ≤ U := hVU ▸ le_iSup V m
  rw [range_glueι, Set.preimage_sdiff]
  have hR : IsConstructible ((U : Set X) ↓∩ Set.range ((S m).f i)) := by
    have hrange : Set.range (Set.inclusion hVmU) = (U : Set X) ↓∩ (V m : Set X) := by
      ext x
      exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
    convert ((S m).isConstructible_range i).image_of_isOpenEmbedding
      (IsOpenEmbedding.inclusion hVmU ((V m).isOpen.preimage continuous_subtypeVal))
      (hrange ▸ hV m) using 1
    ext x
    refine ⟨fun hx ↦ ⟨⟨x, (S m).range_subset i hx⟩, hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    exact hy
  refine hR.sdiff (IsRetrocompact.isConstructible ((isOpen_before m).preimage
    continuous_subtypeVal) ?_)
  simp only [before, Set.preimage_iUnion]
  exact IsRetrocompact.iUnion fun l ↦ IsRetrocompact.iUnion fun _ ↦ hV l

end Glue

/-- Constructible stratifications of the members `V k` of a finite cover of `U` by opens whose
traces on `U` are retrocompact glue to a constructible stratification of `U`, each of whose strata
factors through a stratum of one of the given stratifications. For a chosen enumeration of the
cover, the strata of the glued stratification are the reduced closed subschemes of the strata of
`S k` lying outside the earlier members of the cover. -/
theorem exists_of_iSup_eq {κ : Type*} [Finite κ] {V : κ → X.Opens} (hVU : ⨆ k, V k = U)
    (hV : ∀ k, IsRetrocompact ((U : Set X) ↓∩ (V k : Set X)))
    (S : ∀ k, X.ConstructibleStratification (V k)) :
    ∃ T : X.ConstructibleStratification U, ∀ j, ∃ (k : κ) (i : (S k).ι)
      (h : T.Z j ⟶ (S k).Z i), h ≫ (S k).f i = T.f j := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  have hVU' : ⨆ m, V (e.symm m) = U := (e.symm.iSup_comp (g := V)).trans hVU
  exact ⟨{
    ι := Σ m : Fin n, (S (e.symm m)).ι
    Z p := (IdealSheafData.vanishingIdeal (outside (fun m ↦ S (e.symm m)) p)).subscheme
    f := glueι fun m ↦ S (e.symm m)
    pairwise_disjoint_range := pairwise_disjoint_range_glueι _
    iUnion_range := iUnion_range_glueι _ hVU'
    isConstructible_range := isConstructible_range_glueι _ hVU' fun m ↦ hV (e.symm m) },
    fun p ↦ ⟨e.symm p.1, p.2, _, rfl⟩⟩

end ConstructibleStratification

end AlgebraicGeometry.Scheme
