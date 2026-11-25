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
public import TauCeti.Topology.Stratification

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
* `AlgebraicGeometry.Scheme.ConstructibleStratification.range_f_single`, `range_f_pullback`,
  `range_f_restrict` and `range_f_map`: the images of the strata of these stratifications.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.Factors` and
  `AlgebraicGeometry.Scheme.ConstructibleStratification.Refines`: a morphism factoring through a
  stratum, and a stratification each of whose strata factors through a stratum of another one;
  `restrict_refines` says that restriction refines.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.exists_of_iSup_eq`: stratifications of the
  members of a finite cover of `U` by retrocompact opens glue to a stratification of `U` each of
  whose strata factors through a stratum of one of the given stratifications.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.existsUnique_mem_range`: every point of `U`
  lies in exactly one stratum.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.inf`: the common refinement of two
  stratifications of `U`, whose strata are the fibre products of their strata; `inf_refines_left`,
  `inf_refines_right` and `Refines.inf` say that it is their greatest common refinement, and
  `Refines.pullback` says that pullback preserves refinement.
* `AlgebraicGeometry.Scheme.ConstructibleStratification.toFiniteStratification`: the finite locally
  closed stratification of `U` by the nonempty images of the strata, which sends `single` to `⊤`,
  `inf` to `⊓`, `restrict` and `pullback` to `TauCeti.FiniteStratification.comap`, and refinement
  to the order (`Refines.toFiniteStratification_le`).

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

/-- A point of `X` lies in some stratum of a stratification of `U` if and only if it lies in `U`. -/
lemma exists_mem_range_iff {x : X} : (∃ i, x ∈ Set.range (S.f i)) ↔ x ∈ U := by
  rw [← SetLike.mem_coe, ← S.iUnion_range, Set.mem_iUnion]

/-- Every point of `U` lies in exactly one stratum of a stratification of `U`. -/
lemma existsUnique_mem_range {x : X} (hx : x ∈ U) : ∃! i, x ∈ Set.range (S.f i) := by
  simpa only [Set.mem_univ, true_and] using pairwiseDisjoint_unique
    (f := fun i ↦ Set.range (S.f i)) (S.pairwise_disjoint_range.set_pairwise Set.univ)
    (by simpa only [Set.mem_univ, Set.iUnion_true, S.iUnion_range, SetLike.mem_coe] using hx)

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
    simp only [Pullback.range_snd, ← Set.preimage_iUnion, S.iUnion_range, Scheme.Hom.coe_preimage]
  isConstructible_range i := by
    have heq : (g ⁻¹ᵁ U : Set Y) ↓∩ Set.range (Limits.pullback.snd (S.f i) g) =
        (g ∣_ U) ⁻¹' ((U : Set X) ↓∩ Set.range (S.f i)) := by
      ext x
      simp only [Pullback.range_snd, Set.mem_preimage, morphismRestrict_base]
      -- Both sides say that `g x` lies in the image of the stratum: `Set.restrictPreimage`
      -- applies `g` to the underlying point, and `g ⁻¹ᵁ U` has `g ⁻¹' U` as its carrier.
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
    have hrange : Set.range H.restrict = Set.univ := by
      rw [Set.MapsTo.range_restrict, Scheme.Hom.coe_image, Subtype.coe_preimage_self]
    refine (isConstructible_preimage_iff_of_isOpenEmbedding (j.isOpenEmbedding.restrict H W.isOpen)
      (hrange ▸ IsRetrocompact.univ) (hrange ▸ Set.subset_univ _)).mp ?_
    convert S.isConstructible_range i using 1
    ext x
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.mem_preimage,
      Set.MapsTo.val_restrict_apply, j.isOpenEmbedding.injective.mem_set_image]

/-! ### Images of the strata -/

/-- The single stratum of `single U` has image `U`. -/
lemma range_f_single (U : X.Opens) (i : (single U).ι) : Set.range ((single U).f i) = U :=
  U.range_ι

/-- The strata of `S.pullback g` have the preimages under `g` of the strata of `S` as images. -/
lemma range_f_pullback (g : Y ⟶ X) (i : S.ι) :
    Set.range ((S.pullback g).f i) = g ⁻¹' Set.range (S.f i) :=
  Pullback.range_snd (S.f i) g

/-- The strata of `S.restrict hVU` have the traces on `V` of the strata of `S` as images. -/
lemma range_f_restrict {V : X.Opens} (hVU : V ≤ U) (i : S.ι) :
    Set.range ((S.restrict hVU).f i) = Set.range (S.f i) ∩ V :=
  (Pullback.range_fst_comp (S.f i) V.ι).trans (congrArg _ V.range_ι)

/-- The strata of `S.map j` have the images under `j` of the strata of `S` as images. -/
lemma range_f_map {W : Y.Opens} (S : Y.ConstructibleStratification W) (j : Y ⟶ X)
    [IsOpenImmersion j] (i : S.ι) : Set.range ((S.map j).f i) = j '' Set.range (S.f i) :=
  Set.range_comp (⇑j) (⇑(S.f i))

/-! ### Refinement -/

/-- A morphism `g : Z ⟶ X` *factors through* a constructible stratification `S` when it factors
through the immersion of one of its strata. -/
def Factors {Z : Scheme.{u}} (g : Z ⟶ X) : Prop :=
  ∃ (i : S.ι) (h : Z ⟶ S.Z i), h ≫ S.f i = g

variable {S} in
lemma factors_iff {Z : Scheme.{u}} {g : Z ⟶ X} :
    S.Factors g ↔ ∃ (i : S.ι) (h : Z ⟶ S.Z i), h ≫ S.f i = g :=
  Iff.rfl

/-- A constructible stratification `T` of `V` *refines* a constructible stratification `S` of `U`
when every stratum of `T` factors through a stratum of `S`. -/
def Refines {V : X.Opens} (T : X.ConstructibleStratification V)
    (S : X.ConstructibleStratification U) : Prop :=
  ∀ j, S.Factors (T.f j)

variable {S} in
lemma refines_iff {V : X.Opens} {T : X.ConstructibleStratification V} :
    T.Refines S ↔ ∀ j, S.Factors (T.f j) :=
  Iff.rfl

/-- The restriction of `S` to an open `V ≤ U` refines `S`. -/
lemma restrict_refines {V : X.Opens} (hVU : V ≤ U) : (S.restrict hVU).Refines S :=
  fun i ↦ ⟨i, Limits.pullback.fst _ _, rfl⟩

/-- The pullback along `g` of a refinement is a refinement of the pullback. -/
lemma Refines.pullback {V : X.Opens} {T : X.ConstructibleStratification V} (h : T.Refines S)
    (g : Y ⟶ X) : (T.pullback g).Refines (S.pullback g) := by
  intro j
  obtain ⟨i, a, ha⟩ := h j
  exact ⟨i, Limits.pullback.map _ _ _ _ a (𝟙 Y) (𝟙 X) (by simp [ha]) (by simp),
    (Limits.pullback.lift_snd _ _ _).trans (Category.comp_id _)⟩

/-! ### Common refinement -/

/-- The common refinement of two constructible stratifications of `U`: its strata are the fibre
products over `X` of the strata of the two, whose images are the intersections of their images. -/
@[expose, simps Z f]
noncomputable def inf (T : X.ConstructibleStratification U) : X.ConstructibleStratification U where
  ι := S.ι × T.ι
  Z p := Limits.pullback (S.f p.1) (T.f p.2)
  f p := Limits.pullback.fst _ _ ≫ S.f p.1
  pairwise_disjoint_range := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [Pullback.range_fst_comp]
    by_cases hi : i = i'
    · subst hi
      have hj : j ≠ j' := fun hj ↦ h (by rw [hj])
      exact (T.pairwise_disjoint_range hj).mono Set.inter_subset_right Set.inter_subset_right
    · exact (S.pairwise_disjoint_range hi).mono Set.inter_subset_left Set.inter_subset_left
  iUnion_range := by
    simp only [Pullback.range_fst_comp, Set.iUnion_prod']
    rw [← Set.iUnion_inter_iUnion (fun i ↦ Set.range (S.f i)) fun j ↦ Set.range (T.f j),
      S.iUnion_range, T.iUnion_range, Set.inter_self]
  isConstructible_range p := by
    simp only [Pullback.range_fst_comp, Set.preimage_inter]
    exact (S.isConstructible_range p.1).inter (T.isConstructible_range p.2)

/-- The strata of the common refinement also map to `X` through the strata of `T`. -/
lemma inf_f_eq_snd (T : X.ConstructibleStratification U) (p : S.ι × T.ι) :
    (S.inf T).f p = Limits.pullback.snd _ _ ≫ T.f p.2 :=
  Limits.pullback.condition

/-- The strata of `S.inf T` have the intersections of the strata of `S` and `T` as images. -/
lemma range_f_inf (T : X.ConstructibleStratification U) (p : S.ι × T.ι) :
    Set.range ((S.inf T).f p) = Set.range (S.f p.1) ∩ Set.range (T.f p.2) :=
  Pullback.range_fst_comp _ _

lemma inf_refines_left (T : X.ConstructibleStratification U) : (S.inf T).Refines S :=
  fun p ↦ ⟨p.1, Limits.pullback.fst _ _, rfl⟩

lemma inf_refines_right (T : X.ConstructibleStratification U) : (S.inf T).Refines T :=
  fun p ↦ ⟨p.2, Limits.pullback.snd _ _, (S.inf_f_eq_snd T p).symm⟩

/-- A stratification refining both `S` and `T` refines their common refinement. -/
lemma Refines.inf {V : X.Opens} {T : X.ConstructibleStratification U}
    {R : X.ConstructibleStratification V} (hS : R.Refines S) (hT : R.Refines T) :
    R.Refines (S.inf T) := by
  intro j
  obtain ⟨i, a, ha⟩ := hS j
  obtain ⟨i', b, hb⟩ := hT j
  exact ⟨(i, i'), Limits.pullback.lift a b (ha.trans hb.symm),
    (Limits.pullback.lift_fst_assoc _ _ _ _).trans ha⟩

/-! ### The stratification by the images of the strata -/

/-- The finite locally closed stratification of `U` whose strata are the nonempty images of the
strata of `S`. -/
noncomputable def toFiniteStratification : TauCeti.FiniteStratification U :=
  TauCeti.FiniteStratification.ofErase
    (Set.finite_range fun i ↦ U.ι ⁻¹' Set.range (S.f i)).toFinset
    (by
      rw [Set.Finite.coe_toFinset]
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
      exact (S.pairwise_disjoint_range fun h ↦ hij (by rw [h])).preimage _)
    (by
      rw [Set.Finite.coe_toFinset, Set.sUnion_range, ← Set.preimage_iUnion, S.iUnion_range,
        ← Scheme.Opens.range_ι, Set.preimage_range])
    (by
      simp only [Set.Finite.mem_toFinset, Set.forall_mem_range]
      exact fun i ↦ (S.f i).isLocallyClosed_range.preimage U.ι.continuous)

/-- The strata of `S.toFiniteStratification` are the nonempty images of the strata of `S`. -/
@[simp]
lemma mem_toFiniteStratification_parts {s : Set U} :
    s ∈ S.toFiniteStratification.parts ↔ s.Nonempty ∧ ∃ i, U.ι ⁻¹' Set.range (S.f i) = s := by
  simp [toFiniteStratification]

/-- A refinement gives a finer stratification of `U` by the images of the strata. -/
lemma Refines.toFiniteStratification_le {T : X.ConstructibleStratification U} (h : T.Refines S) :
    T.toFiniteStratification ≤ S.toFiniteStratification := by
  refine TauCeti.FiniteStratification.le_def.2 fun s hs ↦ ?_
  obtain ⟨hs, j, rfl⟩ := T.mem_toFiniteStratification_parts.1 hs
  obtain ⟨i, a, ha⟩ := h j
  have hji : Set.range (T.f j) ⊆ Set.range (S.f i) := by
    rw [← ha]
    exact Set.range_comp_subset_range ⇑a ⇑(S.f i)
  exact ⟨_, S.mem_toFiniteStratification_parts.2 ⟨hs.mono (Set.preimage_mono hji), i, rfl⟩,
    Set.preimage_mono hji⟩

/-- The images of the strata of `single U` form the single-stratum stratification of `U`. -/
@[simp]
lemma toFiniteStratification_single (U : X.Opens) : (single U).toFiniteStratification = ⊤ := by
  ext s
  simp only [mem_toFiniteStratification_parts, range_f_single,
    TauCeti.FiniteStratification.mem_top_parts]
  constructor
  · rintro ⟨⟨x, -⟩, -, rfl⟩
    exact ⟨⟨x⟩, Set.eq_univ_of_forall fun y ↦ y.property⟩
  · rintro ⟨⟨x⟩, rfl⟩
    exact ⟨⟨x, trivial⟩, (), Set.eq_univ_of_forall fun y ↦ y.property⟩

/-- The images of the strata of the common refinement form the common refinement of the
stratifications of `U` by the images of the strata. -/
@[simp]
lemma toFiniteStratification_inf (T : X.ConstructibleStratification U) :
    (S.inf T).toFiniteStratification = S.toFiniteStratification ⊓ T.toFiniteStratification := by
  ext s
  simp only [mem_toFiniteStratification_parts, TauCeti.FiniteStratification.mem_inf_parts]
  constructor
  · rintro ⟨hs, p, rfl⟩
    rw [S.range_f_inf T p, Set.preimage_inter] at hs ⊢
    exact ⟨hs, _, ⟨hs.mono Set.inter_subset_left, p.1, rfl⟩, _,
      ⟨hs.mono Set.inter_subset_right, p.2, rfl⟩, rfl⟩
  · rintro ⟨hs, _, ⟨-, i, rfl⟩, _, ⟨-, j, rfl⟩, rfl⟩
    exact ⟨hs, (i, j), by rw [S.range_f_inf T (i, j), Set.preimage_inter]⟩

/-- If the images of the strata of a stratification `T` of an open `V` of `Y` are the preimages
under a morphism `φ : V ⟶ U` of the images of the strata of `S`, then the stratification of `V` by
the images of the strata of `T` is the pullback along `φ` of that of `S`. -/
lemma toFiniteStratification_eq_comap {V : Y.Opens} (T : Y.ConstructibleStratification V)
    (φ : (V : Scheme) ⟶ U)
    (h : Set.range (fun j ↦ V.ι ⁻¹' Set.range (T.f j)) =
      Set.range (fun i ↦ φ ⁻¹' (U.ι ⁻¹' Set.range (S.f i)))) :
    T.toFiniteStratification = S.toFiniteStratification.comap φ φ.continuous := by
  ext s
  simp only [mem_toFiniteStratification_parts, TauCeti.FiniteStratification.mem_comap_parts]
  constructor
  · rintro ⟨hs, j, rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, φ ⁻¹' (U.ι ⁻¹' Set.range (S.f i)) = V.ι ⁻¹' Set.range (T.f j) :=
      h.subset ⟨j, rfl⟩
    rw [← hi] at hs ⊢
    exact ⟨hs, _, ⟨Set.nonempty_of_nonempty_preimage hs, i, rfl⟩, rfl⟩
  · rintro ⟨hs, _, ⟨-, i, rfl⟩, rfl⟩
    exact ⟨hs, h.superset ⟨i, rfl⟩⟩

/-- The images of the strata of the restriction to `V` form the pullback of the stratification of
`U` by the images of the strata along the inclusion of `V` in `U`. -/
@[simp]
lemma toFiniteStratification_restrict {V : X.Opens} (hVU : V ≤ U) :
    (S.restrict hVU).toFiniteStratification =
      S.toFiniteStratification.comap (X.homOfLE hVU) (X.homOfLE hVU).continuous := by
  have h (i : (S.restrict hVU).ι) : V.ι ⁻¹' Set.range ((S.restrict hVU).f i) =
      X.homOfLE hVU ⁻¹' (U.ι ⁻¹' Set.range (S.f i)) := by
    ext x
    simp only [Set.mem_preimage, S.range_f_restrict hVU i, ← Scheme.Hom.comp_apply,
      Scheme.homOfLE_ι, Set.mem_inter_iff]
    exact and_iff_left x.property
  exact S.toFiniteStratification_eq_comap _ _ (congrArg Set.range (funext h))

/-- The images of the strata of the pullback along `g` form the pullback of the stratification of
`U` by the images of the strata along `g`. -/
@[simp]
lemma toFiniteStratification_pullback (g : Y ⟶ X) :
    (S.pullback g).toFiniteStratification =
      S.toFiniteStratification.comap (g ∣_ U) (g ∣_ U).continuous := by
  have h (i : (S.pullback g).ι) : (g ⁻¹ᵁ U).ι ⁻¹' Set.range ((S.pullback g).f i) =
      (g ∣_ U) ⁻¹' (U.ι ⁻¹' Set.range (S.f i)) := by
    ext x
    rw [Set.mem_preimage, S.range_f_pullback g i]
    simp only [Set.mem_preimage, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  exact S.toFiniteStratification_eq_comap _ _ (congrArg Set.range (funext h))

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
  have hrange : Set.range (Set.inclusion hVmU) = (U : Set X) ↓∩ (V m : Set X) :=
    Set.range_inclusion hVmU
  have hR : IsConstructible ((U : Set X) ↓∩ Set.range ((S m).f i)) :=
    (isConstructible_preimage_iff_of_isOpenEmbedding
      (IsOpenEmbedding.inclusion hVmU ((V m).isOpen.preimage continuous_subtypeVal))
      (hrange ▸ hV m) (hrange ▸ fun _ hx ↦ (S m).range_subset i hx)).mp
      ((S m).isConstructible_range i)
  refine hR.sdiff (IsRetrocompact.isConstructible ((isOpen_before m).preimage
    continuous_subtypeVal) ?_)
  simp only [before, Set.preimage_iUnion]
  exact IsRetrocompact.iUnion fun l ↦ IsRetrocompact.iUnion fun _ ↦ hV l

end Glue

/-- Constructible stratifications of the members `V k` of a finite cover of `U` by opens whose
traces on `U` are retrocompact glue to a constructible stratification of `U`, each of whose strata
factors through a stratum of one of the given stratifications. -/
theorem exists_of_iSup_eq {κ : Type*} [Finite κ] {V : κ → X.Opens} (hVU : ⨆ k, V k = U)
    (hV : ∀ k, IsRetrocompact ((U : Set X) ↓∩ (V k : Set X)))
    (S : ∀ k, X.ConstructibleStratification (V k)) :
    ∃ T : X.ConstructibleStratification U, ∀ j, ∃ k, (S k).Factors (T.f j) := by
  -- For a chosen enumeration of the cover, the strata of the glued stratification are the reduced
  -- closed subschemes of the strata of `S k` lying outside the earlier members of the cover.
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
