/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.IdealSheaf.Functor
public import TauCeti.CategoryTheory.Comma.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The Hilbert functor of points

The degree-`d` Hilbert functor of `X ⟶ S` parametrizes closed subschemes of `T ×_S X`
finite locally free of degree `d` over `T`. It is a subfunctor of the native functor of ideal
sheaves on base changes, so its restrictions use the same pullback of closed subschemes.

## References

* The Stacks Project, [Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- The closed subscheme cut out by an ideal sheaf is finite locally free of degree `d`
over the base. Finite presentation follows from the constant-rank condition. -/
def IsFiniteLocallyFreeOfDegree (I : X.IdealSheafData) (f : X ⟶ S) (d : ℕ) : Prop :=
  IsFinite (I.subschemeι ≫ f) ∧ Flat (I.subschemeι ≫ f) ∧
    (I.subschemeι ≫ f).finrank = fun _ ↦ d

/-- The characteristic conditions of a finite locally free closed family of degree `d`. -/
theorem isFiniteLocallyFreeOfDegree_iff {I : X.IdealSheafData} {f : X ⟶ S} {d : ℕ} :
    I.IsFiniteLocallyFreeOfDegree f d ↔
      IsFinite (I.subschemeι ≫ f) ∧ Flat (I.subschemeι ≫ f) ∧
        (I.subschemeι ≫ f).finrank = fun _ ↦ d :=
  (Iff.rfl)

/-- A finite locally free closed family has finite projection. -/
theorem IsFiniteLocallyFreeOfDegree.isFinite {I : X.IdealSheafData} {f : X ⟶ S} {d : ℕ}
    (hI : I.IsFiniteLocallyFreeOfDegree f d) : IsFinite (I.subschemeι ≫ f) :=
  (isFiniteLocallyFreeOfDegree_iff.mp hI).1

/-- A finite locally free closed family has flat projection. -/
theorem IsFiniteLocallyFreeOfDegree.flat {I : X.IdealSheafData} {f : X ⟶ S} {d : ℕ}
    (hI : I.IsFiniteLocallyFreeOfDegree f d) : Flat (I.subschemeι ≫ f) :=
  (isFiniteLocallyFreeOfDegree_iff.mp hI).2.1

/-- A finite locally free closed family has the prescribed degree at every base point. -/
theorem IsFiniteLocallyFreeOfDegree.finrank {I : X.IdealSheafData} {f : X ⟶ S} {d : ℕ}
    (hI : I.IsFiniteLocallyFreeOfDegree f d) (s : S) : (I.subschemeι ≫ f).finrank s = d :=
  congrFun (isFiniteLocallyFreeOfDegree_iff.mp hI).2.2 s

/-- A finite locally free closed family is locally of finite presentation over the base. -/
theorem IsFiniteLocallyFreeOfDegree.locallyOfFinitePresentation
    {I : X.IdealSheafData} {f : X ⟶ S} {d : ℕ} (hI : I.IsFiniteLocallyFreeOfDegree f d) :
    LocallyOfFinitePresentation (I.subschemeι ≫ f) := by
  have := hI.isFinite
  have := hI.flat
  exact Scheme.Hom.locallyOfFinitePresentation_of_finrank_eq _ hI.finrank

/-- Finite locally free closed subschemes of a fixed degree are preserved by arbitrary
base change. -/
theorem IsFiniteLocallyFreeOfDegree.comap_of_isPullback
    {X' S' : Scheme.{u}} {I : X.IdealSheafData} {f : X ⟶ S} {d : ℕ}
    (hI : I.IsFiniteLocallyFreeOfDegree f d) {g : X' ⟶ X} {f' : X' ⟶ S'} {h : S' ⟶ S}
    (H : IsPullback g f' f h) : (I.comap g).IsFiniteLocallyFreeOfDegree f' d := by
  obtain ⟨hfin, hflat, hrank⟩ := isFiniteLocallyFreeOfDegree_iff.mp hI
  have H' := I.isPullback_subschemeMap_comap f H
  apply isFiniteLocallyFreeOfDegree_iff.mpr
  refine ⟨MorphismProperty.of_isPullback H' hfin, MorphismProperty.of_isPullback H' hflat,
    funext fun s ↦ ?_⟩
  have := hfin
  have := hflat
  exact (I.finrank_comap_of_isPullback f g f' h H s).trans (congrFun hrank (h s))



/-- A closed family of fixed finite locally free degree descends from an open cover of its
parameter scheme. -/
theorem IsFiniteLocallyFreeOfDegree.of_openCover {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
    {T : Over S} {ι : Type*} {Z : ι → Over S}
    (g : ∀ i, Z i ⟶ T) [∀ i, IsOpenImmersion (g i).left]
    (hcover : ∀ t : T.left, ∃ i z, (g i).left z = t)
    (J : (pullback T.hom f).IdealSheafData)
    (hJ : ∀ i, (J.comap ((Over.pullback f).map (g i)).left).IsFiniteLocallyFreeOfDegree
      (pullback.fst (Z i).hom f) d) :
    J.IsFiniteLocallyFreeOfDegree (pullback.fst T.hom f) d := by
  let p := J.subschemeι ≫ pullback.fst T.hom f
  let 𝒰 : T.left.OpenCover := Scheme.Cover.mkOfCovers ι (fun i ↦ (Z i).left)
    (fun i ↦ (g i).left) hcover
  have H (i : ι) := J.isPullback_subschemeMap_comap (pullback.fst T.hom f)
    (Over.isPullback_pullback_map_left f (g i))
  have hprop (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (i : ι)
      (h : P ((J.comap ((Over.pullback f).map (g i)).left).subschemeι ≫
        pullback.fst (Z i).hom f)) : P (𝒰.pullbackHom p i) := by
    apply (MorphismProperty.cancel_left_of_respectsIso P (H i).isoPullback.hom _).mp
    -- The cover projection unfolds to the chosen pullback second projection; its source is
    -- definitionally the one identified by the displayed pullback comparison.
    dsimp only [Scheme.Cover.pullbackHom]
    erw [IsPullback.isoPullback_hom_snd]
    exact h
  have hfinite (i : ι) : IsFinite (𝒰.pullbackHom p i) := hprop _ i (hJ i).isFinite
  have hflat (i : ι) : Flat (𝒰.pullbackHom p i) := hprop _ i (hJ i).flat
  have : IsFinite p := IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) 𝒰 hfinite
  have : IsZariskiLocalAtTarget @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Flat)
  have : Flat p := IsZariskiLocalAtTarget.of_openCover (P := @Flat) 𝒰 hflat
  apply Scheme.IdealSheafData.isFiniteLocallyFreeOfDegree_iff.mpr
  refine ⟨‹IsFinite p›, ‹Flat p›, funext fun t ↦ ?_⟩
  obtain ⟨i, z, rfl⟩ := hcover t
  exact (J.finrank_comap_of_isPullback (pullback.fst T.hom f) _ _ _
    (Over.isPullback_pullback_map_left f (g i)) z).symm.trans ((hJ i).finrank z)

variable {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ S)

/-- A closed immersion preserves the degree of a finite locally free closed family under
scheme-theoretic image. -/
theorem IsFiniteLocallyFreeOfDegree.map_of_isClosedImmersion
    {d : ℕ} {J : X.IdealSheafData} (hJ : J.IsFiniteLocallyFreeOfDegree (i ≫ f) d) :
    (J.map i).IsFiniteLocallyFreeOfDegree f d := by
  let c := J.subschemeι ≫ i
  have : IsClosedImmersion c := inferInstance
  have : IsIso c.toImage := inferInstance
  have key : c.toImage ≫ c.imageι ≫ f = J.subschemeι ≫ i ≫ f := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    simp only [c, Category.assoc]
  rw [isFiniteLocallyFreeOfDegree_iff] at hJ ⊢
  -- The pushforward ideal is the kernel of `c`, whose zero scheme is the image of `c`.
  change IsFinite (c.imageι ≫ f) ∧ Flat (c.imageι ≫ f) ∧
    (c.imageι ≫ f).finrank = fun _ ↦ d
  rw [← key] at hJ
  exact (Scheme.Hom.isFinite_flat_finrank_comp_left_iff_of_isIso _ _ d).mp hJ

/-- A finite locally free closed family contained in a closed ambient subscheme has the
same degree when viewed inside that subscheme. -/
theorem IsFiniteLocallyFreeOfDegree.comap_of_isClosedImmersion
    {d : ℕ} {I : Y.IdealSheafData} (hI : I.IsFiniteLocallyFreeOfDegree f d)
    (hIX : i.ker ≤ I) : (I.comap i).IsFiniteLocallyFreeOfDegree (i ≫ f) d := by
  have hI' : i.ker ≤ I.subschemeι.ker := by
    rwa [Scheme.IdealSheafData.ker_subschemeι]
  have hpb : IsPullback (IsClosedImmersion.lift _ I.subschemeι hI') (𝟙 _)
      i I.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have : IsIso (pullback.snd i I.subschemeι) := by
    rw [← hpb.isoPullback_inv_snd, Category.comp_id]
    infer_instance
  have key : ((I.comapIso _).hom ≫ pullback.snd i I.subschemeι) ≫ I.subschemeι ≫ f =
      (I.comap i).subschemeι ≫ i ≫ f := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
      ← pullback.condition_assoc]
  rw [isFiniteLocallyFreeOfDegree_iff] at hI ⊢
  rw [← key]
  exact (Scheme.Hom.isFinite_flat_finrank_comp_left_iff_of_isIso _ _ d).mpr hI

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)

/-- The degree-`d` Hilbert functor of points of `X` over `S`, as a subfunctor of ideal sheaves
on base changes: its points over `T` are the closed subschemes of `T ×_S X` finite locally
free of degree `d` over `T`. -/
def hilbertSubfunctor : Subfunctor (baseChangeIdealSheafFunctor f) where
  obj T := {I | I.IsFiniteLocallyFreeOfDegree (pullback.fst T.unop.hom f) d}
  map φ _ hI := hI.comap_of_isPullback (Over.isPullback_pullback_map_left f φ.unop)

/-- Membership in the Hilbert subfunctor is the finite locally free degree condition on the
closed subscheme's projection to the test scheme. -/
@[simp]
theorem mem_hilbertSubfunctor_obj_iff {T : (Over S)ᵒᵖ}
    {I : (baseChangeIdealSheafFunctor f).obj T} :
    I ∈ (hilbertSubfunctor f d).obj T ↔
      I.IsFiniteLocallyFreeOfDegree (pullback.fst T.unop.hom f) d :=
  Iff.rfl

/-- The functor of finite locally free degree-`d` closed subschemes of the base changes of `X`.
Its values retain their defining ideal sheaf and finite locally free degree condition. -/
abbrev hilbertFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (hilbertSubfunctor f d).toFunctor

/-- Restriction of a Hilbert family pulls back its defining ideal sheaf. -/
theorem hilbertFunctor_map_val {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (I : (hilbertFunctor f d).obj T) :
    ((hilbertFunctor f d).map φ I).val =
      I.val.comap ((Over.pullback f).map φ.unop).left :=
  (rfl)

end TauCeti.AlgebraicGeometry
