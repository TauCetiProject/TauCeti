/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeProj.BaseChange.Affine
public import TauCeti.AlgebraicGeometry.RelativeProj.Basic

/-!
# Base change of relative Proj

For a graded quasi-coherent algebra `A` on `Y` and a morphism `g : X ⟶ Y`,
`GradedQuasicoherentAlgebra.relativeProjPullbackHom` is the projection from the relative Proj of
`g^* A` to the relative Proj of `A`. Its defining chart formula uses pullback of graded sections.
`GradedQuasicoherentAlgebra.isPullback_relativeProjPullbackHom` identifies the relative Proj of
`g^* A` with the scheme-theoretic fibre product over `Y`. No finite generation or flatness is
required, and the degree-zero part may be larger than the structure sheaf.

The construction follows [Stacks, Lemma 27.16.10 (01O3)](https://stacks.math.columbia.edu/tag/01O3).
The gluing argument is adapted from `RelativeProj/BaseChange.lean` in `roed-math/TauCeti-w2-fresh`
at revision `8bf602f6c2bed52e7e390df1ba2c2de30f8a6dfb`.
-/

public section

open CategoryTheory Limits
open _root_.AlgebraicGeometry Scheme.AffineZariskiSite

namespace TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra

universe u

noncomputable section

variable {X Y : Scheme.{u}} (A : GradedQuasicoherentAlgebra Y) (g : X ⟶ Y)

/-- Pairs of affine opens `V`, `U` in the source and target with `V ≤ g⁻¹ᵁ U`. -/
private abbrev ChartPair :=
  {p : X.AffineZariskiSite × Y.AffineZariskiSite // p.fst.toOpens ≤ g ⁻¹ᵁ p.snd.toOpens}

/-- Use compatible pairs of affine neighbourhoods to cover the source of the base change. -/
private abbrev baseCover : X.OpenCover :=
  .mkOfCovers (ChartPair g) (fun i ↦ Spec Γ(X, i.val.fst.toOpens))
    (fun i ↦ i.val.fst.property.fromSpec) fun x ↦ by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) hxU (g ⁻¹ᵁ U).isOpen
    rw [← hV.range_fromSpec] at hxV
    obtain ⟨z, hz⟩ := hxV
    exact ⟨⟨(⟨V, hV⟩, ⟨U, hU⟩), hVU⟩, z, hz⟩

/-- Cover the relative Proj of the pulled-back algebra by its charts over the same pairs. -/
private abbrev projCover : ((pullback g).obj A).obj.relativeProj.OpenCover :=
  .mkOfCovers (ChartPair g) (fun i ↦ ((pullback g).obj A).obj.relativeProjCover.X i.val.fst)
    (fun i ↦ ((pullback g).obj A).obj.relativeProjCover.f i.val.fst) fun z ↦ by
    obtain ⟨⟨⟨V, U⟩, hV⟩, x, hx⟩ :=
      (baseCover g).exists_eq (((pullback g).obj A).obj.relativeProjToBase z)
    have hx' : V.property.fromSpec x = ((pullback g).obj A).obj.relativeProjToBase z := hx
    have hxV : V.property.fromSpec x ∈ V.property.fromSpec.opensRange := ⟨x, rfl⟩
    rw [V.property.opensRange_fromSpec] at hxV
    have hz : z ∈ ((pullback g).obj A).obj.relativeProjToBase ⁻¹ᵁ V.toOpens := by
      -- Apply the chart equality to the image of `z`, not to `z` in the preimage.
      change ((pullback g).obj A).obj.relativeProjToBase z ∈ V.toOpens
      exact hx' ▸ hxV
    rw [CommMon.relativeProjToBase_preimage] at hz
    exact ⟨⟨(V, U), hV⟩, hz⟩

private instance : Preorder (projCover A g).I₀ := inferInstanceAs (Preorder (ChartPair g))

/-- The paired affine charts admit common refinements at every point of their overlaps. -/
private lemma exists_chartPair_le {i j : ChartPair g} {x : X}
    (hi : x ∈ i.val.fst.toOpens) (hj : x ∈ j.val.fst.toOpens) :
    ∃ k : ChartPair g, k ≤ i ∧ k ≤ j ∧ x ∈ k.val.fst.toOpens := by
  -- The small affine site orders opens by *principal* inclusion in each chart.
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter
    i.val.snd.property j.val.snd.property (g x) ⟨i.property hi, j.property hj⟩
  obtain ⟨s, t, hst, hxs⟩ := exists_basicOpen_le_affine_inter
    i.val.fst.property j.val.fst.property x ⟨hi, hj⟩
  let W := i.val.fst.basicOpen s
  obtain ⟨r, hr, hxr⟩ := W.property.exists_basicOpen_le
    (V := g ⁻¹ᵁ (i.val.snd.basicOpen a).toOpens) ⟨x, hxa⟩ hxs
  exact ⟨⟨(W.basicOpen r, i.val.snd.basicOpen a), hr⟩,
    ⟨(W.basicOpen_le r).trans (i.val.fst.basicOpen_le s), i.val.snd.basicOpen_le a⟩,
    ⟨(W.basicOpen_le r).trans ⟨t, hst.symm⟩, ⟨b, hab.symm⟩⟩, hxr⟩

private instance : (projCover A g).LocallyDirected where
  trans r := ((pullback g).obj A).obj.relativeProjGluingData.functor.map (homOfLE (leOfHom r).1)
  trans_id _ := CategoryTheory.Functor.map_id _ _
  trans_comp _ _ := CategoryTheory.Functor.map_comp _ _ _
  w _ := colimit.w _ _
  directed {i j} z := by
    let B := ((pullback g).obj A).obj
    let f₁ := B.relativeProjCover.f i.val.fst
    let f₂ := B.relativeProjCover.f j.val.fst
    let p := (pullback.fst f₁ f₂ ≫ f₁) z
    let q := B.relativeProjToBase p
    have memOpens (W : X.AffineZariskiSite) (hw : p ∈ (B.relativeProjCover.f W).opensRange) :
        q ∈ W.toOpens := by
      rw [← B.relativeProjToBase_preimage] at hw
      exact hw
    have hi := memOpens i.val.fst ⟨pullback.fst f₁ f₂ z, rfl⟩
    have h := (pullback.condition (f := f₁) (g := f₂)).symm
    have hj := memOpens j.val.fst ⟨pullback.snd f₁ f₂ z,
      (Scheme.Hom.comp_apply _ _ _).symm.trans congr($h z)⟩
    obtain ⟨k, hki, hkj, hk⟩ := exists_chartPair_le g hi hj
    have hpk : p ∈ B.relativeProjToBase ⁻¹ᵁ k.val.fst.toOpens := hk
    rw [B.relativeProjToBase_preimage] at hpk
    obtain ⟨w, hw⟩ := hpk
    refine ⟨k, homOfLE hki, homOfLE hkj, w, ?_⟩
    apply (pullback.fst f₁ f₂ ≫ f₁).isOpenEmbedding.injective
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    have hl := pullback.lift_fst_assoc (f := f₁) (g := f₂)
      (B.relativeProjGluingData.functor.map (homOfLE hki.1))
      (B.relativeProjGluingData.functor.map (homOfLE hkj.1))
      ((colimit.w _ _).trans (colimit.w _ _).symm) f₁
    have hc := hl.trans (colimit.w B.relativeProjGluingData.functor (homOfLE hki.1))
    exact congr($hc w).trans hw
  property_trans r :=
    inferInstanceAs (IsOpenImmersion (((pullback g).obj A).obj.relativeProjGluingData.functor.map
      (homOfLE (leOfHom r).1)))

/-- The chart map to the target relative Proj, formed by pulling back graded sections. -/
private def chartHom (i : ChartPair g) : (projCover A g).X i ⟶ A.obj.relativeProj :=
  Proj.map (A.pullbackGradedSectionsGradedHom g i.property)
    (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g i.property
      i.val.snd.property i.val.fst.property) ≫ A.obj.relativeProjCover.f i.val.snd

private lemma chartHom_compat {i j : (projCover A g).I₀} (f : i ⟶ j) :
    (projCover A g).trans f ≫ chartHom A g j = chartHom A g i := by
  let a := homOfLE (leOfHom f).1
  let b := homOfLE (leOfHom f).2
  let h := i.property.trans (g.preimage_mono (toOpens_mono (leOfHom f).2))
  let m := Proj.map (A.pullbackGradedSectionsGradedHom g h)
    (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g h j.val.snd.property i.val.fst.property)
  have h₁ : ((pullback g).obj A).obj.relativeProjGluingData.functor.map a ≫
      Proj.map (A.pullbackGradedSectionsGradedHom g j.property)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g j.property
          j.val.snd.property j.val.fst.property) = m := by
    rw [CommMon.relativeProjGluingData_functor_map]
    exact (Proj.map_comp ..).symm.trans (Proj.map_congr
      (restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom g A j.property _)
      _ _)
  have h₂ : Proj.map (A.pullbackGradedSectionsGradedHom g i.property)
      (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g i.property
        i.val.snd.property i.val.fst.property) ≫
        A.obj.relativeProjGluingData.functor.map b = m := by
    rw [CommMon.relativeProjGluingData_functor_map]
    exact (Proj.map_comp ..).symm.trans (Proj.map_congr
      (pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom g A _ i.property)
      _ _)
  -- The cover's transition is the source chart transition, and `chartHom` ends with
  -- the target colimit coprojection. Spell these out to use `h₁`, `h₂` and `colimit.w`.
  change ((pullback g).obj A).obj.relativeProjGluingData.functor.map a ≫ (_ ≫ _) = _ ≫ _
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (h₁.trans h₂.symm)).trans <|
    (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (colimit.w A.obj.relativeProjGluingData.functor b)

/-- The projection `Proj_X(g^* A) ⟶ Proj_Y(A)` induced by pullback of graded sections. -/
def relativeProjPullbackHom :
    ((pullback g).obj A).obj.relativeProj ⟶ A.obj.relativeProj :=
  (projCover A g).glueMorphismsOfLocallyDirected (chartHom A g) (chartHom_compat A g)

/-- Over a pair of affine opens `V ≤ g⁻¹ᵁ U`, the projection is the map of projective spectra
induced by pullback of sections from `U` to `V`, followed by the chart over `U`. -/
@[reassoc]
theorem relativeProjCover_f_relativeProjPullbackHom (V : X.AffineZariskiSite)
    (U : Y.AffineZariskiSite) (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    ((pullback g).obj A).obj.relativeProjCover.f V ≫ A.relativeProjPullbackHom g =
      Proj.map (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.property V.property) ≫
        A.obj.relativeProjCover.f U :=
  (projCover A g).map_glueMorphismsOfLocallyDirected _ _ ⟨(V, U), hV⟩

/-- The projection from the relative Proj of the pulled-back algebra lies over `g`. -/
@[reassoc (attr := simp)]
theorem relativeProjPullbackHom_relativeProjToBase :
    A.relativeProjPullbackHom g ≫ A.obj.relativeProjToBase =
      ((pullback g).obj A).obj.relativeProjToBase ≫ g := by
  refine (projCover A g).hom_ext _ _ fun ⟨⟨V, U⟩, hV⟩ ↦ ?_
  -- Use the original relative Proj charts rather than their reindexing in `projCover`.
  change (((pullback g).obj A).obj.relativeProjCover.f V ≫ _) =
    (((pullback g).obj A).obj.relativeProjCover.f V ≫ _)
  refine (A.relativeProjCover_f_relativeProjPullbackHom_assoc g V U hV _).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (A.obj.relativeProjCover_f_relativeProjToBase U)).trans <| ?_
  refine ((A.isPullback_proj_pullbackGradedSections g hV U.property V.property).w_assoc _).trans <|
    (congrArg (_ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec g U.property V.property hV)).trans <|
    (CommMon.relativeProjCover_f_relativeProjToBase_assoc _ V g).symm

/-- Base change of a relative Proj is the relative Proj of the pulled-back graded algebra.
The two projections are the structure morphism and `relativeProjPullbackHom`. -/
theorem isPullback_relativeProjPullbackHom :
    IsPullback ((pullback g).obj A).obj.relativeProjToBase (A.relativeProjPullbackHom g)
      g A.obj.relativeProjToBase := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (baseCover g) fun ⟨⟨V, U⟩, hV⟩ ↦ ?_
  have chart {S : Scheme.{u}} (B : GradedQuasicoherentAlgebra S) (W : S.AffineZariskiSite) :
      IsPullback (Proj.toSpecCoeff (B.obj.gradedSectionsGrading W.toOpens))
        (B.obj.relativeProjCover.f W) W.property.fromSpec B.obj.relativeProjToBase := by
    refine (B.obj.isPullback_relativeProjCover W).of_iso (.refl _) W.property.isoSpec
      (.refl _) (.refl _) ?_ ?_ ?_ ?_
    · simp
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · simp [← IsAffineOpen.isoSpec_inv_ι]
    · simp
  have hQ := ((A.isPullback_proj_pullbackGradedSections g hV U.property V.property).paste_horiz
    (chart A U).flip).flip
  rw [← A.relativeProjCover_f_relativeProjPullbackHom g V U hV,
    IsAffineOpen.SpecMap_appLE_fromSpec g U.property V.property hV] at hQ
  -- Compare the pullback of the cover of `X` with the affine charts of `Proj_X(g^* A)`.
  let hV' := (chart ((pullback g).obj A) V).flip
  exact hQ.of_iso hV'.isoPullback (.refl _) (.refl _) (.refl _)
    ((Category.comp_id _).trans hV'.isoPullback_hom_snd.symm)
    ((Category.comp_id _).trans (hV'.isoPullback_hom_fst_assoc _).symm)
    (Category.id_comp _).symm (by simp)

end

end TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra
