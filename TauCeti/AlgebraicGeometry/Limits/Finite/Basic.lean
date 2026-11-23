/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Affine.Morphism
public import TauCeti.AlgebraicGeometry.Scheme.Opens
public import TauCeti.AlgebraicGeometry.Limits.Affine.Coordinates
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Local
public import TauCeti.RingTheory.FiniteType.FilteredColimits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Finite morphisms at a finite stage

A finite type morphism of quasi-compact quasi-separated stage schemes that
becomes finite over an affine-transition inverse limit becomes finite at
a finite stage. The proof descends affineness, then finitely many integral
generators on an affine cover of the target. This formalizes the finite-morphism
inheritance clause of the Stacks Project, Tag 01ZO.
-/


public section

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Functor

private theorem exists_isFinite_morphismRestrict_baseChange_affine_base_piece
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ k : I) (hk : i₀ ≤ k)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFiniteType f₀.left]
    (haffine : IsAffineHom (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left))
    (V : Y₀.left.Opens) (hV : IsAffineOpen V)
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W)
    (hVW : V ≤ Y₀.hom ⁻¹ᵁ W)
    (hfinite : IsFinite
      ((((Over.pullback (c.π.app (op i₀))).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (c.π.app (op i₀))) ⁻¹ᵁ V))) :
    ∃ (j : I) (hkj : k ≤ j), ∀ (l : I) (hjl : j ≤ l),
      IsFinite
        ((((Over.pullback (D.map (homOfLE (hk.trans (hkj.trans hjl))).op)).map f₀).left)
          ∣_ ((pullback.fst Y₀.hom
            (D.map (homOfLE (hk.trans (hkj.trans hjl))).op)) ⁻¹ᵁ V)) := by
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  classical
  have : IsDirected {i : I // k ≤ i} (· ≤ ·) := inferInstanceAs (IsDirectedOrder (Set.Ici k))
  let d := D.map (homOfLE hk).op
  let fT := ((Over.pullback d).map f₀).left
  let VT := (pullback.fst Y₀.hom d) ⁻¹ᵁ V
  have : IsAffineHom fT := haffine
  have : IsAffineHom (pullback.fst Y₀.hom d) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback Y₀.hom d).flip inferInstance
  have hVT : IsAffineOpen VT := hV.preimage (pullback.fst Y₀.hom d)
  have hUT : IsAffineOpen (fT ⁻¹ᵁ VT) := hVT.preimage fT
  have : LocallyOfFiniteType fT := MorphismProperty.overPullbackMap
    (P := @LocallyOfFiniteType) d f₀ (show LocallyOfFiniteType f₀.left from inferInstance)
  obtain ⟨F, B, C, aB, aC, H⟩ :=
    exists_affine_base_piece_tensor_presentation D c hc i₀ k hk X₀ Y₀ f₀
      V hVT hUT (show LocallyOfFiniteType (fT ∣_ VT) from inferInstance) W hW hVW
  let : Algebra (F.obj ⟨k, le_rfl⟩) B := aB.toAlgebra
  let : Algebra (F.obj ⟨k, le_rfl⟩) C := aC.toAlgebra
  obtain ⟨φ, hft, ⟨elim⟩, estage⟩ := H
  let : Algebra (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
    (CommRingCat.Hom.hom (colimit.ι F ⟨k, le_rfl⟩)).toAlgebra
  have hlim : (Algebra.TensorProduct.map
      (AlgHom.id (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u})) φ).Finite := by
    exact (IsFinite.SpecMap_iff (CommRingCat.ofHom
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u})) φ).toRingHom)).mp
      ((MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) elim).mp hfinite)
  obtain ⟨j, hj, hjfin⟩ :=
    F.exists_finite_tensorProductMap_of_colimit ⟨k, le_rfl⟩ B C φ hft hlim
  refine ⟨j.val, j.property, ?_⟩
  intro l hjl
  let l' : {i : I // k ≤ i} := ⟨l, j.property.trans hjl⟩
  let : Algebra (F.obj ⟨k, le_rfl⟩) (F.obj l') :=
    (CommRingCat.Hom.hom (F.map (homOfLE (hj.trans hjl)))).toAlgebra
  obtain ⟨e⟩ := estage l'
  apply (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) e).mpr
  exact (IsFinite.SpecMap_iff (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id (F.obj ⟨k, le_rfl⟩) (F.obj l')) φ).toRingHom)).mpr
    (hjfin l' hjl)


private theorem exists_isFinite_morphismRestrict_baseChange_affine_open
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ k : I) (hk : i₀ ≤ k)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFiniteType f₀.left]
    (haffine : IsAffineHom (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left))
    (V : Y₀.left.Opens) (hV : IsAffineOpen V)
    (hfinite : IsFinite
      ((((Over.pullback (c.π.app (op i₀))).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (c.π.app (op i₀))) ⁻¹ᵁ V))) :
    ∃ (j : I) (hkj : k ≤ j), ∀ (i : I) (hji : j ≤ i),
      IsFinite
        ((((Over.pullback (D.map (homOfLE (hk.trans (hkj.trans hji))).op)).map f₀).left)
          ∣_ ((pullback.fst Y₀.hom
            (D.map (homOfLE (hk.trans (hkj.trans hji))).op)) ⁻¹ᵁ V)) := by
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  classical
  obtain ⟨U, hU, hUV, W, hW, hUW, t, ht⟩ :=
    AlgebraicGeometry.Scheme.Hom.exists_finite_affine_refinement Y₀.hom V hV.isCompact
  have hlocal (b : t) :=
    exists_isFinite_morphismRestrict_baseChange_affine_base_piece D c hc i₀ k hk
      X₀ Y₀ f₀ haffine (U b.val) (hU b.val) (W b.val) (hW b.val) (hUW b.val)
      (by
        let p := pullback.fst Y₀.hom (c.π.app (op i₀))
        have H := @IsFinite.instMorphismRestrict _ _ _
          ((p ⁻¹ᵁ V).ι ⁻¹ᵁ (p ⁻¹ᵁ U b.val)) hfinite
        have he : (p ⁻¹ᵁ V).ι ''ᵁ ((p ⁻¹ᵁ V).ι ⁻¹ᵁ (p ⁻¹ᵁ U b.val)) =
            p ⁻¹ᵁ U b.val := by
          rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
          exact inf_eq_right.mpr (p.preimage_mono (hUV b.val))
        have H' := (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
          (morphismRestrictRestrict _ _ _)).mp H
        rw [he] at H'
        exact H')
  choose j hj hfin using hlocal
  have : Nonempty I := ⟨k⟩
  obtain ⟨l, hl⟩ := (Set.finite_range j).bddAbove
  obtain ⟨l', hkl', hll'⟩ := exists_ge_ge k l
  refine ⟨l', hkl', ?_⟩
  intro i hli
  apply Scheme.Hom.isFinite_morphismRestrict_of_cover _ _
    (fun b : t ↦ (pullback.fst Y₀.hom
      (D.map (homOfLE (hk.trans (hkl'.trans hli))).op)) ⁻¹ᵁ U b.val)
  · intro x hx
    obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp (ht hx)
    obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hxb
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨b, hb⟩, hxb⟩
  · intro b
    have hji := ((hl (Set.mem_range_self b)).trans hll').trans hli
    exact hfin b i hji


/-- A finite type stage morphism finite over the limit becomes finite at a later stage. -/
theorem exists_isFinite_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    (hfinite : IsFinite (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsFinite (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) := by
  classical
  have hf : IsAffineHom (((Over.pullback (c.π.app (op i₀))).map f₀).left) :=
    hfinite.toIsAffineHom
  obtain ⟨k, hk, haffine⟩ :=
    exists_isAffineHom_baseChange_of_isLimit D c hc i₀ X₀ Y₀ f₀ hf
  have hak := haffine
  let 𝒰 := Y₀.left.affineCover.finiteSubcover
  have hlocal (b : 𝒰.I₀) :=
    exists_isFinite_morphismRestrict_baseChange_affine_open D c hc i₀ k hk X₀ Y₀ f₀
      hak (𝒰.f b).opensRange (isAffineOpen_opensRange (𝒰.f b))
      (@IsFinite.instMorphismRestrict _ _ _ _ hfinite)
  choose j hj hfin using hlocal
  have : Nonempty I := ⟨k⟩
  obtain ⟨i, hi⟩ := (Set.finite_range j).bddAbove
  obtain ⟨i', hki', hii'⟩ := exists_ge_ge k i
  refine ⟨i', hk.trans hki', ?_⟩
  let X := pullback X₀.hom (D.map (homOfLE (hk.trans hki')).op)
  let Y := pullback Y₀.hom (D.map (homOfLE (hk.trans hki')).op)
  let f := ((Over.pullback (D.map (homOfLE (hk.trans hki')).op)).map f₀).left
  have hrestrict : IsFinite (f ∣_ (⊤ : Y.Opens)) :=
    Scheme.Hom.isFinite_morphismRestrict_of_cover f ⊤
    (fun b : 𝒰.I₀ ↦ (pullback.fst Y₀.hom
      (D.map (homOfLE (hk.trans hki')).op)) ⁻¹ᵁ (𝒰.f b).opensRange)
    (by simp only [← Scheme.Hom.preimage_iSup, 𝒰.iSup_opensRange,
      Scheme.Hom.preimage_top, le_refl])
    (fun b ↦ hfin b i' ((hi (Set.mem_range_self b)).trans hii'))
  have htop : IsFinite Y.topIso.hom := IsFinite.instOfIsIsoScheme _
  have H : IsFinite ((f ∣_ (⊤ : Y.Opens)) ≫ (⊤ : Y.Opens).ι) :=
    @IsFinite.instCompScheme _ _ _ _ _ hrestrict htop
  rw [morphismRestrict_ι] at H
  have : IsIso (f ⁻¹ᵁ (⊤ : Y.Opens)).ι := by
    simp only [Scheme.Hom.preimage_top]
    exact inferInstanceAs (IsIso X.topIso.hom)
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) _ _).mp H

end CategoryTheory.Functor
end
