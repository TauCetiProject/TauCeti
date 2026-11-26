/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Cofiltered

/-!
# Existence of cofiltered limits of schemes with affine transition maps

A cofiltered diagram `D : I ⥤ Scheme` with affine transition maps has a limit (Stacks,
Lemma 32.2.1 (01YW)). A diagram of affine schemes has a limit, the spectrum of the colimit of the
rings of global sections, because Mathlib's `AffineScheme` has limits and the inclusion
`AffineScheme.forgetToScheme` preserves them. In general, fix a member `Dᵢ` and a locally
directed open cover of `Dᵢ` by affine schemes `Uᵤ`, such as the cover by all affine opens. The
base changes `Dⱼ ×_{Dᵢ} Uᵤ` of the members over `i` are affine, so they have an affine limit `Lᵤ`;
base change along `Uᵤ ⟶ Uᵥ` identifies `Lᵤ` with `Lᵥ ×_{Uᵥ} Uᵤ`, so the `Lᵤ` glue to a scheme `L`
over `Dᵢ` (`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`). Its projections to the `Dⱼ` are
glued from those of the `Lᵤ`, and a cone with point `T` lifts to `L` over the preimages in `T` of
the `Uᵤ`, where it lifts to the `Lᵤ`. The members over `i` are initial in the diagram, so `L` is
the limit of `D`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.hasLimit_of_isAffine`: a diagram of affine schemes has a
  limit.
* `TauCeti.AlgebraicGeometry.Scheme.hasLimit_of_isAffineHom`: a cofiltered diagram of schemes
  with affine transition maps has a limit.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme

/-- A small diagram of affine schemes has a limit in `Scheme`. -/
theorem hasLimit_of_isAffine {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    [∀ i, IsAffine (D.obj i)] : HasLimit D :=
  have h (i : I) : Scheme.Spec.essImage (D.obj i) := essImage_Spec.mpr inferInstance
  let F : I ⥤ AffineScheme.{u} := Scheme.Spec.essImage.lift D h
  hasLimit_of_iso (F := F ⋙ AffineScheme.forgetToScheme) (Scheme.Spec.essImage.liftCompιIso D h)

section General

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {i : I} (𝒰 : (D.obj i).OpenCover)
  [Category 𝒰.I₀] [𝒰.LocallyDirected] [∀ U, IsAffine (𝒰.X U)]

namespace AffineTransitionLimit

/- The members of the diagrams below are `pullback (D.map j.hom) (𝒰.f U)` only up to unfolding
`Over.mk` and the cover data, which `simp` does not do inside implicit arguments; the proofs
therefore rewrite with the explicitly stated lemmas `functor_map_π`, `toCover_eq` and `π_snd`. -/

/-- (Implementation) The base changes `Dⱼ ×_{Dᵢ} 𝒰ᵤ` of the members of `D` over `i` to the
members `𝒰ᵤ` of an open cover of `Dᵢ`, functorially in `U`. -/
private noncomputable abbrev diagram : 𝒰.I₀ ⥤ Over i ⥤ Scheme.{u} where
  obj U := D.pullbackOver (𝒰.f U)
  map {U V} h :=
    { app j := pullback.map _ _ _ _ (𝟙 _) (𝒰.trans h) (𝟙 _) (by simp) (by simp)
      naturality j k f := by apply pullback.hom_ext <;> simp }
  map_id U := by ext j : 2; apply pullback.hom_ext <;> simp
  map_comp f g := by ext j : 2; apply pullback.hom_ext <;> simp

private instance (U : 𝒰.I₀) (j : Over i) : IsAffine (((diagram D 𝒰).obj U).obj j) :=
  have : IsAffineHom (pullback.snd (D.map j.hom) (𝒰.f U)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D.map j.hom) (𝒰.f U))
      inferInstance
  isAffine_of_isAffineHom (pullback.snd (D.map j.hom) (𝒰.f U))

private instance (U : 𝒰.I₀) : HasLimit ((diagram D 𝒰).obj U) := hasLimit_of_isAffine _

/-- (Implementation) The limits `lim_j Dⱼ ×_{Dᵢ} 𝒰ᵤ`, which are affine, functorially in `U`. -/
private noncomputable abbrev functor : 𝒰.I₀ ⥤ Scheme.{u} where
  obj U := limit ((diagram D 𝒰).obj U)
  map h := limMap ((diagram D 𝒰).map h)
  map_id U := limit.hom_ext fun j ↦ by
    rw [limMap_π, Category.id_comp, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.comp_id]
  map_comp f g := limit.hom_ext fun j ↦ by
    rw [limMap_π, Category.assoc, limMap_π, limMap_π_assoc, Functor.map_comp, NatTrans.comp_app]

@[reassoc]
private lemma functor_map_π {U V : 𝒰.I₀} (h : U ⟶ V) (j : Over i) :
    (functor D 𝒰).map h ≫ limit.π ((diagram D 𝒰).obj V) j =
      limit.π ((diagram D 𝒰).obj U) j ≫
        pullback.map _ _ _ _ (𝟙 _) (𝒰.trans h) (𝟙 _) (by simp) (by simp) :=
  limMap_π _ _

/-- (Implementation) The map `lim_j Dⱼ ×_{Dᵢ} 𝒰ᵤ ⟶ 𝒰ᵤ`. -/
private noncomputable def toCover (U : 𝒰.I₀) : (functor D 𝒰).obj U ⟶ 𝒰.X U :=
  limit.π ((diagram D 𝒰).obj U) (Over.mk (𝟙 i)) ≫ pullback.snd _ _

private lemma toCover_eq (U : 𝒰.I₀) (j : Over i) :
    toCover D 𝒰 U = limit.π ((diagram D 𝒰).obj U) j ≫ pullback.snd _ _ := by
  rw [toCover, ← limit.w _ (Over.homMk j.hom : j ⟶ Over.mk (𝟙 i)), Category.assoc,
    Functor.pullbackOver_map_snd]

@[reassoc (attr := simp)]
private lemma π_snd (U : 𝒰.I₀) (j : Over i) :
    limit.π ((diagram D 𝒰).obj U) j ≫ pullback.snd _ _ = toCover D 𝒰 U :=
  (toCover_eq D 𝒰 U j).symm

@[reassoc (attr := simp)]
private lemma functor_map_toCover {U V : 𝒰.I₀} (h : U ⟶ V) :
    (functor D 𝒰).map h ≫ toCover D 𝒰 V = toCover D 𝒰 U ≫ 𝒰.trans h := by
  rw [toCover_eq D 𝒰 V (Over.mk (𝟙 i)), functor_map_π_assoc, pullback.lift_snd, ← Category.assoc,
    π_snd]

/-- (Implementation) The maps `lim_j Dⱼ ×_{Dᵢ} 𝒰ᵤ ⟶ 𝒰ᵤ`, natural in `U`. -/
private noncomputable def natTrans : functor D 𝒰 ⟶ 𝒰.functorOfLocallyDirected where
  app := toCover D 𝒰
  naturality _ _ h := functor_map_toCover D 𝒰 h

private lemma isPullback_functor_map {U V : 𝒰.I₀} (h : U ⟶ V) :
    IsPullback ((functor D 𝒰).map h) (toCover D 𝒰 U) (toCover D 𝒰 V) (𝒰.trans h) := by
  let l (s : PullbackCone (toCover D 𝒰 V) (𝒰.trans h)) : s.pt ⟶ (functor D 𝒰).obj U :=
    limit.lift ((diagram D 𝒰).obj U)
      { pt := s.pt
        π :=
          { app j := pullback.lift (s.fst ≫ limit.π _ j ≫ pullback.fst _ _) s.snd (by
              simp only [Category.assoc]
              rw [pullback.condition, π_snd_assoc, reassoc_of% s.condition, 𝒰.trans_map])
            naturality j k f := by
              apply pullback.hom_ext
              · simp [← limit.w _ f]
              · simp } }
  have hl_fst (s : PullbackCone (toCover D 𝒰 V) (𝒰.trans h)) (j : Over i) :
      l s ≫ limit.π _ j ≫ pullback.fst _ _ = s.fst ≫ limit.π _ j ≫ pullback.fst _ _ := by
    rw [limit.lift_π_assoc]
    exact pullback.lift_fst _ _ _
  have hl_snd (s : PullbackCone (toCover D 𝒰 V) (𝒰.trans h)) : l s ≫ toCover D 𝒰 U = s.snd := by
    rw [toCover_eq D 𝒰 U (Over.mk (𝟙 i)), limit.lift_π_assoc]
    exact pullback.lift_snd _ _ _
  refine ⟨⟨functor_map_toCover D 𝒰 h⟩, ⟨PullbackCone.IsLimit.mk _ l ?_ hl_snd ?_⟩⟩
  · intro s
    refine limit.hom_ext fun j ↦ pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [functor_map_π_assoc, pullback.lift_fst, Category.comp_id, hl_fst]
    · simp only [Category.assoc]
      rw [π_snd, functor_map_toCover, reassoc_of% hl_snd]
      exact s.condition.symm
  · intro s m hm₁ hm₂
    refine limit.hom_ext fun j ↦ pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [hl_fst, ← hm₁]
      simp only [Category.assoc]
      rw [functor_map_π_assoc, pullback.lift_fst, Category.comp_id]
    · simp only [Category.assoc]
      rw [π_snd, hm₂, hl_snd]

/-- (Implementation) The relative gluing datum of the affine limits `lim_j Dⱼ ×_{Dᵢ} 𝒰ᵤ`. -/
private noncomputable abbrev gluingData : 𝒰.RelativeGluingData where
  functor := functor D 𝒰
  natTrans := natTrans D 𝒰
  equifibered := by
    intro U V h
    exact isPullback_functor_map D 𝒰 h

private instance {U V : 𝒰.I₀} (h : U ⟶ V) : IsOpenImmersion ((functor D 𝒰).map h) :=
  Scheme.Cover.RelativeGluingData.instIsOpenImmersionMapI₀Functor
    (gluingData D 𝒰) h

variable [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀]

private instance : (functor D 𝒰 ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin
    (gluingData D 𝒰)

/-- (Implementation) The projection from the glued scheme to a member `Dⱼ` over `i`. -/
private noncomputable def π (j : Over i) : (gluingData D 𝒰).glued ⟶ D.obj j.left :=
  colimit.desc (functor D 𝒰)
    { pt := D.obj j.left
      ι :=
        { app U := limit.π ((diagram D 𝒰).obj U) j ≫ pullback.fst _ _
          naturality U V h := by simp } }

@[reassoc (attr := simp)]
private lemma ι_π (U : 𝒰.I₀) (j : Over i) :
    colimit.ι (functor D 𝒰) U ≫ π D 𝒰 j = limit.π ((diagram D 𝒰).obj U) j ≫ pullback.fst _ _ :=
  colimit.ι_desc _ _

private lemma π_comp_map_hom (j : Over i) :
    π D 𝒰 j ≫ D.map j.hom = (gluingData D 𝒰).toBase := by
  refine colimit.hom_ext fun U ↦ ?_
  rw [ι_π_assoc, pullback.condition, ← Category.assoc, π_snd]
  exact ((gluingData D 𝒰).ι_toBase U).symm

private lemma π_comp_map {j k : Over i} (f : j ⟶ k) : π D 𝒰 j ≫ D.map f.left = π D 𝒰 k := by
  refine colimit.hom_ext fun U ↦ ?_
  rw [ι_π_assoc, ι_π, ← limit.w _ f, Category.assoc, Functor.pullbackOver_map_fst]

/-- (Implementation) The cone over the members of `D` over `i` with point the glued scheme. -/
private noncomputable def cone : Cone (Over.forget i ⋙ D) where
  pt := (gluingData D 𝒰).glued
  π :=
    { app := π D 𝒰
      naturality _ _ f := (Category.id_comp _).trans (π_comp_map D 𝒰 f).symm }

/-- (Implementation) Morphisms to the glued scheme agreeing after every projection agree. -/
private lemma hom_ext {W : Scheme.{u}} {a b : W ⟶ (gluingData D 𝒰).glued}
    (h : ∀ j, a ≫ π D 𝒰 j = b ≫ π D 𝒰 j) : a = b := by
  have hab : a ≫ (gluingData D 𝒰).toBase = b ≫ (gluingData D 𝒰).toBase := by
    rw [← π_comp_map_hom D 𝒰 (Over.mk (𝟙 i)), reassoc_of% h]
  refine AlgebraicGeometry.Scheme.Cover.hom_ext (𝒰.pullback₁ (a ≫ (gluingData D 𝒰).toBase))
    _ _ fun (U : 𝒰.I₀) ↦ ?_
  have hP : IsPullback (toCover D 𝒰 U) (colimit.ι (functor D 𝒰) U) (𝒰.f U)
      (gluingData D 𝒰).toBase :=
    (gluingData D 𝒰).isPullback_natTrans_ι_toBase U
  have wa : pullback.snd (a ≫ (gluingData D 𝒰).toBase) (𝒰.f U) ≫ 𝒰.f U =
      (pullback.fst _ _ ≫ a) ≫ (gluingData D 𝒰).toBase := by
    rw [Category.assoc, ← pullback.condition]
  have wb : pullback.snd (a ≫ (gluingData D 𝒰).toBase) (𝒰.f U) ≫ 𝒰.f U =
      (pullback.fst _ _ ≫ b) ≫ (gluingData D 𝒰).toBase := by
    rw [Category.assoc, ← hab, ← pullback.condition]
  have hc : hP.lift _ _ wa = hP.lift _ _ wb := by
    refine limit.hom_ext fun j ↦ pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [← ι_π, hP.lift_snd_assoc, hP.lift_snd_assoc]
      simp only [Category.assoc, h]
    · simp only [Category.assoc]
      rw [π_snd, hP.lift_fst, hP.lift_fst]
  exact (hP.lift_snd _ _ wa).symm.trans ((congrArg (· ≫ _) hc).trans (hP.lift_snd _ _ wb))

/-- (Implementation) Over a member of the cover, a cone over the members of `D` over `i` lifts
to the affine limit. -/
private noncomputable def liftAux (s : Cone (Over.forget i ⋙ D)) (U : 𝒰.I₀) :
    pullback (s.π.app (Over.mk (𝟙 i))) (𝒰.f U) ⟶ (functor D 𝒰).obj U :=
  limit.lift ((diagram D 𝒰).obj U)
    { pt := _
      π :=
        { app j := pullback.lift (pullback.fst _ _ ≫ s.π.app j) (pullback.snd _ _) (by
            rw [Category.assoc, ← pullback.condition,
              ← s.w (Over.homMk j.hom : j ⟶ Over.mk (𝟙 i))]
            rfl)
          naturality j k f := by
            apply pullback.hom_ext
            · simp [← s.w f]
            · simp } }

@[reassoc]
private lemma liftAux_π (s : Cone (Over.forget i ⋙ D)) (U : 𝒰.I₀) (j : Over i) :
    liftAux D 𝒰 s U ≫ colimit.ι (functor D 𝒰) U ≫ π D 𝒰 j = pullback.fst _ _ ≫ s.π.app j := by
  rw [ι_π, liftAux, limit.lift_π_assoc]
  exact pullback.lift_fst _ _ _

private lemma liftAux_comp_eq (s : Cone (Over.forget i ⋙ D)) {U V : 𝒰.I₀} {W : Scheme.{u}}
    (x : W ⟶ pullback (s.π.app (Over.mk (𝟙 i))) (𝒰.f U))
    (y : W ⟶ pullback (s.π.app (Over.mk (𝟙 i))) (𝒰.f V))
    (hxy : x ≫ pullback.fst _ _ = y ≫ pullback.fst _ _) :
    x ≫ liftAux D 𝒰 s U ≫ colimit.ι (functor D 𝒰) U =
      y ≫ liftAux D 𝒰 s V ≫ colimit.ι (functor D 𝒰) V :=
  hom_ext D 𝒰 fun j ↦ by
    simp only [Category.assoc, liftAux_π, reassoc_of% hxy]

/-- (Implementation) The lift of a cone over the members of `D` over `i` to the glued scheme,
glued from the lifts over the preimages of the members of the cover. -/
private noncomputable def lift (s : Cone (Over.forget i ⋙ D)) :
    s.pt ⟶ (gluingData D 𝒰).glued :=
  AlgebraicGeometry.Scheme.Cover.glueMorphisms (𝒰.pullback₁ (s.π.app (Over.mk (𝟙 i))))
    (fun U ↦ liftAux D 𝒰 s U ≫ colimit.ι (functor D 𝒰) U) fun _ _ ↦
      liftAux_comp_eq D 𝒰 s _ _ pullback.condition

private lemma lift_π (s : Cone (Over.forget i ⋙ D)) (j : Over i) :
    lift D 𝒰 s ≫ π D 𝒰 j = s.π.app j :=
  AlgebraicGeometry.Scheme.Cover.hom_ext (𝒰.pullback₁ (s.π.app (Over.mk (𝟙 i)))) _ _
    fun U ↦ (AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms_assoc _ _ _ U _).trans
      ((Category.assoc _ _ _).trans (liftAux_π D 𝒰 s U j))

/-- (Implementation) The glued scheme is the limit of the members of `D` over `i`. -/
private noncomputable def isLimit : IsLimit (cone D 𝒰) where
  lift := lift D 𝒰
  fac := lift_π D 𝒰
  uniq s _ hm := hom_ext D 𝒰 fun j ↦ (hm j).trans (lift_π D 𝒰 s j).symm

end AffineTransitionLimit

/-- A cofiltered diagram of schemes with affine transition maps has a limit. It is glued from the
affine limits `lim_j Dⱼ ×_{Dᵢ} U` over the affine opens `U` of any member `Dᵢ`. Stacks,
Lemma 32.2.1 (01YW). -/
instance hasLimit_of_isAffineHom [IsCofiltered I] : HasLimit D :=
  let i : I := IsCofiltered.nonempty.some
  have (U : (D.obj i).directedAffineCover.I₀) : IsAffine ((D.obj i).directedAffineCover.X U) :=
    U.property
  have : HasLimit (Over.forget i ⋙ D) :=
    ⟨⟨⟨_, AffineTransitionLimit.isLimit D (D.obj i).directedAffineCover⟩⟩⟩
  Functor.Initial.hasLimit_of_comp (Over.forget i)

end General

end TauCeti.AlgebraicGeometry.Scheme
