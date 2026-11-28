/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.Galois
public import TauCeti.AlgebraicGeometry.Sites.Etale.Pullback
public import TauCeti.FieldTheory.IsAlgClosed.Basic
public import TauCeti.FieldTheory.IsSepClosed
public import TauCeti.FieldTheory.RatFunc.PowerTower

/-!
# Pushforward functoriality and algebraic-closure comparisons

This file extends `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint` with:

* **Pushforward along scheme morphisms**: the fully faithful slice embedding `toOver`, lifting
  `Over.map`, `Over.mapId`, `Over.mapComp`, and `Over.mapCongr` via `mapCompToOver` to
  `GeometricPoint.map f`, `mapId`, `mapComp`, and `mapCongr`, together with the associativity and
  unit coherence laws (`mapComp_assoc`, `mapId_comp`, `comp_mapId`), and naturality of the
  pullback–stalk comparison `smallEtalePullbackCompSheafFiberIso` with respect to morphisms of
  geometric points.
* **Algebraic vs. separable closures**: `fromAlgClosure` and `algClosureToSepClosure`, showing that
  `Spec kbar ⟶ Spec ksep` is an isomorphism in `GeometricPoint S` if and only if the base field is
  perfect, while always inducing an isomorphism of points and étale stalks
  (`isIso_toPointFunctor_map`, `stalkIso`).

## References

* The Stacks Project, [Tag 03PO](https://stacks.math.columbia.edu/tag/03PO) and
  [Tag 04FN](https://stacks.math.columbia.edu/tag/04FN).
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme.GeometricPoint

section Map

/-- The fully faithful embedding sending a geometric point `(Ω, s)` of `S` to `Over.mk s.hom` in
`Over S`. -/
@[expose, simps]
noncomputable def toOver (S : Scheme.{u}) : GeometricPoint S ⥤ Over S where
  obj s := Over.mk s.hom
  map φ := Over.homMk φ.hom φ.w

/-- `toOver S` is fully faithful: morphisms of geometric points are morphisms of their underlying
spectra over `S`. -/
noncomputable def toOverFullyFaithful (S : Scheme.{u}) : (toOver S).FullyFaithful where
  preimage f := ⟨f.left, Over.w f⟩

instance (S : Scheme.{u}) : (toOver S).Full := (toOverFullyFaithful S).full

instance (S : Scheme.{u}) : (toOver S).Faithful := (toOverFullyFaithful S).faithful

/-- The underlying scheme morphism of a preimage under `toOver S` is `f.left`. -/
@[simp]
theorem toOver_preimage_hom {S : Scheme.{u}} {s₁ s₂ : GeometricPoint S}
    (f : (toOver S).obj s₁ ⟶ (toOver S).obj s₂) :
    ((toOver S).preimage f).hom = f.left :=
  congrArg Over.Hom.left ((toOver S).map_preimage f)

-- Exposed so `((map f).obj s).Ω`, `((map f).obj s).hom`, and `((map f).map φ).hom` unfold in
-- coherence statements.
/-- Pushforward of geometric points along a scheme morphism `f : X ⟶ Y`, lifting `Over.map f`
through `toOver`. -/
@[expose, simps! obj_Ω obj_hom map_hom]
noncomputable def map {X Y : Scheme.{u}} (f : X ⟶ Y) : GeometricPoint X ⥤ GeometricPoint Y where
  obj s := ⟨s.Ω, s.hom ≫ f⟩
  map φ := ⟨φ.hom, by simp⟩

/-- Natural isomorphism comparing geometric-point pushforward `map f` via `toOver` with slice
pushforward `Over.map f`. -/
noncomputable def mapCompToOver {X Y : Scheme.{u}} (f : X ⟶ Y) :
    map f ⋙ toOver Y ≅ toOver X ⋙ Over.map f :=
  NatIso.ofComponents
    (fun s ↦ Over.isoMk (Iso.refl (Spec (.of s.Ω))) (by dsimp [toOver, map]; simp))
    fun _ ↦ by
      ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The forward component of `mapCompToOver f` at `s` has the identity as underlying scheme
morphism. -/
@[simp]
theorem mapCompToOver_hom_app_left {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeometricPoint X) :
    ((mapCompToOver f).hom.app s).left = 𝟙 _ :=
  (rfl)

/-- The inverse component of `mapCompToOver f` at `s` has the identity as underlying scheme
morphism. -/
@[simp]
theorem mapCompToOver_inv_app_left {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeometricPoint X) :
    ((mapCompToOver f).inv.app s).left = 𝟙 _ :=
  (rfl)

/-- Pushforward along `𝟙 X` is naturally isomorphic to the identity functor, lifted from
`Over.mapId X`. -/
noncomputable def mapId (X : Scheme.{u}) : map (𝟙 X) ≅ 𝟭 (GeometricPoint X) :=
  Functor.fullyFaithfulCancelRight (toOver X)
    (mapCompToOver (𝟙 X) ≪≫ Functor.isoWhiskerLeft (toOver X) (Over.mapId X))

/-- The component of `mapId X` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapId_hom_app_hom {X : Scheme.{u}} (s : GeometricPoint X) :
    ((mapId X).hom.app s).hom = 𝟙 (Spec (.of s.Ω)) := by
  rw [mapId, Functor.fullyFaithfulCancelRight_hom_app, toOver_preimage_hom]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Over.comp_left, mapCompToOver_hom_app_left, Over.mapId_hom_app_left]
  rfl

/-- The inverse component of `mapId X` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapId_inv_app_hom {X : Scheme.{u}} (s : GeometricPoint X) :
    ((mapId X).inv.app s).hom = 𝟙 (Spec (.of s.Ω)) := by
  rw [mapId, Functor.fullyFaithfulCancelRight_inv_app, toOver_preimage_hom]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Over.comp_left, Over.mapId_inv_app_left, mapCompToOver_inv_app_left]
  rfl

/-- Pushforward along a composite `f ≫ g` is naturally isomorphic to the composite of the
pushforwards, lifted from `Over.mapComp f g`. -/
noncomputable def mapComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) ≅ map f ⋙ map g :=
  Functor.fullyFaithfulCancelRight (toOver Z)
    (mapCompToOver (f ≫ g) ≪≫
      Functor.isoWhiskerLeft (toOver X) (Over.mapComp f g) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (mapCompToOver f).symm (Over.map g) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (map f) (mapCompToOver g).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The component of `mapComp f g` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapComp_hom_app_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : GeometricPoint X) :
    ((mapComp f g).hom.app s).hom = 𝟙 (Spec (.of s.Ω)) := by
  rw [mapComp, Functor.fullyFaithfulCancelRight_hom_app, toOver_preimage_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Over.comp_left, Over.id_left,
    Over.map_map_left, mapCompToOver_hom_app_left, mapCompToOver_inv_app_left,
    Over.mapComp_hom_app_left, Category.id_comp]
  rfl

/-- The inverse component of `mapComp f g` at `s` has the identity as underlying scheme
morphism. -/
@[simp]
theorem mapComp_inv_app_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : GeometricPoint X) :
    ((mapComp f g).inv.app s).hom = 𝟙 (Spec (.of s.Ω)) := by
  rw [mapComp, Functor.fullyFaithfulCancelRight_inv_app, toOver_preimage_hom]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Over.comp_left, Over.id_left,
    Over.map_map_left, mapCompToOver_hom_app_left, mapCompToOver_inv_app_left,
    Over.mapComp_inv_app_left, Category.comp_id]
  rfl

/-- Equal scheme morphisms induce naturally isomorphic pushforward functors, lifted from
`Over.mapCongr`. -/
noncomputable def mapCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) : map f ≅ map g :=
  Functor.fullyFaithfulCancelRight (toOver Y)
    (mapCompToOver f ≪≫
      Functor.isoWhiskerLeft (toOver X) (Over.mapCongr f g h) ≪≫
      (mapCompToOver g).symm)

/-- The component of `mapCongr h` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapCongr_hom_app_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (s : GeometricPoint X) :
    ((mapCongr h).hom.app s).hom = 𝟙 (Spec (.of s.Ω)) := by
  rw [mapCongr, Functor.fullyFaithfulCancelRight_hom_app, toOver_preimage_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Over.comp_left, mapCompToOver_hom_app_left,
    Over.mapCongr_hom_app_left, mapCompToOver_inv_app_left]
  rfl

/-- The inverse component of `mapCongr h` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapCongr_inv_app_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (s : GeometricPoint X) :
    ((mapCongr h).inv.app s).hom = 𝟙 (Spec (.of s.Ω)) := by
  rw [mapCongr, Functor.fullyFaithfulCancelRight_inv_app, toOver_preimage_hom]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Over.comp_left, mapCompToOver_hom_app_left,
    Over.mapCongr_inv_app_left, mapCompToOver_inv_app_left]
  rfl

/-- Associativity coherence for `mapComp`. -/
theorem mapComp_assoc {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (s : GeometricPoint W) :
    (mapComp (f ≫ g) h).hom.app s ≫ (map h).map ((mapComp f g).hom.app s) =
      (mapCongr (Category.assoc f g h)).hom.app s ≫
        (mapComp f (g ≫ h)).hom.app s ≫ (mapComp g h).hom.app ((map f).obj s) := by
  ext : 1
  simp only [comp_hom, map_map_hom, mapComp_hom_app_hom, mapCongr_hom_app_hom]
  -- `((map f).obj s).Ω` is definitionally `s.Ω` in the implicit target object of `𝟙`.
  rfl

/-- Left unit coherence for `mapId` and `mapComp`. -/
theorem mapId_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeometricPoint X) :
    (mapComp (𝟙 X) f).hom.app s ≫ (map f).map ((mapId X).hom.app s) =
      (mapCongr (Category.id_comp f)).hom.app s := by
  ext : 1
  exact (comp_hom _ _).trans <|
    (congrArg₂ (· ≫ ·) (mapComp_hom_app_hom (𝟙 X) f s)
      ((map_map_hom f ((mapId X).hom.app s)).trans (mapId_hom_app_hom s))).trans <|
    (Category.comp_id _).trans (mapCongr_hom_app_hom (Category.id_comp f) s).symm

/-- Right unit coherence for `mapComp` and `mapId`. -/
theorem comp_mapId {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeometricPoint X) :
    (mapComp f (𝟙 Y)).hom.app s ≫ (mapId Y).hom.app ((map f).obj s) =
      (mapCongr (Category.comp_id f)).hom.app s := by
  ext : 1
  simp only [comp_hom, mapComp_hom_app_hom, mapId_hom_app_hom, mapCongr_hom_app_hom]
  -- `((map f).obj s).Ω` is definitionally `s.Ω` in the implicit target object of `𝟙`.
  rfl

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (A : Type*) [Category* A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
  [(f.smallEtalePushforward A).IsRightAdjoint]

private theorem smallEtalePullbackCompSheafFiberIso_inv_comp_stalkIso_hom
    {s₁ s₂ : GeometricPoint X} (φ : s₁ ⟶ s₂) :
    (f.smallEtalePullbackCompSheafFiberIso A s₂.hom).inv ≫
        Functor.whiskerLeft (f.smallEtalePullback A) (stalkIso φ (A := A)).hom =
      (stalkIso ((map f).map φ) (A := A)).hom ≫
        (f.smallEtalePullbackCompSheafFiberIso A s₁.hom).inv := by
  ext G
  refine (pointSmallEtale (s₂.hom ≫ f)).presheafFiber_hom_ext fun V y ↦ ?_
  have h1 := congrArg (· ≫ (stalkIso φ (A := A)).hom.app ((f.smallEtalePullback A).obj G))
    ((pointSmallEtale s₂.hom).toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app
      f.smallEtaleBaseChange (f.pointSmallEtaleFiberCompIso s₂.hom) A G V y)
  have h2 := toPresheafFiber_toPointFunctor_map_sheafFiber_app φ
    ((f.smallEtalePullback A).obj G) (f.smallEtaleBaseChange.obj V)
    ((f.pointSmallEtaleFiberCompIso s₂.hom).inv.app V y)
  have h3 := toPresheafFiber_toPointFunctor_map_sheafFiber_app ((map f).map φ) G V y
  rw [← stalkIso_hom] at h2 h3
  have h4 := (pointSmallEtale s₁.hom).toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app
    f.smallEtaleBaseChange (f.pointSmallEtaleFiberCompIso s₁.hom) A G V
    ((Over.homMk ((map f).map φ).hom ((map f).map φ).w :
      Over.mk (s₁.hom ≫ f) ⟶ Over.mk (s₂.hom ≫ f)) ≫ y)
  have h5 :
      (Over.homMk φ.hom φ.w : Over.mk s₁.hom ⟶ Over.mk s₂.hom) ≫
          (f.pointSmallEtaleFiberCompIso s₂.hom).inv.app V y =
        (f.pointSmallEtaleFiberCompIso s₁.hom).inv.app V
          ((Over.homMk ((map f).map φ).hom ((map f).map φ).w :
            Over.mk (s₁.hom ≫ f) ⟶ Over.mk (s₂.hom ≫ f)) ≫ y) := by
    apply Over.OverMorphism.ext
    refine Eq.trans (congrArg (φ.hom ≫ ·)
      (Hom.pointSmallEtaleFiberCompIso_inv_app_left f s₂.hom V y)) ?_
    refine Eq.trans ?_ (Hom.pointSmallEtaleFiberCompIso_inv_app_left f s₁.hom V _).symm
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans <|
        (congrArg (φ.hom ≫ ·) (pullback.lift_fst _ _ _)).trans <|
          (pullback.lift_fst _ _ _).symm
    · exact (Category.assoc _ _ _).trans <|
        (congrArg (φ.hom ≫ ·) (pullback.lift_snd _ _ _)).trans <|
          φ.w.trans (pullback.lift_snd _ _ _).symm
  let unitV := ((f.smallEtaleBaseChange.sheafAdjunctionContinuous A
    (smallEtaleTopology Y) (smallEtaleTopology X)).unit.app G).hom.app (op V)
  let stalkMap := (stalkIso ((map f).map φ) (A := A)).hom.app G
  let inv₁ := (f.smallEtalePullbackCompSheafFiberIso A s₁.hom).inv.app G
  refine ((Category.assoc _ _ _).symm).trans ?_
  refine h1.trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (unitV ≫ ·) h2).trans ?_
  refine (congrArg (fun x ↦ unitV ≫ (pointSmallEtale s₁.hom).toPresheafFiber
    (f.smallEtaleBaseChange.obj V) x ((f.smallEtalePullback A).obj G).obj) h5).trans ?_
  refine h4.symm.trans ?_
  exact (congrArg (· ≫ inv₁) h3.symm).trans (Category.assoc _ stalkMap inv₁)

/-- **Naturality of the pullback–stalk comparison in morphisms of geometric points.** For
`f : X ⟶ Y` and `φ : s₁ ⟶ s₂` in `GeometricPoint X`, pulling back and applying `stalkIso φ`
agrees, under the two stalk comparisons `smallEtalePullbackCompSheafFiberIso`, with applying
`stalkIso ((map f).map φ)`. -/
theorem isoWhiskerLeft_smallEtalePullback_stalkIso_trans_smallEtalePullbackCompSheafFiberIso
    {s₁ s₂ : GeometricPoint X} (φ : s₁ ⟶ s₂) :
    Functor.isoWhiskerLeft (f.smallEtalePullback A) (stalkIso φ (A := A)) ≪≫
        f.smallEtalePullbackCompSheafFiberIso A s₁.hom =
      f.smallEtalePullbackCompSheafFiberIso A s₂.hom ≪≫
        stalkIso ((map f).map φ) (A := A) := by
  refine Iso.ext (NatTrans.ext (funext fun G ↦ ?_))
  let hom₁ := (f.smallEtalePullbackCompSheafFiberIso A s₁.hom).hom.app G
  let hom₂ := (f.smallEtalePullbackCompSheafFiberIso A s₂.hom).hom.app G
  let inv₁ := (f.smallEtalePullbackCompSheafFiberIso A s₁.hom).inv.app G
  let stalkφ := (stalkIso φ (A := A)).hom.app ((f.smallEtalePullback A).obj G)
  let stalkMap := (stalkIso ((map f).map φ) (A := A)).hom.app G
  have hinv := NatTrans.congr_app
    (smallEtalePullbackCompSheafFiberIso_inv_comp_stalkIso_hom f A φ) G
  have h0 :
      stalkφ ≫ hom₁ =
        (hom₂ ≫ ((f.smallEtalePullbackCompSheafFiberIso A s₂.hom).inv ≫
          Functor.whiskerLeft (f.smallEtalePullback A) (stalkIso φ (A := A)).hom).app G) ≫ hom₁ :=
    (Category.id_comp (stalkφ ≫ hom₁)).symm.trans <|
      (congrArg (· ≫ (stalkφ ≫ hom₁))
        (Iso.hom_inv_id_app (f.smallEtalePullbackCompSheafFiberIso A s₂.hom) G).symm).trans <|
          (Category.assoc _ _ _).trans <|
            (congrArg (hom₂ ≫ ·) (Category.assoc _ _ _).symm).trans <|
              (Category.assoc _ _ _).symm
  refine h0.trans ?_
  refine (congrArg (fun x ↦ (hom₂ ≫ x) ≫ hom₁) hinv).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (hom₂ ≫ ·) (Category.assoc stalkMap inv₁ hom₁)).trans ?_
  exact (congrArg (fun x ↦ hom₂ ≫ (stalkMap ≫ x))
    (Iso.inv_hom_id_app (f.smallEtalePullbackCompSheafFiberIso A s₁.hom) G)).trans
      (congrArg (hom₂ ≫ ·) (Category.comp_id stalkMap))

/-- Natural-transformation form of
`isoWhiskerLeft_smallEtalePullback_stalkIso_trans_smallEtalePullbackCompSheafFiberIso`. -/
@[reassoc]
theorem whiskerLeft_smallEtalePullback_stalkIso_hom_comp_smallEtalePullbackCompSheafFiberIso_hom
    {s₁ s₂ : GeometricPoint X} (φ : s₁ ⟶ s₂) :
    Functor.whiskerLeft (f.smallEtalePullback A) (stalkIso φ (A := A)).hom ≫
        (f.smallEtalePullbackCompSheafFiberIso A s₁.hom).hom =
      (f.smallEtalePullbackCompSheafFiberIso A s₂.hom).hom ≫
        (stalkIso ((map f).map φ) (A := A)).hom :=
  congrArg Iso.hom
    (isoWhiskerLeft_smallEtalePullback_stalkIso_trans_smallEtalePullbackCompSheafFiberIso f A φ)

/-- Component form at an étale sheaf `F` of
`whiskerLeft_smallEtalePullback_stalkIso_hom_comp_smallEtalePullbackCompSheafFiberIso_hom`. -/
@[reassoc]
theorem stalkIso_hom_app_smallEtalePullback_comp_smallEtalePullbackCompSheafFiberIso_hom_app
    {s₁ s₂ : GeometricPoint X} (φ : s₁ ⟶ s₂) (F : Sheaf (Scheme.smallEtaleTopology Y) A) :
    (stalkIso φ (A := A)).hom.app ((f.smallEtalePullback A).obj F) ≫
        (f.smallEtalePullbackCompSheafFiberIso A s₁.hom).hom.app F =
      (f.smallEtalePullbackCompSheafFiberIso A s₂.hom).hom.app F ≫
        (stalkIso ((map f).map φ) (A := A)).hom.app F :=
  NatTrans.congr_app
    (whiskerLeft_smallEtalePullback_stalkIso_hom_comp_smallEtalePullbackCompSheafFiberIso_hom
      f A φ) F

end Pullback

end Map

section Closures

variable {S : Scheme.{u}}

/-- The canonical morphism from the algebraically closed geometric point over `s` to `s`,
exhibiting that algebraically closed points give the same stalks as separably closed ones. -/
noncomputable def fromAlgClosure (s : GeometricPoint S) :
    ofOver s.hom (AlgebraicClosure s.Ω) ⟶ s :=
  homOfRingHom (algebraMap s.Ω (AlgebraicClosure s.Ω)) rfl

/-- The ring homomorphism underlying `fromAlgClosure s` is
`algebraMap s.Ω (AlgebraicClosure s.Ω)`. -/
@[simp]
theorem Hom.ringHom_fromAlgClosure (s : GeometricPoint S) :
    (fromAlgClosure s).ringHom = algebraMap s.Ω (AlgebraicClosure s.Ω) :=
  Hom.ringHom_homOfRingHom _ _

/-- `fromAlgClosure s` is an isomorphism in `GeometricPoint S` if and only if `s.Ω` is already
algebraically closed (whereas `(toPointFunctor S).map (fromAlgClosure s)` is always an isomorphism
by `isIso_toPointFunctor_map`). -/
theorem isIso_fromAlgClosure_iff (s : GeometricPoint S) :
    IsIso (fromAlgClosure s) ↔ IsAlgClosed s.Ω := by
  rw [Hom.isIso_iff_ringHom_surjective, Hom.ringHom_fromAlgClosure,
    ← IsAlgClosed.iff_algebraMap_surjective s.Ω (AlgebraicClosure s.Ω)]

/-- For a separably closed separable extension `Ω` of a field `K`,
`fromAlgClosure (ofOver a Ω)` is an isomorphism in `GeometricPoint S` if and only if `K` is
perfect. -/
theorem isIso_fromAlgClosure_ofOver_iff_perfectField {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra K Ω] [Algebra.IsSeparable K Ω] :
    IsIso (fromAlgClosure (ofOver a Ω)) ↔ PerfectField K := by
  rw [isIso_fromAlgClosure_iff]
  exact IsSepClosed.isAlgClosed_iff_perfectField K Ω

/-- The canonical morphism from `ofOver a (AlgebraicClosure K)` to
`ofOver a (SeparableClosure K)`. It is an isomorphism in `GeometricPoint S` if and only if `K` is
perfect (`isIso_algClosureToSepClosure_iff_perfectField`), while its image under `toPointFunctor S`
is always an isomorphism (`isIso_toPointFunctor_map`). -/
noncomputable def algClosureToSepClosure {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    ofOver a (AlgebraicClosure K) ⟶ ofOver a (SeparableClosure K) :=
  homOfAlgHom a (IsScalarTower.toAlgHom K (SeparableClosure K) (AlgebraicClosure K))

/-- The ring homomorphism underlying `algClosureToSepClosure a` is the canonical inclusion
`SeparableClosure K →+* AlgebraicClosure K`. -/
@[simp]
theorem Hom.ringHom_algClosureToSepClosure {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    (algClosureToSepClosure a).ringHom =
      algebraMap (SeparableClosure K) (AlgebraicClosure K) :=
  Hom.ringHom_homOfAlgHom _ _

/-- `algClosureToSepClosure a` is an isomorphism in `GeometricPoint S` if and only if `K` is
perfect. -/
theorem isIso_algClosureToSepClosure_iff_perfectField {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ S) :
    IsIso (algClosureToSepClosure a) ↔ PerfectField K := by
  rw [Hom.isIso_iff_ringHom_surjective, Hom.ringHom_algClosureToSepClosure]
  have : Algebra.IsAlgebraic (SeparableClosure K) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K) (A := AlgebraicClosure K)
  rw [← IsAlgClosed.iff_algebraMap_surjective (SeparableClosure K) (AlgebraicClosure K),
    IsSepClosed.isAlgClosed_iff_perfectField K (SeparableClosure K)]

/-- For any field `K` and any `a : Spec (.of (RatFunc K)) ⟶ S`, the morphism
`algClosureToSepClosure a` is an isomorphism in `GeometricPoint S` if and only if `K` has
characteristic zero (whereas `(toPointFunctor S).map (algClosureToSepClosure a)` is always an
isomorphism by `isIso_toPointFunctor_map`). -/
theorem isIso_algClosureToSepClosure_ratFunc_iff {K : Type u} [Field K]
    (a : Spec (.of (RatFunc K)) ⟶ S) :
    IsIso (algClosureToSepClosure a) ↔ CharZero K :=
  (isIso_algClosureToSepClosure_iff_perfectField a).trans
    (TauCeti.RatFunc.perfectField_iff_charZero K)

end Closures

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
