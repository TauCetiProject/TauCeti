/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Stalk
import TauCeti.AlgebraicGeometry.FiniteEtale.BaseChange
import TauCeti.AlgebraicGeometry.FiniteEtale.Gluing
import TauCeti.AlgebraicGeometry.Limits.FinitePresentation
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Section
import TauCeti.RingTheory.Etale.DirectLimit

/-!
# Spreading out finite étale schemes from stalks and cofiltered limits

For a scheme `X`, an open `U : X.Opens`, and `s : X`, this file proves stalk object descent
(`exists_pullback_fromSpecStalkOfMem_iso`), cofiltered affine-transition limit descent
(`exists_hom_pullback_of_isLimit`, `exists_pullback_map_eq_of_isLimit`,
`exists_iso_pullback_of_isLimit`), binary open gluing (`exists_sup_of_iso_inf`), and spreading of
finite étale extensions from `Spec (X.presheaf.stalk s)` (`exists_spread_fromSpecStalk`).

## References

* [The Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4) (limits of finite
  étale schemes).
* [The Stacks Project, Lemma 32.10.1](https://stacks.math.columbia.edu/tag/01ZM) (descent of
  morphisms and isomorphisms along cofiltered limits).
* [The Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH) (gluing schemes
  along opens).
* [The Stacks Project, Lemma 32.20.3](https://stacks.math.columbia.edu/tag/0BQ5) (spreading out
  from the spectrum of a local ring).
* [The Stacks Project, Lemma 32.20.4](https://stacks.math.columbia.edu/tag/0EY3) (extending
  finite étale covers across open subsets).
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

/-- Every finite étale scheme over `Spec (X.presheaf.stalk s)` descends to a finite étale scheme
over some affine open neighborhood `W₀ : X.AffineOpenNhds s`. -/
@[stacks 01Z4 "for finite étale schemes"]
theorem exists_pullback_fromSpecStalkOfMem_iso {X : Scheme.{u}} (s : X)
    (Ys : FiniteEtaleScheme (Spec (X.presheaf.stalk s))) :
    ∃ (W₀ : X.AffineOpenNhds s) (YW₀ : FiniteEtaleScheme W₀.opens.toScheme),
      Nonempty ((pullback (W₀.opens.fromSpecStalkOfMem s W₀.mem)).obj YW₀ ≅ Ys) := by
  let L := Ring.DirectLimit (X.stalkDirectSystemObj s) (fun U V h ↦ X.stalkDirectSystemMap s U V h)
  let φ : CommRingCat.of L ≅ X.presheaf.stalk s := (X.directLimitRingEquivStalk s).toCommRingCatIso
  let YL := (pullback (Spec.map φ.inv)).obj Ys
  let AL_op := (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of L)).inverse.obj YL
  obtain ⟨W₀, AW₀, ⟨eAW₀⟩⟩ :=
    Ring.DirectLimit.finiteEtale_essSurj (f := X.stalkDirectSystemMap s) AL_op.unop
  let R₀ := X.stalkDirectSystemObj s W₀
  let := (Ring.DirectLimit.of _ (X.stalkDirectSystemMap s · · ·) W₀).toAlgebra
  let Z₀ := (spec Γ(X, W₀.opens)).obj (op AW₀)
  have heL : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ L)))).obj Z₀ ≅ YL :=
    (specCompPullbackIso R₀ L).app (op AW₀) ≪≫ (spec (.of L)).mapIso (Iso.op eAW₀).symm ≪≫
      eqToIso (by simp [AL_op]) ≪≫
      (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of L)).counitIso.app YL
  have hgerm : Spec.map φ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ L)) =
      W₀.opens.fromSpecStalkOfMem s W₀.mem ≫ W₀.opens.toSpecΓ := by
    rw [← Spec.map_comp, Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]
    congr 1; ext x; exact X.directLimitRingEquivStalk_of s W₀ x
  have hφ : Spec.map φ.hom ≫ Spec.map φ.inv = 𝟙 _ := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact ⟨W₀, (pullback W₀.opens.toSpecΓ).obj Z₀,
    ⟨((pullbackComp (W₀.opens.fromSpecStalkOfMem s W₀.mem) W₀.opens.toSpecΓ).app Z₀).symm ≪≫
      (pullbackCompIsoOfEq (Spec.map φ.hom) _ _ hgerm).symm.app Z₀ ≪≫
      (pullback (Spec.map φ.hom)).mapIso heL ≪≫
      (pullbackCompIsoOfEq (Spec.map φ.hom) (Spec.map φ.inv) (𝟙 _) hφ).app Ys ≪≫
      pullbackId.app Ys⟩⟩

@[reassoc]
private theorem pullback_map_left_fst {S T : Scheme.{u}} (f : T ⟶ S)
    {Y₁ Y₂ : FiniteEtaleScheme S} (g : Y₁ ⟶ Y₂) :
    ((pullback f).map g).hom.left ≫ Limits.pullback.fst Y₂.obj.hom f =
      Limits.pullback.fst Y₁.obj.hom f ≫ g.hom.left :=
  (congrArg (· ≫ Limits.pullback.fst Y₂.obj.hom f)
    (Over.pullback_map_left f Y₁.obj)).trans (Limits.pullback.lift_fst _ _ _)

private theorem pullbackCompIsoOfEq_conj_hom_left_fst {U T S : Scheme.{u}}
    {f : U ⟶ T} {g : T ⟶ S} {fg : U ⟶ S} (h : f ≫ g = fg)
    {Y₁ Y₂ : FiniteEtaleScheme S} (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    ((pullbackCompIsoOfEq f g fg h).inv.app Y₁ ≫ (pullback f).map β ≫
        (pullbackCompIsoOfEq f g fg h).hom.app Y₂).hom.left ≫
      Limits.pullback.fst Y₂.obj.hom fg =
      Limits.pullback.map Y₁.obj.hom fg Y₁.obj.hom g (𝟙 _) f (𝟙 _) (by simp) (by simp [h]) ≫
        β.hom.left ≫ Limits.pullback.fst Y₂.obj.hom g := by
  have hcomp :
      ((pullbackCompIsoOfEq f g fg h).inv.app Y₁ ≫ (pullback f).map β ≫
        (pullbackCompIsoOfEq f g fg h).hom.app Y₂).hom.left =
      ((pullbackCompIsoOfEq f g fg h).inv.app Y₁).hom.left ≫
        ((pullback f).map β).hom.left ≫
        ((pullbackCompIsoOfEq f g fg h).hom.app Y₂).hom.left := by
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      Over.comp_left, Over.comp_left]
  have h1 : ((pullback f).map β).hom.left ≫
        ((pullbackCompIsoOfEq f g fg h).hom.app Y₂).hom.left ≫ Limits.pullback.fst Y₂.obj.hom fg =
      Limits.pullback.fst ((pullback g).obj Y₁).obj.hom f ≫
        β.hom.left ≫ Limits.pullback.fst Y₂.obj.hom g :=
    (congrArg (((pullback f).map β).hom.left ≫ ·)
      (pullbackCompIsoOfEq_hom_app_hom_left_fst h Y₂)).trans
      (pullback_map_left_fst_assoc f β (Limits.pullback.fst Y₂.obj.hom g))
  have h2 : ((pullbackCompIsoOfEq f g fg h).inv.app Y₁).hom.left ≫
        ((pullback f).map β).hom.left ≫
        ((pullbackCompIsoOfEq f g fg h).hom.app Y₂).hom.left ≫ Limits.pullback.fst Y₂.obj.hom fg =
      Limits.pullback.map Y₁.obj.hom fg Y₁.obj.hom g (𝟙 _) f (𝟙 _) (by simp) (by simp [h]) ≫
        β.hom.left ≫ Limits.pullback.fst Y₂.obj.hom g :=
    (congrArg (((pullbackCompIsoOfEq f g fg h).inv.app Y₁).hom.left ≫ ·)
      ((Category.assoc _ _ _).trans h1)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ β.hom.left ≫ Limits.pullback.fst Y₂.obj.hom g)
          (pullbackCompIsoOfEq_inv_app_hom_left_fst h Y₁)))
  exact (congrArg (· ≫ Limits.pullback.fst Y₂.obj.hom fg) hcomp).trans
    ((Category.assoc _ _ _).trans h2)

section LimitSpreading

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Limits.Cone D)

private theorem pullback_hom_ext {S T : Scheme.{u}} {f : T ⟶ S} {X : FiniteEtaleScheme T}
    {Y : FiniteEtaleScheme S} {v₁ v₂ : X ⟶ (pullback f).obj Y}
    (h : v₁.hom.left ≫ Limits.pullback.fst Y.obj.hom f =
      v₂.hom.left ≫ Limits.pullback.fst Y.obj.hom f) : v₁ = v₂ :=
  ObjectProperty.hom_ext _ <| Over.pullback_hom_ext h

@[reassoc]
private theorem pullbackSymmetry_comp_pullbackSymmetry {A B S : Scheme.{u}}
    (p : A ⟶ S) (q : B ⟶ S) :
    (Limits.pullbackSymmetry p q).hom ≫ (Limits.pullbackSymmetry q p).hom = 𝟙 _ := by
  apply Limits.pullback.hom_ext <;> simp

private theorem pullbackSymmetry_conj_snd {T S : Scheme.{u}} (f : T ⟶ S)
    {Y₁ Y₂ : FiniteEtaleScheme S}
    (b : Limits.pullback f Y₁.obj.hom ⟶ Limits.pullback f Y₂.obj.hom)
    (hb : b ≫ Limits.pullback.fst f Y₂.obj.hom = Limits.pullback.fst f Y₁.obj.hom) :
    ((Limits.pullbackSymmetry Y₁.obj.hom f).hom ≫ b ≫ (Limits.pullbackSymmetry f Y₂.obj.hom).hom) ≫
        Limits.pullback.snd Y₂.obj.hom f =
      Limits.pullback.snd Y₁.obj.hom f := by
  rw [Category.assoc, Category.assoc, Limits.pullbackSymmetry_hom_comp_snd, hb,
    Limits.pullbackSymmetry_hom_comp_fst]

private theorem pullbackSymmetry_conj_fst {T S : Scheme.{u}} (f : T ⟶ S)
    {Y₁ Y₂ : FiniteEtaleScheme S}
    (g : (pullback f).obj Y₁ ⟶ (pullback f).obj Y₂) :
    ((Limits.pullbackSymmetry f Y₁.obj.hom).hom ≫ g.hom.left ≫
        (Limits.pullbackSymmetry Y₂.obj.hom f).hom) ≫
        Limits.pullback.fst f Y₂.obj.hom =
      Limits.pullback.fst f Y₁.obj.hom := by
  have hw : g.hom.left ≫ Limits.pullback.snd Y₂.obj.hom f = Limits.pullback.snd Y₁.obj.hom f :=
    Over.w g.hom
  have h1 : g.hom.left ≫ (Limits.pullbackSymmetry Y₂.obj.hom f).hom ≫
      Limits.pullback.fst f Y₂.obj.hom = Limits.pullback.snd Y₁.obj.hom f :=
    (congrArg (g.hom.left ≫ ·) (Limits.pullbackSymmetry_hom_comp_fst Y₂.obj.hom f)).trans hw
  exact (Category.assoc _ _ _).trans ((congrArg ((Limits.pullbackSymmetry f Y₁.obj.hom).hom ≫ ·)
    ((Category.assoc _ _ _).trans h1)).trans (Limits.pullbackSymmetry_hom_comp_snd f Y₁.obj.hom))

private theorem pullbackSymmetry_conj_fst_eq_snd {T S : Scheme.{u}} (f : T ⟶ S)
    {Y₁ Y₂ : FiniteEtaleScheme S}
    (b : Limits.pullback f Y₁.obj.hom ⟶ Limits.pullback f Y₂.obj.hom) :
    ((Limits.pullbackSymmetry Y₁.obj.hom f).hom ≫ b ≫
        (Limits.pullbackSymmetry f Y₂.obj.hom).hom) ≫
        Limits.pullback.fst Y₂.obj.hom f =
      (Limits.pullbackSymmetry Y₁.obj.hom f).hom ≫ b ≫ Limits.pullback.snd f Y₂.obj.hom :=
  (Category.assoc _ _ _).trans (congrArg ((Limits.pullbackSymmetry Y₁.obj.hom f).hom ≫ ·)
    ((Category.assoc b _ _).trans
      (congrArg (b ≫ ·) (Limits.pullbackSymmetry_hom_comp_fst f Y₂.obj.hom))))

private theorem pullbackSymmetry_conj_inv_eq_id {A S : Scheme.{u}} (f : A ⟶ S)
    {Y₁ Y₂ : FiniteEtaleScheme S}
    {g : ((pullback f).obj Y₁).obj.left ⟶ ((pullback f).obj Y₂).obj.left}
    {h : ((pullback f).obj Y₂).obj.left ⟶ ((pullback f).obj Y₁).obj.left}
    (hgh : g ≫ h = 𝟙 _) :
    ((Limits.pullbackSymmetry f Y₁.obj.hom).hom ≫ g ≫
        (Limits.pullbackSymmetry Y₂.obj.hom f).hom) ≫
      ((Limits.pullbackSymmetry f Y₂.obj.hom).hom ≫ h ≫
        (Limits.pullbackSymmetry Y₁.obj.hom f).hom) = 𝟙 _ := by
  let s₁ := (Limits.pullbackSymmetry f Y₁.obj.hom).hom
  let s₂ := (Limits.pullbackSymmetry Y₂.obj.hom f).hom
  let s₃ := (Limits.pullbackSymmetry f Y₂.obj.hom).hom
  let s₄ := (Limits.pullbackSymmetry Y₁.obj.hom f).hom
  calc (s₁ ≫ g ≫ s₂) ≫ (s₃ ≫ h ≫ s₄)
    _ = s₁ ≫ (g ≫ s₂) ≫ (s₃ ≫ h ≫ s₄) := Category.assoc _ _ _
    _ = s₁ ≫ g ≫ s₂ ≫ s₃ ≫ h ≫ s₄ := congrArg (s₁ ≫ ·) (Category.assoc g s₂ (s₃ ≫ h ≫ s₄))
    _ = s₁ ≫ g ≫ (s₂ ≫ s₃) ≫ h ≫ s₄ :=
        congrArg (fun k ↦ s₁ ≫ g ≫ k) (Category.assoc s₂ s₃ (h ≫ s₄)).symm
    _ = s₁ ≫ g ≫ 𝟙 _ ≫ h ≫ s₄ :=
        congrArg (fun k ↦ s₁ ≫ g ≫ k ≫ h ≫ s₄) (pullbackSymmetry_comp_pullbackSymmetry _ _)
    _ = s₁ ≫ g ≫ h ≫ s₄ := congrArg (fun k ↦ s₁ ≫ g ≫ k) (Category.id_comp _)
    _ = s₁ ≫ 𝟙 _ ≫ s₄ :=
        congrArg (s₁ ≫ ·) ((Category.assoc g h s₄).symm.trans (congrArg (· ≫ s₄) hgh))
    _ = s₁ ≫ s₄ := congrArg (s₁ ≫ ·) (Category.id_comp s₄)
    _ = 𝟙 _ := pullbackSymmetry_comp_pullbackSymmetry _ _

@[reassoc]
private theorem pullback_map_pullbackSymmetry {A B S Z : Scheme.{u}} {m : A ⟶ B}
    {g : B ⟶ S} {mg : A ⟶ S} (h : m ≫ g = mg) (p : Z ⟶ S) :
    Limits.pullback.map p mg p g (𝟙 Z) m (𝟙 S) (by simp) (by simp [h]) ≫
        (Limits.pullbackSymmetry p g).hom =
      (Limits.pullbackSymmetry p mg).hom ≫
        Limits.pullback.map mg p g p m (𝟙 Z) (𝟙 S) (by simp [h]) (by simp) := by
  apply Limits.pullback.hom_ext <;> simp

private theorem exists_hom_pullback_of_isLimit_aux [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : Limits.IsLimit c) {i₀ : I}
    (Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀))
    (α : (pullback (c.π.app i₀)).obj Y₁ ⟶ (pullback (c.π.app i₀)).obj Y₂) :
    ∃ (j : I) (fj : j ⟶ i₀)
      (b : Limits.pullback (D.map fj) Y₁.obj.hom ⟶ Limits.pullback (D.map fj) Y₂.obj.hom)
      (hb₁ : b ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _),
      let β : (pullback (D.map fj)).obj Y₁ ⟶ (pullback (D.map fj)).obj Y₂ :=
        (finiteEtaleSchemeProperty (D.obj j)).homMk
          (Over.homMk ((Limits.pullbackSymmetry _ _).hom ≫ b ≫ (Limits.pullbackSymmetry _ _).hom)
            (pullbackSymmetry_conj_snd (D.map fj) b hb₁))
      (pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).inv.app Y₁ ≫
        (pullback (c.π.app j)).map β ≫
        (pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).hom.app Y₂ = α ∧
      Limits.pullback.map (c.π.app i₀) Y₁.obj.hom (D.map fj) Y₁.obj.hom (c.π.app j) (𝟙 _) (𝟙 _)
          (by simp) (by simp) ≫ b =
        ((Limits.pullbackSymmetry _ _).hom ≫ α.hom.left ≫ (Limits.pullbackSymmetry _ _).hom) ≫
          Limits.pullback.map (c.π.app i₀) Y₂.obj.hom (D.map fj) Y₂.obj.hom (c.π.app j)
            (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  have : QuasiCompact Y₁.obj.hom := inferInstance
  have : QuasiSeparated Y₁.obj.hom := inferInstance
  have : LocallyOfFinitePresentation Y₂.obj.hom := inferInstance
  let a : Limits.pullback (c.π.app i₀) Y₁.obj.hom ⟶ Limits.pullback (c.π.app i₀) Y₂.obj.hom :=
    (Limits.pullbackSymmetry _ _).hom ≫ α.hom.left ≫ (Limits.pullbackSymmetry _ _).hom
  have ha : a ≫ Limits.pullback.fst (c.π.app i₀) Y₂.obj.hom =
      Limits.pullback.fst (c.π.app i₀) Y₁.obj.hom :=
    pullbackSymmetry_conj_fst (c.π.app i₀) α
  obtain ⟨j, fj, b, hb₁, hb₂⟩ := hc.exists_pullbackMap_comp_eq a ha
  refine ⟨j, fj, b, hb₁, pullback_hom_ext ?_, hb₂⟩
  let β : (pullback (D.map fj)).obj Y₁ ⟶ (pullback (D.map fj)).obj Y₂ :=
    (finiteEtaleSchemeProperty (D.obj j)).homMk (Over.homMk
      ((Limits.pullbackSymmetry _ _).hom ≫ b ≫ (Limits.pullbackSymmetry _ _).hom)
      (pullbackSymmetry_conj_snd (D.map fj) b hb₁))
  have hcomp : ((pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).inv.app Y₁ ≫
        (pullback (c.π.app j)).map β ≫
        (pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).hom.app Y₂).hom.left ≫
      Limits.pullback.fst Y₂.obj.hom (c.π.app i₀) =
      Limits.pullback.map Y₁.obj.hom (c.π.app i₀) Y₁.obj.hom (D.map fj) (𝟙 _) (c.π.app j) (𝟙 _)
          (by simp) (by simp [c.w fj]) ≫
        (Limits.pullbackSymmetry _ _).hom ≫ b ≫ Limits.pullback.snd (D.map fj) Y₂.obj.hom :=
    (pullbackCompIsoOfEq_conj_hom_left_fst (c.w fj) β).trans
      (congrArg (Limits.pullback.map Y₁.obj.hom (c.π.app i₀) Y₁.obj.hom (D.map fj)
        (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp [c.w fj]) ≫ ·)
        (pullbackSymmetry_conj_fst_eq_snd (D.map fj) b))
  rw [hcomp, pullback_map_pullbackSymmetry_assoc (c.w fj) Y₁.obj.hom, reassoc_of% hb₂]
  have hsymm2 : (Limits.pullbackSymmetry Y₂.obj.hom (c.π.app i₀)).hom ≫
      Limits.pullback.map (c.π.app i₀) Y₂.obj.hom (D.map fj) Y₂.obj.hom (c.π.app j)
        (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      Limits.pullback.snd (D.map fj) Y₂.obj.hom =
      Limits.pullback.fst Y₂.obj.hom (c.π.app i₀) := by
    rw [Limits.pullback.lift_snd, Category.comp_id, Limits.pullbackSymmetry_hom_comp_snd]
  have h3 : α.hom.left ≫ (Limits.pullbackSymmetry Y₂.obj.hom (c.π.app i₀)).hom ≫
      Limits.pullback.map (c.π.app i₀) Y₂.obj.hom (D.map fj) Y₂.obj.hom (c.π.app j)
        (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      Limits.pullback.snd (D.map fj) Y₂.obj.hom =
      α.hom.left ≫ Limits.pullback.fst Y₂.obj.hom (c.π.app i₀) :=
    congrArg (α.hom.left ≫ ·) hsymm2
  have h2 := congrArg ((Limits.pullbackSymmetry (c.π.app i₀) Y₁.obj.hom).hom ≫ ·)
    ((Category.assoc α.hom.left _ _).trans h3)
  exact (Category.assoc _ _ _).trans ((congrArg
    ((Limits.pullbackSymmetry Y₁.obj.hom (c.π.app i₀)).hom ≫ ·)
    ((Category.assoc _ _ _).trans h2)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg
      (· ≫ α.hom.left ≫ Limits.pullback.fst Y₂.obj.hom (c.π.app i₀))
      (pullbackSymmetry_comp_pullbackSymmetry Y₁.obj.hom (c.π.app i₀))).trans
      (Category.id_comp _))))

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)]

/-- Along a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
morphisms, any morphism between the pullbacks of two finite étale schemes `Y₁, Y₂` from a stage `i₀`
to the limit descends to a morphism over some stage `j` mapping to `i₀`. -/
@[stacks 01ZM "for finite étale schemes"]
theorem exists_hom_pullback_of_isLimit [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : Limits.IsLimit c) {i₀ : I} (Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀))
    (α : (pullback (c.π.app i₀)).obj Y₁ ⟶ (pullback (c.π.app i₀)).obj Y₂) :
    ∃ (j : I) (fj : j ⟶ i₀) (β : (pullback (D.map fj)).obj Y₁ ⟶ (pullback (D.map fj)).obj Y₂),
      (pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).inv.app Y₁ ≫
        (pullback (c.π.app j)).map β ≫
        (pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).hom.app Y₂ = α :=
  let ⟨j, fj, _, _, hβ, _⟩ := exists_hom_pullback_of_isLimit_aux D c hc Y₁ Y₂ α
  ⟨j, fj, _, hβ⟩

/-- Along a cofiltered limit of quasi-compact schemes with affine transition morphisms, two
morphisms between finite étale schemes at stage `i₀` that become equal on the limit already become
equal at some stage `k` mapping to `i₀`. -/
@[stacks 01ZM "for finite étale schemes"]
theorem exists_pullback_map_eq_of_isLimit (hc : Limits.IsLimit c) {i₀ : I}
    {Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀)} (β₁ β₂ : Y₁ ⟶ Y₂)
    (h : (pullback (c.π.app i₀)).map β₁ = (pullback (c.π.app i₀)).map β₂) :
    ∃ (k : I) (fk : k ⟶ i₀), (pullback (D.map fk)).map β₁ = (pullback (D.map fk)).map β₂ := by
  have : LocallyOfFiniteType Y₂.obj.hom := inferInstance
  let t : D.pullbackOver Y₁.obj.hom ⟶ (Functor.const (Over i₀)).obj (D.obj i₀) :=
    { app j := Limits.pullback.snd _ _ ≫ Y₁.obj.hom
      naturality j k f := by simp [D.pullbackOver_map_snd_assoc Y₁.obj.hom f] }
  have hlim : (c.pullbackOver Y₁.obj.hom).π.app (Over.mk (𝟙 i₀)) ≫
        Limits.pullback.snd (D.map (Over.mk (𝟙 i₀)).hom) Y₁.obj.hom ≫ β₁.hom.left =
      (c.pullbackOver Y₁.obj.hom).π.app (Over.mk (𝟙 i₀)) ≫
        Limits.pullback.snd (D.map (Over.mk (𝟙 i₀)).hom) Y₁.obj.hom ≫ β₂.hom.left := by
    rw [Limits.Cone.pullbackOver_π_app_snd_assoc, Limits.Cone.pullbackOver_π_app_snd_assoc]
    have hfst : Limits.pullback.fst Y₁.obj.hom (c.π.app i₀) ≫ β₁.hom.left =
        Limits.pullback.fst Y₁.obj.hom (c.π.app i₀) ≫ β₂.hom.left :=
      (pullback_map_left_fst (c.π.app i₀) β₁).symm.trans ((congrArg (fun u ↦ u.hom.left ≫
        Limits.pullback.fst Y₂.obj.hom (c.π.app i₀)) h).trans
        (pullback_map_left_fst (c.π.app i₀) β₂))
    have hfst' := congrArg ((Limits.pullbackSymmetry (c.π.app i₀) Y₁.obj.hom).hom ≫ ·) hfst
    simpa only [Limits.pullbackSymmetry_hom_comp_fst_assoc] using hfst'
  obtain ⟨k, hkj, hk⟩ := AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (D.pullbackOver Y₁.obj.hom) t Y₂.obj.hom (c.pullbackOver Y₁.obj.hom)
    (hc.pullbackOver Y₁.obj.hom) (i := Over.mk (𝟙 i₀))
    (Limits.pullback.snd _ _ ≫ β₁.hom.left) (Limits.pullback.snd _ _ ≫ β₂.hom.left)
    (by simp [t, Over.w β₁.hom]) (by simp [t, Over.w β₂.hom]) hlim
  refine ⟨k.left, k.hom, pullback_hom_ext ?_⟩
  rw [D.pullbackOver_map_snd_assoc Y₁.obj.hom hkj,
    D.pullbackOver_map_snd_assoc Y₁.obj.hom hkj] at hk
  have hsymm := congrArg ((Limits.pullbackSymmetry Y₁.obj.hom (D.map k.hom)).hom ≫ ·) hk
  simp only [Limits.pullbackSymmetry_hom_comp_snd_assoc] at hsymm
  exact (pullback_map_left_fst (D.map k.hom) β₁).trans
    (hsymm.trans (pullback_map_left_fst (D.map k.hom) β₂).symm)

/-- Along a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
morphisms, an isomorphism `e` on the limit between the pullbacks of two finite étale schemes
`Y₁, Y₂` at stage `i₀` descends to an isomorphism `ek` at some stage `k` mapping to `i₀` whose
pullback to the limit recovers `e.hom`. -/
@[stacks 01ZM "for finite étale schemes"]
theorem exists_iso_pullback_of_isLimit [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : Limits.IsLimit c) {i₀ : I} (Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀))
    (e : (pullback (c.π.app i₀)).obj Y₁ ≅ (pullback (c.π.app i₀)).obj Y₂) :
    ∃ (k : I) (fk : k ⟶ i₀) (ek : (pullback (D.map fk)).obj Y₁ ≅ (pullback (D.map fk)).obj Y₂),
      (pullbackCompIsoOfEq (c.π.app k) (D.map fk) (c.π.app i₀) (c.w fk)).inv.app Y₁ ≫
        (pullback (c.π.app k)).map ek.hom ≫
        (pullbackCompIsoOfEq (c.π.app k) (D.map fk) (c.π.app i₀) (c.w fk)).hom.app Y₂ = e.hom := by
  have : LocallyOfFinitePresentation Y₁.obj.hom := inferInstance
  have : LocallyOfFiniteType Y₂.obj.hom := inferInstance
  have : QuasiCompact Y₁.obj.hom := inferInstance
  have : QuasiCompact Y₂.obj.hom := inferInstance
  have : QuasiSeparated Y₂.obj.hom := inferInstance
  obtain ⟨j, fj, b, hb₁, hβ, hb₂⟩ := exists_hom_pullback_of_isLimit_aux D c hc Y₁ Y₂ e.hom
  let a := (Limits.pullbackSymmetry (c.π.app i₀) Y₁.obj.hom).hom ≫ e.hom.hom.left ≫
    (Limits.pullbackSymmetry Y₂.obj.hom (c.π.app i₀)).hom
  have ha : a ≫ Limits.pullback.fst (c.π.app i₀) Y₂.obj.hom =
      Limits.pullback.fst (c.π.app i₀) Y₁.obj.hom :=
    pullbackSymmetry_conj_fst (c.π.app i₀) e.hom
  have ha_iso : IsIso a := by
    have he1 : e.hom.hom.left ≫ e.inv.hom.left = 𝟙 _ := congr(($e.hom_inv_id).hom.left)
    have he2 : e.inv.hom.left ≫ e.hom.hom.left = 𝟙 _ := congr(($e.inv_hom_id).hom.left)
    exact ⟨(Limits.pullbackSymmetry _ _).hom ≫ e.inv.hom.left ≫
      (Limits.pullbackSymmetry _ _).hom,
      pullbackSymmetry_conj_inv_eq_id (c.π.app i₀) he1,
      pullbackSymmetry_conj_inv_eq_id (c.π.app i₀) he2⟩
  have : IsIso (Limits.pullback.map (c.π.app j) (Limits.pullback.fst (D.map fj) Y₁.obj.hom)
      (c.π.app j) (Limits.pullback.fst (D.map fj) Y₂.obj.hom) (𝟙 _) b (𝟙 _) (by simp)
      (by exact hb₁.symm)) :=
    (MorphismProperty.pullbackMap_iff_of_pullbackMap_comp_eq
      (.isomorphisms Scheme) fj ha hb₁ hb₂).mpr ha_iso
  obtain ⟨k, hkj, hk⟩ := hc.exists_isIso_pullbackMap b hb₁
  let β : (pullback (D.map fj)).obj Y₁ ⟶ (pullback (D.map fj)).obj Y₂ :=
    (finiteEtaleSchemeProperty (D.obj j)).homMk
      (Over.homMk ((Limits.pullbackSymmetry _ _).hom ≫ b ≫ (Limits.pullbackSymmetry _ _).hom)
        (pullbackSymmetry_conj_snd (D.map fj) b hb₁))
  let βK := (pullbackCompIsoOfEq (D.map hkj) (D.map fj) (D.map (hkj ≫ fj))
      (D.map_comp _ _).symm).inv.app Y₁ ≫
    (pullback (D.map hkj)).map β ≫
    (pullbackCompIsoOfEq (D.map hkj) (D.map fj) (D.map (hkj ≫ fj))
      (D.map_comp _ _).symm).hom.app Y₂
  let ψ {Z : Scheme.{u}} (r : Z ⟶ D.obj i₀) :
      Limits.pullback (D.map hkj) (Limits.pullback.fst (D.map fj) r) ≅
        Limits.pullback (D.map (hkj ≫ fj)) r :=
    Limits.pullbackRightPullbackFstIso (D.map fj) r (D.map hkj) ≪≫
      Limits.pullback.congrHom (D.map_comp hkj fj).symm rfl
  have hψ_hom_fst : ∀ {Z : Scheme.{u}} (r : Z ⟶ D.obj i₀),
      (ψ r).hom ≫ Limits.pullback.fst (D.map (hkj ≫ fj)) r =
        Limits.pullback.fst (D.map hkj) (Limits.pullback.fst (D.map fj) r) := by
    intro Z r; simp [ψ]
  have hψ_hom_snd : ∀ {Z : Scheme.{u}} (r : Z ⟶ D.obj i₀),
      (ψ r).hom ≫ Limits.pullback.snd (D.map (hkj ≫ fj)) r =
        Limits.pullback.snd (D.map hkj) (Limits.pullback.fst (D.map fj) r) ≫
          Limits.pullback.snd (D.map fj) r := by
    intro Z r; simp [ψ]
  have hψ_inv_fst : ∀ {Z : Scheme.{u}} (r : Z ⟶ D.obj i₀),
      (ψ r).inv ≫ Limits.pullback.fst (D.map hkj) (Limits.pullback.fst (D.map fj) r) =
        Limits.pullback.fst (D.map (hkj ≫ fj)) r := by
    intro Z r; simp [ψ]
  have hψ_inv_snd : ∀ {Z : Scheme.{u}} (r : Z ⟶ D.obj i₀),
      (ψ r).inv ≫ Limits.pullback.snd (D.map hkj) (Limits.pullback.fst (D.map fj) r) ≫
          Limits.pullback.snd (D.map fj) r =
        Limits.pullback.snd (D.map (hkj ≫ fj)) r := by
    intro Z r; simp [ψ]
  let bK := Limits.pullback.map (D.map hkj) (Limits.pullback.fst (D.map fj) Y₁.obj.hom)
    (D.map hkj) (Limits.pullback.fst (D.map fj) Y₂.obj.hom) (𝟙 _) b (𝟙 _) (by simp)
    (by exact hb₁.symm)
  have hbK : βK.hom.left = (Limits.pullbackSymmetry Y₁.obj.hom (D.map (hkj ≫ fj))).hom ≫
      (ψ Y₁.obj.hom).inv ≫ bK ≫ (ψ Y₂.obj.hom).hom ≫
      (Limits.pullbackSymmetry (D.map (hkj ≫ fj)) Y₂.obj.hom).hom := by
    apply Limits.pullback.hom_ext
    · have hLHS_fst : βK.hom.left ≫ Limits.pullback.fst Y₂.obj.hom (D.map (hkj ≫ fj)) =
          (Limits.pullback.map Y₁.obj.hom (D.map (hkj ≫ fj)) Y₁.obj.hom (D.map fj) (𝟙 _)
              (D.map hkj) (𝟙 _) (by simp) (by simp [D.map_comp]) ≫
            (Limits.pullbackSymmetry Y₁.obj.hom (D.map fj)).hom) ≫
            b ≫ Limits.pullback.snd (D.map fj) Y₂.obj.hom := by
        refine (pullbackCompIsoOfEq_conj_hom_left_fst (D.map_comp hkj fj).symm β).trans ?_
        refine ((congrArg (Limits.pullback.map Y₁.obj.hom (D.map (hkj ≫ fj)) Y₁.obj.hom (D.map fj)
            (𝟙 _) (D.map hkj) (𝟙 _) (by simp) (by simp [D.map_comp]) ≫ ·) ?_).trans
          (Category.assoc _ _ _).symm)
        exact (Category.assoc _ _ _).trans (congrArg ((Limits.pullbackSymmetry Y₁.obj.hom
          (D.map fj)).hom ≫ ·) ((Category.assoc _ _ _).trans
          (congrArg (b ≫ ·) (Limits.pullbackSymmetry_hom_comp_fst (D.map fj) Y₂.obj.hom))))
      have hRHS_fst : ((Limits.pullbackSymmetry Y₁.obj.hom (D.map (hkj ≫ fj))).hom ≫
            (ψ Y₁.obj.hom).inv ≫ bK ≫ (ψ Y₂.obj.hom).hom ≫
            (Limits.pullbackSymmetry (D.map (hkj ≫ fj)) Y₂.obj.hom).hom) ≫
            Limits.pullback.fst Y₂.obj.hom (D.map (hkj ≫ fj)) =
          ((Limits.pullbackSymmetry Y₁.obj.hom (D.map (hkj ≫ fj))).hom ≫
            (ψ Y₁.obj.hom).inv ≫
            Limits.pullback.snd (D.map hkj) (Limits.pullback.fst (D.map fj) Y₁.obj.hom)) ≫
            b ≫ Limits.pullback.snd (D.map fj) Y₂.obj.hom := by
        rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
          Limits.pullbackSymmetry_hom_comp_fst, hψ_hom_snd Y₂.obj.hom,
          Limits.pullback.lift_snd_assoc]
        simp only [Category.assoc]
      refine hLHS_fst.trans ((congrArg (· ≫ b ≫ Limits.pullback.snd (D.map fj) Y₂.obj.hom) ?_).trans
        hRHS_fst.symm)
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Limits.pullbackSymmetry_hom_comp_fst, Limits.pullback.lift_snd,
          Category.assoc, Category.assoc, ← Limits.pullback.condition,
          reassoc_of% (hψ_inv_fst Y₁.obj.hom), Limits.pullbackSymmetry_hom_comp_fst_assoc]
      · rw [Category.assoc, Limits.pullbackSymmetry_hom_comp_snd, Limits.pullback.lift_fst,
          Category.comp_id, Category.assoc, Category.assoc, hψ_inv_snd Y₁.obj.hom,
          Limits.pullbackSymmetry_hom_comp_snd]
    · have hw : βK.hom.left ≫ Limits.pullback.snd Y₂.obj.hom (D.map (hkj ≫ fj)) =
          Limits.pullback.snd Y₁.obj.hom (D.map (hkj ≫ fj)) := Over.w βK.hom
      refine hw.trans (Eq.symm ?_)
      change ((Limits.pullbackSymmetry Y₁.obj.hom (D.map (hkj ≫ fj))).hom ≫
          (ψ Y₁.obj.hom).inv ≫ bK ≫ (ψ Y₂.obj.hom).hom ≫
          (Limits.pullbackSymmetry (D.map (hkj ≫ fj)) Y₂.obj.hom).hom) ≫
          Limits.pullback.snd Y₂.obj.hom (D.map (hkj ≫ fj)) =
        Limits.pullback.snd Y₁.obj.hom (D.map (hkj ≫ fj))
      rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
        Limits.pullbackSymmetry_hom_comp_snd, hψ_hom_fst Y₂.obj.hom,
        Limits.pullback.lift_fst, Category.comp_id, hψ_inv_fst Y₁.obj.hom,
        Limits.pullbackSymmetry_hom_comp_fst]
  have h1 : IsIso (bK ≫ (ψ Y₂.obj.hom).hom ≫
      (Limits.pullbackSymmetry (D.map (hkj ≫ fj)) Y₂.obj.hom).hom) :=
    @IsIso.comp_isIso _ _ _ _ _ bK _ hk inferInstance
  have h2 : IsIso ((ψ Y₁.obj.hom).inv ≫ bK ≫ (ψ Y₂.obj.hom).hom ≫
      (Limits.pullbackSymmetry (D.map (hkj ≫ fj)) Y₂.obj.hom).hom) :=
    @IsIso.comp_isIso _ _ _ _ _ (ψ Y₁.obj.hom).inv _ inferInstance h1
  have hbK_left : IsIso βK.hom.left := by
    rw [hbK]
    exact @IsIso.comp_isIso _ _ _ _ _ (Limits.pullbackSymmetry Y₁.obj.hom (D.map (hkj ≫ fj))).hom
      _ inferInstance h2
  have hbK_hom : IsIso βK.hom :=
    @isIso_of_reflects_iso _ _ _ _ _ _ βK.hom (Over.forget _) hbK_left inferInstance
  have hbK_iso : IsIso βK :=
    @isIso_of_reflects_iso _ _ _ _ _ _ βK (finiteEtaleSchemeProperty (D.obj k)).ι hbK_hom
      inferInstance
  refine ⟨k, hkj ≫ fj, @asIso _ _ _ _ βK hbK_iso, ?_⟩
  rw [asIso_hom, pullbackCompIsoOfEq_conj_comp (c.w hkj) (D.map_comp _ _).symm
    (D.map_comp _ _).symm (c.w (hkj ≫ fj)) (c.w (hkj ≫ fj)) (c.w fj) (c.w fj) β, hβ]

end LimitSpreading

/-- Two finite étale schemes over open subschemes `U, W : X.Opens` equipped with an isomorphism
`eGlue` between their restrictions to `(U ⊓ W).toScheme` glue to a finite étale scheme `V'` over
`(U ⊔ W).toScheme` equipped with chart isomorphisms `eU` over `U.toScheme` and `eW` over
`W.toScheme` compatible with `eGlue` on `(U ⊓ W).toScheme`. -/
@[stacks 01LH "for two open subschemes and finite étale schemes"]
theorem exists_sup_of_iso_inf {X : Scheme.{u}} {U W : X.Opens}
    (V : FiniteEtaleScheme U.toScheme) (YW : FiniteEtaleScheme W.toScheme)
    (eGlue : (pullback (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left)).obj V ≅
      (pullback (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right)).obj YW) :
    ∃ (V' : FiniteEtaleScheme (U ⊔ W).toScheme)
      (eU : (pullback (X.homOfLE le_sup_left)).obj V' ≅ V)
      (eW : (pullback (X.homOfLE le_sup_right)).obj V' ≅ YW),
      (pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left) (X.homOfLE le_sup_left)
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
          (X.homOfLE_homOfLE _ _)).inv.app V' ≫
        (pullback (X.homOfLE inf_le_left)).map eU.hom ≫ eGlue.hom =
      (pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right) (X.homOfLE le_sup_right)
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
          (X.homOfLE_homOfLE _ _)).inv.app V' ≫
        (pullback (X.homOfLE inf_le_right)).map eW.hom := by
  have hpb : IsPullback (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
      (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right)
      (X.homOfLE (U := U) (V := U ⊔ W) le_sup_left)
      (X.homOfLE (U := W) (V := U ⊔ W) le_sup_right) :=
    IsOpenImmersion.isPullback _ _ _ _ (by simp) (by
      simp [Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage, Scheme.Hom.preimage_inf,
        Scheme.Opens.ι_preimage_self])
  have hcover : (X.homOfLE (U := U) (V := U ⊔ W) le_sup_left).opensRange ⊔
      (X.homOfLE (U := W) (V := U ⊔ W) le_sup_right).opensRange = ⊤ := by
    simp [Scheme.opensRange_homOfLE, ← Scheme.Hom.preimage_sup]
  obtain ⟨V', eU, eW, hcompat⟩ := exists_pullback_iso_of_isPullback hpb hcover eGlue
  refine ⟨V', eU, eW, pullback_hom_ext ?_⟩
  let f₁ : YW.obj.left ⟶ Limits.pullback V'.obj.hom (X.homOfLE le_sup_right) := eW.inv.hom.left
  have : IsIso f₁ :=
    ⟨eW.hom.hom.left, congr(($eW.inv_hom_id).hom.left), congr(($eW.hom_inv_id).hom.left)⟩
  have : IsOpenImmersion (Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right)) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (IsPullback.of_hasPullback V'.obj.hom _).flip inferInstance
  have : Mono f₁ := IsIso.mono_of_iso f₁
  have : Mono (Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right)) := IsOpenImmersion.mono _
  have : Mono (f₁ ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right)) :=
    mono_comp f₁ _
  apply (cancel_mono (f₁ ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right))).mp
  dsimp only [f₁]
  have heU : eU.hom.hom.left ≫ eU.inv.hom.left = 𝟙 _ := congr(($eU.hom_inv_id).hom.left)
  have heW : eW.hom.hom.left ≫ eW.inv.hom.left = 𝟙 _ := congr(($eW.hom_inv_id).hom.left)
  have hLHS :
      ((pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
          (X.homOfLE le_sup_left)
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
          (X.homOfLE_homOfLE _ _)).inv.app V' ≫
        (pullback (X.homOfLE inf_le_left)).map eU.hom ≫ eGlue.hom).hom.left ≫
      Limits.pullback.fst YW.obj.hom (X.homOfLE inf_le_right) ≫
        eW.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right) =
      Limits.pullback.fst V'.obj.hom
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left)) ≫
        𝟙 _ := by
    let fU := X.homOfLE (U := U ⊓ W) (V := U) inf_le_left
    let invL := ((pullbackCompIsoOfEq fU (X.homOfLE le_sup_left)
      (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
      (X.homOfLE_homOfLE _ _)).inv.app V').hom.left
    let mapU := ((pullback fU).map eU.hom).hom.left
    let tail := Limits.pullback.fst YW.obj.hom
        (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right) ≫
      eW.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right)
    let tailU := eU.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_left)
    have hcomp :
        ((pullbackCompIsoOfEq fU (X.homOfLE le_sup_left)
            (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
            (X.homOfLE_homOfLE _ _)).inv.app V' ≫
          (pullback fU).map eU.hom ≫ eGlue.hom).hom.left =
        invL ≫ mapU ≫ eGlue.hom.hom.left := by
      rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
        Over.comp_left, Over.comp_left]
    have h1 : mapU ≫ eGlue.hom.hom.left ≫ tail =
        Limits.pullback.fst ((pullback (X.homOfLE le_sup_left)).obj V').obj.hom fU ≫
          Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_left) := by
      have s₁ := congrArg (mapU ≫ ·) hcompat.symm
      have s₂ := congrArg (· ≫ tailU) (pullback_map_left_fst fU eU.hom)
      have s₃ : eU.hom.hom.left ≫ tailU = Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_left) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_left)) heU).trans
            (Category.id_comp _))
      exact s₁.trans ((Category.assoc _ _ _).symm.trans (s₂.trans ((Category.assoc _ _ _).trans
        (congrArg (Limits.pullback.fst ((pullback (X.homOfLE le_sup_left)).obj V').obj.hom fU ≫ ·)
          s₃))))
    have s₄ := (pullbackCompIsoOfEq_inv_app_hom_left_fst_assoc
      (X.homOfLE_homOfLE (U := U ⊓ W) (V := U) (W := U ⊔ W) inf_le_left le_sup_left) V'
      (Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_left))).trans
      (Limits.pullback.lift_fst _ _ _)
    exact (congrArg (· ≫ tail) hcomp).trans ((Category.assoc _ _ _).trans
      ((congrArg (invL ≫ ·) ((Category.assoc _ _ _).trans h1)).trans s₄))
  have hRHS :
      ((pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right)
          (X.homOfLE le_sup_right)
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
          (X.homOfLE_homOfLE _ _)).inv.app V' ≫
        (pullback (X.homOfLE inf_le_right)).map eW.hom).hom.left ≫
      Limits.pullback.fst YW.obj.hom (X.homOfLE inf_le_right) ≫
        eW.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right) =
      Limits.pullback.fst V'.obj.hom
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left)) ≫
        𝟙 _ := by
    let fW := X.homOfLE (U := U ⊓ W) (V := W) inf_le_right
    let invR := ((pullbackCompIsoOfEq fW
      (X.homOfLE le_sup_right)
      (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
      (X.homOfLE_homOfLE _ _)).inv.app V').hom.left
    let mapW := ((pullback fW).map eW.hom).hom.left
    let tail := Limits.pullback.fst YW.obj.hom fW ≫
      eW.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right)
    let tailW := eW.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right)
    have hcomp :
        ((pullbackCompIsoOfEq fW
            (X.homOfLE le_sup_right)
            (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
            (X.homOfLE_homOfLE _ _)).inv.app V' ≫
          (pullback fW).map eW.hom).hom.left =
        invR ≫ mapW := by
      rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
    have h1 : mapW ≫ tail =
        Limits.pullback.fst ((pullback (X.homOfLE le_sup_right)).obj V').obj.hom fW ≫
          Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right) := by
      have s₂ := congrArg (· ≫ tailW) (pullback_map_left_fst fW eW.hom)
      have s₃ : eW.hom.hom.left ≫ tailW = Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right)) heW).trans
            (Category.id_comp _))
      exact (Category.assoc _ _ _).symm.trans (s₂.trans ((Category.assoc _ _ _).trans
        (congrArg (Limits.pullback.fst ((pullback (X.homOfLE le_sup_right)).obj V').obj.hom fW ≫ ·)
          s₃)))
    have s₄ := (pullbackCompIsoOfEq_inv_app_hom_left_fst_assoc
      (X.homOfLE_homOfLE (U := U ⊓ W) (V := W) (W := U ⊔ W) inf_le_right le_sup_right) V'
      (Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right))).trans
      (Limits.pullback.lift_fst _ _ _)
    exact (congrArg (· ≫ tail) hcomp).trans ((Category.assoc _ _ _).trans
      ((congrArg (invR ≫ ·) h1).trans s₄))
  exact (Category.assoc _ _ _).trans (hLHS.trans (hRHS.symm.trans (Category.assoc _ _ _).symm))

/-- Limit-to-overlap compatibility: if `ek` at a finite stage `B` pulls back along `a : A ⟶ B`
to the cone-vertex transport of `e₀'`, then transporting `ek` along `eRange : Stage ≅ B` and
pulling back along `m = iPt.inv ≫ a ≫ eRange.inv` recovers `e₀'`. -/
private theorem overlap_of_limit_desc {Pt Stage A B C S₁ S₂ : Scheme.{u}}
    {a : A ⟶ B} {b : B ⟶ C} {ab : A ⟶ C} (hab : a ≫ b = ab) {f₁ : C ⟶ S₁} {f₂ : C ⟶ S₂}
    (iPt : A ≅ Pt) (eRange : Stage ≅ B) {g₁ : Pt ⟶ S₁} {g₂ : Pt ⟶ S₂} {i₁ : Stage ⟶ S₁}
    {i₂ : Stage ⟶ S₂} (htop₁ : iPt.hom ≫ g₁ = ab ≫ f₁) (htop₂ : iPt.hom ≫ g₂ = ab ≫ f₂)
    (hstage₁ : eRange.hom ≫ (b ≫ f₁) = i₁) (hstage₂ : eRange.hom ≫ (b ≫ f₂) = i₂)
    (hm₁ : (iPt.inv ≫ a ≫ eRange.inv) ≫ i₁ = g₁)
    (hm₂ : (iPt.inv ≫ a ≫ eRange.inv) ≫ i₂ = g₂) {Y₁ : FiniteEtaleScheme S₁}
    {Y₂ : FiniteEtaleScheme S₂} (e₀' : (pullback g₁).obj Y₁ ≅ (pullback g₂).obj Y₂)
    (ek : (pullback b).obj ((pullback f₁).obj Y₁) ≅ (pullback b).obj ((pullback f₂).obj Y₂))
    (hek : (pullbackCompIsoOfEq a b ab hab).inv.app ((pullback f₁).obj Y₁) ≫
        (pullback a).map ek.hom ≫ (pullbackCompIsoOfEq a b ab hab).hom.app ((pullback f₂).obj Y₂) =
      ((pullbackCompIsoOfEq ab f₁ (ab ≫ f₁) rfl).app Y₁ ≪≫
        (((pullbackCompIsoOfEq iPt.hom g₁ _ htop₁).app Y₁).symm ≪≫ (pullback iPt.hom).mapIso e₀' ≪≫
          (pullbackCompIsoOfEq iPt.hom g₂ _ htop₂).app Y₂) ≪≫
        ((pullbackCompIsoOfEq ab f₂ (ab ≫ f₂) rfl).app Y₂).symm).hom) :
    (pullbackCompIsoOfEq (iPt.inv ≫ a ≫ eRange.inv) i₁ g₁ hm₁).inv.app Y₁ ≫
        (pullback (iPt.inv ≫ a ≫ eRange.inv)).map
          ((((pullbackCompIsoOfEq eRange.hom (b ≫ f₁) i₁ hstage₁).app Y₁).symm ≪≫
            (pullback eRange.hom).mapIso (((pullbackCompIsoOfEq b f₁ _ rfl).app Y₁).symm ≪≫ ek ≪≫
              (pullbackCompIsoOfEq b f₂ _ rfl).app Y₂) ≪≫
            (pullbackCompIsoOfEq eRange.hom (b ≫ f₂) i₂ hstage₂).app Y₂).hom) ≫
        (pullbackCompIsoOfEq (iPt.inv ≫ a ≫ eRange.inv) i₂ g₂ hm₂).hom.app Y₂ = e₀'.hom := by
  let eLimFlat := (pullbackCompIsoOfEq iPt.hom g₁ _ htop₁).inv.app Y₁ ≫
    (pullback iPt.hom).map e₀'.hom ≫ (pullbackCompIsoOfEq iPt.hom g₂ _ htop₂).hom.app Y₂
  let ekFlat := (pullbackCompIsoOfEq b f₁ _ rfl).inv.app Y₁ ≫ ek.hom ≫
    (pullbackCompIsoOfEq b f₂ _ rfl).hom.app Y₂
  have hab₁ : a ≫ (b ≫ f₁) = ab ≫ f₁ := by rw [← Category.assoc, hab]
  have hab₂ : a ≫ (b ≫ f₂) = ab ≫ f₂ := by rw [← Category.assoc, hab]
  have hekFlat : (pullbackCompIsoOfEq a (b ≫ f₁) (ab ≫ f₁) hab₁).inv.app Y₁ ≫
      (pullback a).map ekFlat ≫
      (pullbackCompIsoOfEq a (b ≫ f₂) (ab ≫ f₂) hab₂).hom.app Y₂ = eLimFlat := by
    simp only [ekFlat, Functor.map_comp, Category.assoc]
    rw [← pullbackCompIsoOfEq_comp_inv_app_assoc hab rfl hab₁ rfl Y₁,
      ← pullbackCompIsoOfEq_comp_hom_app hab rfl hab₂ rfl Y₂, reassoc_of% hek]
    simp [eLimFlat]
  have hae₁ : (iPt.inv ≫ a) ≫ (b ≫ f₁) = g₁ := by
    rw [Category.assoc, hab₁, ← htop₁, Iso.inv_hom_id_assoc]
  have hae₂ : (iPt.inv ≫ a) ≫ (b ≫ f₂) = g₂ := by
    rw [Category.assoc, hab₂, ← htop₂, Iso.inv_hom_id_assoc]
  have ha₁ : iPt.inv ≫ (ab ≫ f₁) = g₁ := by rw [← htop₁, Iso.inv_hom_id_assoc]
  have ha₂ : iPt.inv ≫ (ab ≫ f₂) = g₂ := by rw [← htop₂, Iso.inv_hom_id_assoc]
  have hinv_id₁ : (iPt.inv ≫ iPt.hom) ≫ g₁ = g₁ := by rw [iPt.inv_hom_id, Category.id_comp]
  have hinv_id₂ : (iPt.inv ≫ iPt.hom) ≫ g₂ = g₂ := by rw [iPt.inv_hom_id, Category.id_comp]
  have hm_eRange : (iPt.inv ≫ a ≫ eRange.inv) ≫ eRange.hom = iPt.inv ≫ a := by simp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [pullbackCompIsoOfEq_conj_comp hm_eRange hstage₁ hstage₂ hm₁ hm₂ hae₁ hae₂ ekFlat,
    ← pullbackCompIsoOfEq_conj_comp rfl hab₁ hab₂ ha₁ ha₂ hae₁ hae₂ ekFlat,
    hekFlat,
    pullbackCompIsoOfEq_conj_comp rfl htop₁ htop₂ ha₁ ha₂ hinv_id₁ hinv_id₂ e₀'.hom,
    pullbackCompIsoOfEq_conj_of_eq_id iPt.inv_hom_id hinv_id₁ hinv_id₂ e₀'.hom]

/-- Gluing compatibility on the stalk overlap: given chart isomorphisms `eU, eW` satisfying binary
gluing compatibility `hglueSup` on `Inf` and overlap compatibility `hmGlue` along `m : O ⟶ Inf`,
the stalk restriction `es` built from `eW` and `eW₀` commutes with `eU` and `e₀`. -/
private theorem spread_gluing_compat {O Inf U W UW W₀ S : Scheme.{u}}
    {gU : O ⟶ U} {ιOs : O ⟶ S} {iU : Inf ⟶ U} {iW : Inf ⟶ W} {jU : U ⟶ UW} {jW : W ⟶ UW}
    {ij : Inf ⟶ UW} {mapk : W ⟶ W₀} {sW : S ⟶ W} {sUW : S ⟶ UW} {sW₀ : S ⟶ W₀} {m : O ⟶ Inf}
    (hiUjU : iU ≫ jU = ij) (hiWjW : iW ≫ jW = ij) (hgUjU : gU ≫ jU = ιOs ≫ sUW)
    (hsWjW : sW ≫ jW = sUW) (hsWmapk : sW ≫ mapk = sW₀) (hmU : m ≫ iU = gU)
    (hmW : m ≫ iW = ιOs ≫ sW) {V : FiniteEtaleScheme U} {YW₀ : FiniteEtaleScheme W₀}
    {Ys : FiniteEtaleScheme S} {V' : FiniteEtaleScheme UW} (eW₀ : (pullback sW₀).obj YW₀ ≅ Ys)
    (e₀ : (pullback gU).obj V ≅ (pullback ιOs).obj Ys)
    (eGlueFlat : (pullback iU).obj V ≅ (pullback (iW ≫ mapk)).obj YW₀)
    (eU : (pullback jU).obj V' ≅ V) (eW : (pullback jW).obj V' ≅ (pullback mapk).obj YW₀)
    (hglueSup : (pullbackCompIsoOfEq iU jU ij hiUjU).inv.app V' ≫ (pullback iU).map eU.hom ≫
        (eGlueFlat ≪≫ ((pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).app YW₀).symm).hom =
      (pullbackCompIsoOfEq iW jW ij hiWjW).inv.app V' ≫ (pullback iW).map eW.hom)
    (hmGlue : (pullbackCompIsoOfEq m iU gU hmU).inv.app V ≫
        (pullback m).map eGlueFlat.hom ≫
        (pullbackCompIsoOfEq m (iW ≫ mapk) (ιOs ≫ sW₀)
          (by rw [← Category.assoc, hmW, Category.assoc, hsWmapk])).hom.app YW₀ =
      (e₀ ≪≫ (pullback ιOs).mapIso eW₀.symm ≪≫
        (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).app YW₀).hom) :
    (pullbackCompIsoOfEq gU jU (ιOs ≫ sUW) hgUjU).inv.app V' ≫ (pullback gU).map eU.hom ≫ e₀.hom =
      (pullbackCompIsoOfEq ιOs sUW (ιOs ≫ sUW) rfl).inv.app V' ≫ (pullback ιOs).map
        (((pullbackCompIsoOfEq sW jW sUW hsWjW).app V').symm ≪≫ (pullback sW).mapIso eW ≪≫
          (pullbackCompIsoOfEq sW mapk sW₀ hsWmapk).app YW₀ ≪≫ eW₀).hom := by
  let tailIso := (pullback ιOs).mapIso eW₀.symm ≪≫
    (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).app YW₀
  rw [← cancel_mono tailIso.hom]
  have hm_ij : m ≫ ij = ιOs ≫ sUW := by rw [← hiUjU, ← Category.assoc, hmU, hgUjU]
  have hm_sW₀ : m ≫ (iW ≫ mapk) = ιOs ≫ sW₀ := by
    rw [← Category.assoc, hmW, Category.assoc, hsWmapk]
  have hOsW_jW : (ιOs ≫ sW) ≫ jW = ιOs ≫ sUW := by rw [Category.assoc, hsWjW]
  have hOsW_mapk : (ιOs ≫ sW) ≫ mapk = ιOs ≫ sW₀ := by rw [Category.assoc, hsWmapk]
  have hSup : ((pullbackCompIsoOfEq iU jU ij hiUjU).inv.app V' ≫ (pullback iU).map eU.hom) ≫
        eGlueFlat.hom =
      (pullbackCompIsoOfEq iW jW ij hiWjW).inv.app V' ≫ (pullback iW).map eW.hom ≫
        (pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).hom.app YW₀ := by
    have h := congrArg (· ≫ (pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).hom.app YW₀) hglueSup
    simpa only [Category.assoc, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.inv_hom_id_app,
      Category.comp_id] using h
  have hesTail : (pullback ιOs).map (((pullbackCompIsoOfEq sW jW sUW hsWjW).app V').symm ≪≫
        (pullback sW).mapIso eW ≪≫ (pullbackCompIsoOfEq sW mapk sW₀ hsWmapk).app YW₀ ≪≫ eW₀).hom ≫
        tailIso.hom =
      (pullback ιOs).map ((pullbackCompIsoOfEq sW jW sUW hsWjW).inv.app V' ≫
        (pullback sW).map eW.hom ≫ (pullbackCompIsoOfEq sW mapk sW₀ hsWmapk).hom.app YW₀) ≫
        (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).hom.app YW₀ := by
    simp only [tailIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc]
  simp only [Category.assoc]
  rw [hesTail,
    pullbackCompIsoOfEq_conj_comp rfl hsWjW hsWmapk rfl rfl hOsW_jW hOsW_mapk eW.hom,
    ← Iso.trans_hom e₀ tailIso, ← hmGlue,
    reassoc_of% ((pullbackCompIsoOfEq m iU gU hmU).inv.naturality eU.hom),
    pullbackCompIsoOfEq_comp_inv_app_assoc hmU hiUjU hm_ij hgUjU V',
    ← (pullback m).map_comp_assoc, ← (pullback m).map_comp_assoc, hSup,
    Functor.map_comp, Functor.map_comp, Category.assoc,
    ← pullbackCompIsoOfEq_comp_inv_app_assoc hmW hiWjW hm_ij hOsW_jW V',
    ← Functor.comp_map (pullback iW) (pullback m) eW.hom, Category.assoc,
    ← (pullbackCompIsoOfEq m iW (ιOs ≫ sW) hmW).inv.naturality_assoc eW.hom,
    ← pullbackCompIsoOfEq_comp_hom_app hmW rfl hm_sW₀ hOsW_mapk YW₀, Iso.inv_hom_id_app_assoc]

/-- Given an open `U : X.Opens` with `[QuasiCompact U.ι]`, a point `s : X`, a finite étale scheme
`V` over `U.toScheme`, a finite étale scheme `Ys` over `Spec (X.presheaf.stalk s)`, and an
isomorphism `e₀` between their pullbacks to `(X.fromSpecStalk s ⁻¹ᵁ U).toScheme`, there exist an
affine open neighborhood `W : X.AffineOpenNhds s` and a finite étale scheme `V'` over
`(U ⊔ W.opens).toScheme` equipped with restriction isomorphisms `eU` to `V` and `es` to `Ys`
commuting with `e₀` on `(X.fromSpecStalk s ⁻¹ᵁ U).toScheme`. -/
@[stacks 0BQ5 "for finite étale schemes", stacks 0EY3 "for finite étale schemes"]
theorem exists_spread_fromSpecStalk {X : Scheme.{u}} {U : X.Opens} [QuasiCompact U.ι]
    {s : X} (V : FiniteEtaleScheme U.toScheme)
    (Ys : FiniteEtaleScheme (Spec (X.presheaf.stalk s)))
    (e₀ : (pullback ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl)).obj V ≅
      (pullback (X.fromSpecStalk s ⁻¹ᵁ U).ι).obj Ys) :
    ∃ (W : X.AffineOpenNhds s) (V' : FiniteEtaleScheme (U ⊔ W.opens).toScheme)
      (eU : (pullback (X.homOfLE le_sup_left)).obj V' ≅ V)
      (es : (pullback ((U ⊔ W.opens).fromSpecStalkOfMem s
        (show s ∈ U ⊔ W.opens from Or.inr W.mem))).obj V' ≅ Ys),
      (pullbackCompIsoOfEq ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl)
          (X.homOfLE le_sup_left)
          ((X.fromSpecStalk s ⁻¹ᵁ U).ι ≫
            (U ⊔ W.opens).fromSpecStalkOfMem s (show s ∈ U ⊔ W.opens from Or.inr W.mem))
          (by rw [← cancel_mono (U ⊔ W.opens).ι, Category.assoc, Category.assoc, X.homOfLE_ι,
                Scheme.Hom.resLE_comp_ι, (U ⊔ W.opens).fromSpecStalkOfMem_ι])).inv.app V' ≫
        (pullback ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl)).map eU.hom ≫
        e₀.hom =
      (pullbackCompIsoOfEq (X.fromSpecStalk s ⁻¹ᵁ U).ι
          ((U ⊔ W.opens).fromSpecStalkOfMem s (show s ∈ U ⊔ W.opens from Or.inr W.mem))
          _ rfl).inv.app V' ≫
        (pullback (X.fromSpecStalk s ⁻¹ᵁ U).ι).map es.hom := by
  -- Phase 1: Descend `Ys` from `Spec 𝒪_{X,s}` to an affine open neighbourhood `W₀`.
  obtain ⟨W₀, YW₀, ⟨eW₀⟩⟩ := exists_pullback_fromSpecStalkOfMem_iso s Ys
  -- Phase 2: Transport `e₀` to the stalk-opens limit cone and descend it to a finite stage `k`.
  let DO := X.stalkOpensDiagram U s W₀; let cO := X.stalkOpensCone U s W₀
  let j₀ : Over W₀ := Over.mk (𝟙 W₀); let iPt := X.stalkOpensConePtIso U s W₀
  let fV := X.stalkOpensTopToOpen U s W₀; let fW := X.stalkOpensTopToNhds U s W₀
  let gU := (X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl
  let ιOs := (X.fromSpecStalk s ⁻¹ᵁ U).ι; let sW₀ := W₀.opens.fromSpecStalkOfMem s W₀.mem
  let e₀' := e₀ ≪≫ (pullback ιOs).mapIso eW₀.symm ≪≫
    (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).app YW₀
  have htopV : iPt.hom ≫ gU = cO.π.app j₀ ≫ fV := (X.stalkOpensCone_π_top_toOpen U s W₀).symm
  have htopW : iPt.hom ≫ (ιOs ≫ sW₀) = cO.π.app j₀ ≫ fW := by
    simpa only [Category.assoc] using (X.stalkOpensCone_π_top_toNhds U s W₀).symm
  obtain ⟨k, fk, ek, hek⟩ := exists_iso_pullback_of_isLimit DO cO (X.isLimitStalkOpensCone U s W₀)
    ((pullback fV).obj V) ((pullback fW).obj YW₀)
    ((pullbackCompIsoOfEq (cO.π.app j₀) fV _ rfl).app V ≪≫
      (((pullbackCompIsoOfEq iPt.hom gU _ htopV).app V).symm ≪≫ (pullback iPt.hom).mapIso e₀' ≪≫
        (pullbackCompIsoOfEq iPt.hom (ιOs ≫ sW₀) _ htopW).app YW₀) ≪≫
      ((pullbackCompIsoOfEq (cO.π.app j₀) fW _ rfl).app YW₀).symm)
  -- Phase 3: Transport `ek` to `U ⊓ W` and glue `V` with `YW₀|_{W}` over `U ⊔ W`.
  let W : X.AffineOpenNhds s := k.left; let eRange := X.stalkOpensStageIso U s k
  let mapk := X.homOfLE (Scheme.AffineOpenNhds.le_iff.mp (leOfHom k.hom))
  let iU := X.homOfLE (U := U ⊓ W.opens) (V := U) inf_le_left
  let iW := X.homOfLE (U := U ⊓ W.opens) (V := W.opens) inf_le_right
  have hstageV : eRange.hom ≫ (DO.map fk ≫ fV) = iU := X.stalkOpensStageIso_hom_map_toOpen U s fk
  have hstageW := X.stalkOpensStageIso_hom_map_toNhds U s fk
  let eGlueFlat := ((pullbackCompIsoOfEq eRange.hom (DO.map fk ≫ fV) iU hstageV).app V).symm ≪≫
    (pullback eRange.hom).mapIso (((pullbackCompIsoOfEq (DO.map fk) fV _ rfl).app V).symm ≪≫ ek ≪≫
      (pullbackCompIsoOfEq (DO.map fk) fW _ rfl).app YW₀) ≪≫
    (pullbackCompIsoOfEq eRange.hom (DO.map fk ≫ fW) (iW ≫ mapk) hstageW).app YW₀
  obtain ⟨V', eU, eW, hglueSup⟩ := exists_sup_of_iso_inf V ((pullback mapk).obj YW₀)
    (eGlueFlat ≪≫ ((pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).app YW₀).symm)
  -- Phase 4: Assemble the stalk isomorphism `es` and deduce overlap compatibility.
  let sW := W.opens.fromSpecStalkOfMem s W.mem
  let sUW := (U ⊔ W.opens).fromSpecStalkOfMem s (show s ∈ U ⊔ W.opens from Or.inr W.mem)
  have hsW_jW : sW ≫ X.homOfLE le_sup_right = sUW := by
    rw [← cancel_mono (U ⊔ W.opens).ι]; simp [sW, sUW]
  have hsW_mapk : sW ≫ mapk = sW₀ := by rw [← cancel_mono W₀.opens.ι]; simp [sW, mapk, sW₀, W]
  have hgU_jU : gU ≫ X.homOfLE le_sup_left = ιOs ≫ sUW := by
    rw [← cancel_mono (U ⊔ W.opens).ι]; simp [gU, ιOs, sUW]
  have hm_mapk : (iPt.inv ≫ cO.π.app k ≫ eRange.inv) ≫ (iW ≫ mapk) = ιOs ≫ sW₀ := by
    rw [← Category.assoc, X.stalkOpensConePtIso_inv_π_stageIso_inv_nhds U s k, Category.assoc,
      hsW_mapk]
  let es := ((pullbackCompIsoOfEq sW (X.homOfLE le_sup_right) sUW hsW_jW).app V').symm ≪≫
    (pullback sW).mapIso eW ≪≫ (pullbackCompIsoOfEq sW mapk sW₀ hsW_mapk).app YW₀ ≪≫ eW₀
  refine ⟨W, V', eU, es, spread_gluing_compat (X.homOfLE_homOfLE _ _) (X.homOfLE_homOfLE _ _)
    hgU_jU hsW_jW hsW_mapk (X.stalkOpensConePtIso_inv_π_stageIso_inv U s k)
    (X.stalkOpensConePtIso_inv_π_stageIso_inv_nhds U s k) eW₀ e₀ eGlueFlat eU eW hglueSup
    (overlap_of_limit_desc (cO.w fk) iPt eRange htopV htopW hstageV hstageW
      (X.stalkOpensConePtIso_inv_π_stageIso_inv U s k) hm_mapk e₀' ek hek)⟩

end TauCeti.FiniteEtaleScheme
