/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Tactic.Observe
import TauCeti.AlgebraicGeometry.Gluing.BinaryOpen
import TauCeti.AlgebraicGeometry.Limits.AffineTransition
import TauCeti.AlgebraicGeometry.Scheme.Opens
import TauCeti.RingTheory.Etale.DirectLimit

/-!
# Spreading out finite étale schemes from stalks and cofiltered limits

Let `X` be a scheme, `U : X.Opens` an open subscheme, and `s : X` a point. This file establishes
the spreading-and-gluing theory for finite étale covers around `Spec 𝒪_{X,s}`:

* **Stalk object descent** (`exists_pullback_fromSpecStalkOfMem_iso`): every finite étale scheme
  over `Spec (X.presheaf.stalk s)` is the pullback of a finite étale scheme over some affine open
  neighbourhood `W₀ : X.AffineOpenNhds s`, obtained from `X.stalkRingEquivDirectLimit s` and
  `Ring.DirectLimit.finiteEtale_essSurj`.
* **Cofiltered affine-transition limit descent** (`exists_hom_pullback_of_isLimit`,
  `exists_pullback_map_eq_of_isLimit`, `exists_iso_pullback_of_isLimit`): along any cofiltered limit
  of quasi-compact quasi-separated schemes with affine transition morphisms, morphisms and morphism
  equalities between pulled-back finite étale schemes descend to a finite stage, and two finite
  étale schemes whose limit pullbacks are isomorphic already become isomorphic at some finite stage.
* **Binary open gluing and stalk spreading** (`exists_sup_of_iso_inf`,
  `exists_spread_fromSpecStalk`): when `U.ι` is quasi-compact, a finite étale scheme `V` over
  `U.toScheme` whose pullback to `(X.fromSpecStalk s ⁻¹ᵁ U).toScheme` extends across
  `Spec (X.presheaf.stalk s)` spreads and glues (via `TauCeti.BinaryOpenGluingData`) to a finite
  étale scheme over `(U ⊔ W.opens).toScheme` for some `W : X.AffineOpenNhds s`.

## References

* [Stacks Project, Lemma 32.20.3](https://stacks.math.columbia.edu/tag/0BQ5)
* [Stacks Project, Lemma 32.20.4](https://stacks.math.columbia.edu/tag/0EY3)
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

section StalkObjectDescent

/-- Every finite étale scheme over `Spec (X.presheaf.stalk s)` descends to a finite étale scheme
over some affine open neighborhood `W₀ : X.AffineOpenNhds s`. -/
@[stacks 0BQ5]
theorem exists_pullback_fromSpecStalkOfMem_iso {X : Scheme.{u}} (s : X)
    (Ys : FiniteEtaleScheme (Spec (X.presheaf.stalk s))) :
    ∃ (W₀ : X.AffineOpenNhds s) (YW₀ : FiniteEtaleScheme W₀.opens.toScheme),
      Nonempty ((pullback (W₀.opens.fromSpecStalkOfMem s W₀.mem)).obj YW₀ ≅ Ys) := by
  let L := Ring.DirectLimit (X.stalkDirectSystemObj s) (fun U V h ↦ X.stalkDirectSystemMap s U V h)
  let eR : L ≃+* X.presheaf.stalk s := X.stalkRingEquivDirectLimit s
  let φ : CommRingCat.of L ≅ X.presheaf.stalk s := eR.toCommRingCatIso
  let YL : FiniteEtaleScheme (Spec (.of L)) := (pullback (Spec.map φ.inv)).obj Ys
  let AL_op := (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of L)).inverse.obj YL
  let eAL : (spec (.of L)).obj AL_op ≅ YL :=
    eqToIso (by simp [AL_op]) ≪≫
      (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of L)).counitIso.app YL
  obtain ⟨W₀, AW₀, ⟨eAW₀⟩⟩ :=
    Ring.DirectLimit.finiteEtale_essSurj (f := X.stalkDirectSystemMap s) AL_op.unop
  let := (Ring.DirectLimit.of (X.stalkDirectSystemObj s)
    (fun U V h ↦ X.stalkDirectSystemMap s U V h) W₀).toAlgebra
  have : IsAffine W₀.opens.toScheme := W₀.isAffineOpen
  let Z₀ : FiniteEtaleScheme (Spec Γ(X, W₀.opens)) := (spec Γ(X, W₀.opens)).obj (op AW₀)
  let YW₀ : FiniteEtaleScheme W₀.opens.toScheme := (pullback W₀.opens.toSpecΓ).obj Z₀
  have heL :
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.stalkDirectSystemObj s W₀) L)))).obj
          Z₀ ≅
        YL :=
    pullbackSpecObjIso AW₀ ≪≫ (spec (.of L)).mapIso (Iso.op eAW₀).symm ≪≫ eAL
  have hgerm :
      Spec.map φ.hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap (X.stalkDirectSystemObj s W₀) L)) =
        W₀.opens.fromSpecStalkOfMem s W₀.mem ≫ W₀.opens.toSpecΓ := by
    rw [← Spec.map_comp, Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]
    congr 1
    ext x
    exact X.stalkRingEquivDirectLimit_of s W₀ x
  have hφ : Spec.map φ.hom ≫ Spec.map φ.inv = 𝟙 (Spec (X.presheaf.stalk s)) := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  refine ⟨W₀, YW₀, ⟨?_⟩⟩
  exact ((pullbackComp (W₀.opens.fromSpecStalkOfMem s W₀.mem) W₀.opens.toSpecΓ).app Z₀).symm ≪≫
    (pullbackCompIsoOfEq (Spec.map φ.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap (X.stalkDirectSystemObj s W₀) L)))
      (W₀.opens.fromSpecStalkOfMem s W₀.mem ≫ W₀.opens.toSpecΓ) hgerm).symm.app Z₀ ≪≫
    (pullback (Spec.map φ.hom)).mapIso heL ≪≫
    (pullbackCompIsoOfEq (Spec.map φ.hom) (Spec.map φ.inv) (𝟙 _) hφ).app Ys ≪≫
    pullbackId.app Ys

end StalkObjectDescent

section LimitSpreading

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Limits.Cone D)

section FstProj

variable {Z S : Scheme.{u}} {g : Z ⟶ S} {Y Y₁ Y₂ Y₃ : FiniteEtaleScheme S}

private def homLeft (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    Limits.pullback Y₁.obj.hom g ⟶ Limits.pullback Y₂.obj.hom g :=
  β.hom.left

private theorem homLeft_snd (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    homLeft β ≫ Limits.pullback.snd Y₂.obj.hom g = Limits.pullback.snd Y₁.obj.hom g :=
  Over.w β.hom

private def fstProj (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    Limits.pullback Y₁.obj.hom g ⟶ Y₂.obj.left :=
  homLeft β ≫ Limits.pullback.fst Y₂.obj.hom g

@[simp]
private theorem fstProj_id (Y : FiniteEtaleScheme S) :
    fstProj (𝟙 ((pullback g).obj Y)) = Limits.pullback.fst Y.obj.hom g :=
  Category.id_comp _

@[simp]
private theorem fstProj_comp (β₁ : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂)
    (β₂ : (pullback g).obj Y₂ ⟶ (pullback g).obj Y₃) :
    fstProj (β₁ ≫ β₂) = homLeft β₁ ≫ fstProj β₂ :=
  Category.assoc _ _ _

private theorem fstProj_comp_hom (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    fstProj β ≫ Y₂.obj.hom = Limits.pullback.snd Y₁.obj.hom g ≫ g := by
  rw [fstProj, Category.assoc, Limits.pullback.condition, ← Category.assoc, homLeft_snd]

private def mkOfFstProj (a : Limits.pullback Y₁.obj.hom g ⟶ Y₂.obj.left)
    (ha : a ≫ Y₂.obj.hom = Limits.pullback.snd Y₁.obj.hom g ≫ g) :
    (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂ :=
  ObjectProperty.homMk <| Over.homMk (Limits.pullback.lift a (Limits.pullback.snd Y₁.obj.hom g) ha)
    (Limits.pullback.lift_snd a (Limits.pullback.snd Y₁.obj.hom g) ha)

private theorem homLeft_mkOfFstProj (a : Limits.pullback Y₁.obj.hom g ⟶ Y₂.obj.left)
    (ha : a ≫ Y₂.obj.hom = Limits.pullback.snd Y₁.obj.hom g ≫ g) :
    homLeft (Y₁ := Y₁) (Y₂ := Y₂) (mkOfFstProj a ha) =
      Limits.pullback.lift a (Limits.pullback.snd Y₁.obj.hom g) ha :=
  rfl

private theorem fstProj_mkOfFstProj (a : Limits.pullback Y₁.obj.hom g ⟶ Y₂.obj.left)
    (ha : a ≫ Y₂.obj.hom = Limits.pullback.snd Y₁.obj.hom g ≫ g) :
    fstProj (Y₁ := Y₁) (Y₂ := Y₂) (mkOfFstProj a ha) = a :=
  Limits.pullback.lift_fst _ _ _

private theorem hom_ext_of_fstProj {β₁ β₂ : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂}
    (h : fstProj β₁ = fstProj β₂) : β₁ = β₂ :=
  ObjectProperty.hom_ext _ <| Over.OverMorphism.ext <|
    Limits.pullback.hom_ext h ((homLeft_snd β₁).trans (homLeft_snd β₂).symm)

end FstProj

private def resStageHom {i₀ : I} {Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀)} {k j : Over i₀}
    (u : k ⟶ j) (β : (pullback (D.map j.hom)).obj Y₁ ⟶ (pullback (D.map j.hom)).obj Y₂) :
    (pullback (D.map k.hom)).obj Y₁ ⟶ (pullback (D.map k.hom)).obj Y₂ :=
  mkOfFstProj ((pullbackDiagram D i₀ Y₁.obj.hom).map u ≫ fstProj β) (by
    rw [Category.assoc, fstProj_comp_hom]; simp [← D.map_comp])

private theorem fstProj_resStageHom {i₀ : I} {Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀)}
    {k j : Over i₀} (u : k ⟶ j)
    (β : (pullback (D.map j.hom)).obj Y₁ ⟶ (pullback (D.map j.hom)).obj Y₂) :
    fstProj (resStageHom D u β) = (pullbackDiagram D i₀ Y₁.obj.hom).map u ≫ fstProj β :=
  fstProj_mkOfFstProj _ _

private theorem resStageHom_id {i₀ : I} {Y : FiniteEtaleScheme (D.obj i₀)}
    {k j : Over i₀} (u : k ⟶ j) :
    resStageHom D u (𝟙 ((pullback (D.map j.hom)).obj Y)) = 𝟙 ((pullback (D.map k.hom)).obj Y) := by
  apply hom_ext_of_fstProj
  simp [fstProj_resStageHom]

private theorem resStageHom_comp {i₀ : I} {Y₁ Y₂ Y₃ : FiniteEtaleScheme (D.obj i₀)}
    {k j : Over i₀} (u : k ⟶ j)
    (β₁ : (pullback (D.map j.hom)).obj Y₁ ⟶ (pullback (D.map j.hom)).obj Y₂)
    (β₂ : (pullback (D.map j.hom)).obj Y₂ ⟶ (pullback (D.map j.hom)).obj Y₃) :
    resStageHom D u (β₁ ≫ β₂) = resStageHom D u β₁ ≫ resStageHom D u β₂ := by
  apply hom_ext_of_fstProj
  have hcomm : homLeft (resStageHom D u β₁) ≫ (pullbackDiagram D i₀ Y₂.obj.hom).map u =
      (pullbackDiagram D i₀ Y₁.obj.hom).map u ≫ homLeft β₁ := by
    rw [resStageHom, homLeft_mkOfFstProj]
    exact Limits.pullback.hom_ext (by simp [fstProj]) (by simp [homLeft_snd])
  rw [fstProj_resStageHom, fstProj_comp, fstProj_comp, fstProj_resStageHom,
    ← Category.assoc, ← hcomm, Category.assoc]

/-- Cone-projection compatibility for compositions of stage morphisms lifting limit morphisms. -/
private theorem cone_π_fstProj_comp {i₀ : I} {Z₁ Z₂ Z₃ : FiniteEtaleScheme (D.obj i₀)}
    {j : Over i₀} (α : (pullback (c.π.app i₀)).obj Z₁ ⟶ (pullback (c.π.app i₀)).obj Z₂)
    (γ : (pullback (c.π.app i₀)).obj Z₂ ⟶ (pullback (c.π.app i₀)).obj Z₃)
    (βα : (pullback (D.map j.hom)).obj Z₁ ⟶ (pullback (D.map j.hom)).obj Z₂)
    (βγ : (pullback (D.map j.hom)).obj Z₂ ⟶ (pullback (D.map j.hom)).obj Z₃)
    (hβα : (pullbackDiagramCone D c i₀ Z₁.obj.hom).π.app j ≫ fstProj βα = fstProj α)
    (hβγ : (pullbackDiagramCone D c i₀ Z₂.obj.hom).π.app j ≫ fstProj βγ = fstProj γ) :
    (pullbackDiagramCone D c i₀ Z₁.obj.hom).π.app j ≫ fstProj (βα ≫ βγ) = fstProj (α ≫ γ) := by
  have hcomm : (pullbackDiagramCone D c i₀ Z₁.obj.hom).π.app j ≫ homLeft βα =
      homLeft α ≫ (pullbackDiagramCone D c i₀ Z₂.obj.hom).π.app j := by
    refine Limits.pullback.hom_ext (by simpa [fstProj] using hβα) ?_
    simp [homLeft_snd, reassoc_of% homLeft_snd]
  rw [fstProj_comp, fstProj_comp, ← Category.assoc, hcomm, Category.assoc, hβγ]

/-- Morphism descent from the limit of a cofiltered affine-transition diagram of qcqs schemes to a
stage in `Over i₀`, tracking compatibility on first projections. -/
private theorem exists_stageHom_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : Limits.IsLimit c) {i₀ : I} {Z₁ Z₂ : FiniteEtaleScheme (D.obj i₀)}
    (α : (pullback (c.π.app i₀)).obj Z₁ ⟶ (pullback (c.π.app i₀)).obj Z₂) :
    ∃ (j : Over i₀) (β : (pullback (D.map j.hom)).obj Z₁ ⟶ (pullback (D.map j.hom)).obj Z₂),
      (pullbackDiagramCone D c i₀ Z₁.obj.hom).π.app j ≫ fstProj β = fstProj α := by
  have ha : (pullbackDiagramCone D c i₀ Z₁.obj.hom).π ≫ pullbackDiagramToBase D i₀ Z₁.obj.hom =
      (Functor.const (Over i₀)).map (fstProj α ≫ Z₂.obj.hom) := by
    ext j
    simp [fstProj_comp_hom, c.w j.hom]
  obtain ⟨j, g, hg₁, hg₂⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (pullbackDiagram D i₀ Z₁.obj.hom) (pullbackDiagramToBase D i₀ Z₁.obj.hom) Z₂.obj.hom
      (pullbackDiagramCone D c i₀ Z₁.obj.hom) (isLimitPullbackDiagramCone D c hc i₀ Z₁.obj.hom)
      (fstProj α) ha
  exact ⟨j, mkOfFstProj g (hg₂.trans (pullbackDiagramToBase_app D i₀ Z₁.obj.hom j)),
    by rw [fstProj_mkOfFstProj, hg₁]⟩

/-- Eventual equality at a further stage for two stage morphisms whose limit projections agree. -/
private theorem exists_resStageHom_eq_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    (hc : Limits.IsLimit c) {i₀ : I} {Z₁ Z₂ : FiniteEtaleScheme (D.obj i₀)} (j : Over i₀)
    (β₁ β₂ : (pullback (D.map j.hom)).obj Z₁ ⟶ (pullback (D.map j.hom)).obj Z₂)
    (hπ : (pullbackDiagramCone D c i₀ Z₁.obj.hom).π.app j ≫ fstProj β₁ =
      (pullbackDiagramCone D c i₀ Z₁.obj.hom).π.app j ≫ fstProj β₂) :
    ∃ (k : Over i₀) (u : k ⟶ j), resStageHom D u β₁ = resStageHom D u β₂ := by
  obtain ⟨k, u, hu⟩ :=
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (pullbackDiagram D i₀ Z₁.obj.hom) (pullbackDiagramToBase D i₀ Z₁.obj.hom) Z₂.obj.hom
      (pullbackDiagramCone D c i₀ Z₁.obj.hom) (isLimitPullbackDiagramCone D c hc i₀ Z₁.obj.hom)
      (fstProj β₁) (fstProj β₂)
      ((pullbackDiagramToBase_app D i₀ Z₁.obj.hom j).trans (fstProj_comp_hom β₁).symm)
      ((pullbackDiagramToBase_app D i₀ Z₁.obj.hom j).trans (fstProj_comp_hom β₂).symm) hπ
  exact ⟨k, u, hom_ext_of_fstProj (by rw [fstProj_resStageHom, fstProj_resStageHom, hu])⟩

/-- Along a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
morphisms, any morphism between the pullbacks of two finite étale schemes `Y₁, Y₂` from a stage `i₀`
to the limit descends to a morphism over some stage `j` mapping to `i₀`. -/
@[stacks 0BQ5]
theorem exists_hom_pullback_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : Limits.IsLimit c) {i₀ : I} (Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀))
    (α : (pullback (c.π.app i₀)).obj Y₁ ⟶ (pullback (c.π.app i₀)).obj Y₂) :
    ∃ (j : I) (fj : j ⟶ i₀)
      (β : (pullback (D.map fj)).obj Y₁ ⟶ (pullback (D.map fj)).obj Y₂),
      (pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).inv.app Y₁ ≫
          (pullback (c.π.app j)).map β ≫
          (pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).hom.app Y₂ =
        α := by
  obtain ⟨j, β, hβ⟩ := exists_stageHom_of_isLimit D c hc α
  refine ⟨j.left, j.hom, β, hom_ext_of_fstProj ?_⟩
  -- Compare both morphisms in `Over c.pt` after projecting to `Y₂.obj.left`.
  have hC := pullbackCompIsoOfEq_hom_app_hom_left_fst (c.w j.hom) Y₂
  have hA := pullbackCompIsoOfEq_inv_app_hom_left_fst (c.w j.hom) Y₁
  simp only [fstProj, homLeft, ObjectProperty.FullSubcategory.comp_hom, pullback_map_hom,
    Over.comp_left] at hβ ⊢
  dsimp [pullback] at α β hβ hA hC ⊢
  have hB : ((Over.pullback (c.π.app j.left)).map β.hom).left ≫
      Limits.pullback.fst (Limits.pullback.snd Y₂.obj.hom (D.map j.hom)) (c.π.app j.left) =
      Limits.pullback.fst (Limits.pullback.snd Y₁.obj.hom (D.map j.hom)) (c.π.app j.left) ≫
        β.hom.left := by simp
  rw [Category.assoc, Category.assoc, hC, reassoc_of% hB, reassoc_of% hA]
  exact hβ

/-- Along a cofiltered limit of quasi-compact schemes with affine transition morphisms, two
morphisms between finite étale schemes at stage `i₀` that become equal on the limit already become
equal at some stage `k` mapping to `i₀`. -/
@[stacks 0BQ5]
theorem exists_pullback_map_eq_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    (hc : Limits.IsLimit c) {i₀ : I} {Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀)} (β₁ β₂ : Y₁ ⟶ Y₂)
    (h : (pullback (c.π.app i₀)).map β₁ = (pullback (c.π.app i₀)).map β₂) :
    ∃ (k : I) (fk : k ⟶ i₀), (pullback (D.map fk)).map β₁ = (pullback (D.map fk)).map β₂ := by
  let j₀ : Over i₀ := Over.mk (𝟙 i₀)
  have hfst (β : Y₁ ⟶ Y₂) :
      (pullbackDiagramCone D c i₀ Y₁.obj.hom).π.app j₀ ≫
          fstProj ((pullback (D.map j₀.hom)).map β) =
        fstProj ((pullback (c.π.app i₀)).map β) := by
    dsimp [j₀, fstProj, homLeft]; simp
  have hπ :
      (pullbackDiagramCone D c i₀ Y₁.obj.hom).π.app j₀ ≫
          fstProj ((pullback (D.map j₀.hom)).map β₁) =
        (pullbackDiagramCone D c i₀ Y₁.obj.hom).π.app j₀ ≫
          fstProj ((pullback (D.map j₀.hom)).map β₂) := by
    rw [hfst β₁, hfst β₂, h]
  obtain ⟨k, u, hu⟩ := exists_resStageHom_eq_of_isLimit D c hc j₀ _ _ hπ
  have hres (β : Y₁ ⟶ Y₂) :
      resStageHom D u ((pullback (D.map j₀.hom)).map β) = (pullback (D.map k.hom)).map β := by
    apply hom_ext_of_fstProj
    rw [fstProj_resStageHom]; dsimp [j₀, fstProj, homLeft]; simp
  exact ⟨k.left, k.hom, (hres β₁).symm.trans (hu.trans (hres β₂))⟩

/-- Along a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
morphisms, two finite étale schemes `Y₁, Y₂` at stage `i₀` whose pullbacks to the limit are
isomorphic already have isomorphic pullbacks at some stage `k` mapping to `i₀`. -/
@[stacks 0BQ5, stacks 0EY3]
theorem exists_iso_pullback_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : Limits.IsLimit c) {i₀ : I} (Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀))
    (e : (pullback (c.π.app i₀)).obj Y₁ ≅ (pullback (c.π.app i₀)).obj Y₂) :
    ∃ (k : I) (fk : k ⟶ i₀),
      Nonempty ((pullback (D.map fk)).obj Y₁ ≅ (pullback (D.map fk)).obj Y₂) := by
  obtain ⟨j₁, φ₁, hφ₁⟩ := exists_stageHom_of_isLimit D c hc e.hom
  obtain ⟨j₂, ψ₂, hψ₂⟩ := exists_stageHom_of_isLimit D c hc e.inv
  let j₃ : Over i₀ := IsCofiltered.min j₁ j₂
  let φ₃ := resStageHom D (IsCofiltered.minToLeft j₁ j₂) φ₁
  let ψ₃ := resStageHom D (IsCofiltered.minToRight j₁ j₂) ψ₂
  have hφ₃ : (pullbackDiagramCone D c i₀ Y₁.obj.hom).π.app j₃ ≫ fstProj φ₃ = fstProj e.hom := by
    rw [fstProj_resStageHom, ← Category.assoc, (pullbackDiagramCone D c i₀ Y₁.obj.hom).w, hφ₁]
  have hψ₃ : (pullbackDiagramCone D c i₀ Y₂.obj.hom).π.app j₃ ≫ fstProj ψ₃ = fstProj e.inv := by
    rw [fstProj_resStageHom, ← Category.assoc, (pullbackDiagramCone D c i₀ Y₂.obj.hom).w, hψ₂]
  have hcomp₁ : (pullbackDiagramCone D c i₀ Y₁.obj.hom).π.app j₃ ≫ fstProj (φ₃ ≫ ψ₃) =
      (pullbackDiagramCone D c i₀ Y₁.obj.hom).π.app j₃ ≫ fstProj (𝟙 _) := by
    rw [cone_π_fstProj_comp D c e.hom e.inv φ₃ ψ₃ hφ₃ hψ₃, e.hom_inv_id, fstProj_id, fstProj_id]
    simp
  obtain ⟨j₄, u₃, hu₃⟩ := exists_resStageHom_eq_of_isLimit D c hc j₃ (φ₃ ≫ ψ₃) (𝟙 _) hcomp₁
  let φ₄ := resStageHom D u₃ φ₃
  let ψ₄ := resStageHom D u₃ ψ₃
  have hφ₄ψ₄ : φ₄ ≫ ψ₄ = 𝟙 _ := by rw [← resStageHom_comp, hu₃, resStageHom_id]
  have hφ₄ : (pullbackDiagramCone D c i₀ Y₁.obj.hom).π.app j₄ ≫ fstProj φ₄ = fstProj e.hom := by
    rw [fstProj_resStageHom, ← Category.assoc, (pullbackDiagramCone D c i₀ Y₁.obj.hom).w u₃, hφ₃]
  have hψ₄ : (pullbackDiagramCone D c i₀ Y₂.obj.hom).π.app j₄ ≫ fstProj ψ₄ = fstProj e.inv := by
    rw [fstProj_resStageHom, ← Category.assoc, (pullbackDiagramCone D c i₀ Y₂.obj.hom).w u₃, hψ₃]
  have hcomp₂ : (pullbackDiagramCone D c i₀ Y₂.obj.hom).π.app j₄ ≫ fstProj (ψ₄ ≫ φ₄) =
      (pullbackDiagramCone D c i₀ Y₂.obj.hom).π.app j₄ ≫ fstProj (𝟙 _) := by
    rw [cone_π_fstProj_comp D c e.inv e.hom ψ₄ φ₄ hψ₄ hφ₄, e.inv_hom_id, fstProj_id, fstProj_id]
    simp
  obtain ⟨j₅, u₄, hu₄⟩ := exists_resStageHom_eq_of_isLimit D c hc j₄ (ψ₄ ≫ φ₄) (𝟙 _) hcomp₂
  exact ⟨j₅.left, j₅.hom, ⟨{
    hom := resStageHom D u₄ φ₄
    inv := resStageHom D u₄ ψ₄
    hom_inv_id := by rw [← resStageHom_comp, hφ₄ψ₄, resStageHom_id]
    inv_hom_id := by rw [← resStageHom_comp, hu₄, resStageHom_id] }⟩⟩

end LimitSpreading

section SpreadAndGlue

/-- Two finite étale schemes over open subschemes `U, W : X.Opens` equipped with an isomorphism
between their restrictions to `(U ⊓ W).toScheme` glue to a finite étale scheme over
`(U ⊔ W).toScheme` whose restriction to `U.toScheme` is isomorphic to the first scheme. -/
@[stacks 0EY3]
theorem exists_sup_of_iso_inf {X : Scheme.{u}} {U W : X.Opens}
    (V : FiniteEtaleScheme U.toScheme) (YW : FiniteEtaleScheme W.toScheme)
    (eGlue : (pullback (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left)).obj V ≅
      (pullback (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right)).obj YW) :
    ∃ V' : FiniteEtaleScheme (U ⊔ W).toScheme,
      Nonempty ((pullback (X.homOfLE le_sup_left)).obj V' ≅ V) := by
  let Dglue : BinaryOpenGluingData U W :=
    { left := V.obj.left, leftHom := V.obj.hom, right := YW.obj.left, rightHom := YW.obj.hom
      iso := { hom := eGlue.hom.hom.left, inv := eGlue.inv.hom.left
               hom_inv_id := congr(($eGlue.hom_inv_id).hom.left)
               inv_hom_id := congr(($eGlue.inv_hom_id).hom.left) }
      iso_hom_snd := Over.w eGlue.hom.hom }
  observe hasFiniteAffineProperty : HasAffineProperty @IsFinite.{u}
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  have : IsZariskiLocalAtTarget @IsFinite.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hasFiniteAffineProperty
  have : IsZariskiLocalAtTarget @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.Etale)
  have : IsFinite Dglue.toBase :=
    Dglue.morphismProperty_toBase (@IsFinite) inferInstance inferInstance
  have : Etale Dglue.toBase :=
    Dglue.morphismProperty_toBase (@Etale) inferInstance inferInstance
  let eLeft : (Over.pullback (X.homOfLE (U := U) (V := U ⊔ W) le_sup_left)).obj
      (Over.mk Dglue.toBase) ≅ V.obj :=
    Over.isoMk Dglue.pullbackLeftIso Dglue.pullbackLeftIso_hom_leftHom
  exact ⟨ofHom Dglue.toBase,
    ⟨ObjectProperty.isoMk _ (eqToIso (by simp only [pullback_obj_obj, ofHom_obj]) ≪≫ eLeft)⟩⟩

section StalkOpens

private abbrev stalkOpensDiagram (X : Scheme.{u}) (U : X.Opens) (s : X)
    (W₀ : X.AffineOpenNhds s) : Over W₀ ⥤ Scheme.{u} :=
  opensDiagram (X.affineOpenNhdsDiagram s) W₀ (W₀.opens.ι ⁻¹ᵁ U)

private abbrev stalkOpensCone (X : Scheme.{u}) (U : X.Opens) (s : X)
    (W₀ : X.AffineOpenNhds s) : Limits.Cone (stalkOpensDiagram X U s W₀) :=
  opensCone (X.affineOpenNhdsDiagram s) (X.specStalkCone s) W₀ (W₀.opens.ι ⁻¹ᵁ U)

variable {X : Scheme.{u}} (U : X.Opens) {s : X}

private def stalkOpensObjIso {W₀ : X.AffineOpenNhds s} (j : Over W₀) :
    (stalkOpensDiagram X U s W₀).obj j ≅ (j.left.opens.ι ⁻¹ᵁ U).toScheme :=
  opensDiagramObjIso (X.affineOpenNhdsDiagram s) W₀ (W₀.opens.ι ⁻¹ᵁ U) j ≪≫
    j.left.opens.toScheme.isoOfEq
      (by rw [← Scheme.Hom.comp_preimage, Scheme.affineOpenNhdsDiagram_map, X.homOfLE_ι])

private def stalkOpensConePtIso (W₀ : X.AffineOpenNhds s) :
    (stalkOpensCone X U s W₀).pt ≅ (X.fromSpecStalk s ⁻¹ᵁ U).toScheme :=
  opensConePtIso (X.affineOpenNhdsDiagram s) (X.specStalkCone s) W₀ (W₀.opens.ι ⁻¹ᵁ U) ≪≫
    (Spec (X.presheaf.stalk s)).isoOfEq
      (by rw [← Scheme.Hom.comp_preimage, Scheme.specStalkCone_π_app,
        Scheme.Opens.fromSpecStalkOfMem_ι])

private theorem stalkOpensDiagram_map_comp_objIso_hom_ι {W₀ : X.AffineOpenNhds s}
    {j k : Over W₀} (f : j ⟶ k) :
    (stalkOpensDiagram X U s W₀).map f ≫ (stalkOpensObjIso U k).hom ≫ (k.left.opens.ι ⁻¹ᵁ U).ι =
      (stalkOpensObjIso U j).hom ≫ (j.left.opens.ι ⁻¹ᵁ U).ι ≫
        X.homOfLE (Scheme.AffineOpenNhds.le_iff.mp (leOfHom f.left)) := by
  simp only [stalkOpensObjIso, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    Scheme.isoOfEq_hom_ι_assoc]
  rw [← Category.assoc, opensDiagram_map_comp_objIso_hom,
    Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.affineOpenNhdsDiagram_map X s f.left]

private theorem stalkOpensCone_π_app_comp_objIso_hom_ι {W₀ : X.AffineOpenNhds s} (j : Over W₀) :
    (stalkOpensCone X U s W₀).π.app j ≫ (stalkOpensObjIso U j).hom ≫ (j.left.opens.ι ⁻¹ᵁ U).ι =
      (stalkOpensConePtIso U W₀).hom ≫ (X.fromSpecStalk s ⁻¹ᵁ U).ι ≫
        j.left.opens.fromSpecStalkOfMem s j.left.mem := by
  simp only [stalkOpensObjIso, stalkOpensConePtIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, Scheme.isoOfEq_hom_ι_assoc]
  rw [← Category.assoc, opensCone_π_app_comp_objIso_hom,
    Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.specStalkCone_π_app X s j.left]

private def stalkOpensTopToOpen (W₀ : X.AffineOpenNhds s) :
    (stalkOpensDiagram X U s W₀).obj (Over.mk (𝟙 W₀)) ⟶ U.toScheme :=
  (stalkOpensObjIso U (Over.mk (𝟙 W₀))).hom ≫ W₀.opens.ι.resLE U (W₀.opens.ι ⁻¹ᵁ U) le_rfl

private def stalkOpensTopToNhds (W₀ : X.AffineOpenNhds s) :
    (stalkOpensDiagram X U s W₀).obj (Over.mk (𝟙 W₀)) ⟶ W₀.opens.toScheme :=
  (stalkOpensObjIso U (Over.mk (𝟙 W₀))).hom ≫ (W₀.opens.ι ⁻¹ᵁ U).ι

private theorem stalkOpensTopToOpen_ι (W₀ : X.AffineOpenNhds s) :
    stalkOpensTopToOpen U W₀ ≫ U.ι = stalkOpensTopToNhds U W₀ ≫ W₀.opens.ι := by
  simp [stalkOpensTopToOpen, stalkOpensTopToNhds]

private theorem stalkOpensCone_π_top_toNhds (W₀ : X.AffineOpenNhds s) :
    (stalkOpensCone X U s W₀).π.app (Over.mk (𝟙 W₀)) ≫ stalkOpensTopToNhds U W₀ =
      ((stalkOpensConePtIso U W₀).hom ≫ (X.fromSpecStalk s ⁻¹ᵁ U).ι) ≫
        W₀.opens.fromSpecStalkOfMem s W₀.mem := by
  simpa only [stalkOpensTopToNhds, Over.mk_left, Category.assoc] using
    stalkOpensCone_π_app_comp_objIso_hom_ι U (W₀ := W₀) (Over.mk (𝟙 W₀))

private theorem stalkOpensCone_π_top_toOpen (W₀ : X.AffineOpenNhds s) :
    (stalkOpensCone X U s W₀).π.app (Over.mk (𝟙 W₀)) ≫ stalkOpensTopToOpen U W₀ =
      (stalkOpensConePtIso U W₀).hom ≫
        (X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl := by
  rw [← cancel_mono U.ι, Category.assoc, stalkOpensTopToOpen_ι,
    ← Category.assoc ((stalkOpensCone X U s W₀).π.app _), stalkOpensCone_π_top_toNhds,
    Category.assoc, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Category.assoc, Scheme.Hom.resLE_comp_ι]

private def stalkOpensStageIso {W₀ : X.AffineOpenNhds s} (k : Over W₀) :
    (U ⊓ k.left.opens).toScheme ≅ (stalkOpensDiagram X U s W₀).obj k :=
  (k.left.opens.ι.isoImage (k.left.opens.ι ⁻¹ᵁ U) ≪≫
      X.isoOfEq ((k.left.opens.ι_image_preimage_eq_inf U).trans (inf_comm _ _))).symm ≪≫
    (stalkOpensObjIso U k).symm

private theorem stalkOpensStageIso_hom_map_toNhds {W₀ : X.AffineOpenNhds s}
    {k : Over W₀} (fk : k ⟶ Over.mk (𝟙 W₀)) :
    (stalkOpensStageIso U k).hom ≫
        (stalkOpensDiagram X U s W₀).map fk ≫ stalkOpensTopToNhds U W₀ =
      X.homOfLE (U := U ⊓ k.left.opens) (V := k.left.opens) inf_le_right ≫
        X.homOfLE (Scheme.AffineOpenNhds.le_iff.mp (leOfHom k.hom)) := by
  have hfk : fk.left = k.hom := by simpa using Over.w fk
  have hmap := stalkOpensDiagram_map_comp_objIso_hom_ι U fk
  simp only [Over.mk_left] at hmap
  have hfac : (k.left.opens.ι.isoImage (k.left.opens.ι ⁻¹ᵁ U) ≪≫
        X.isoOfEq ((k.left.opens.ι_image_preimage_eq_inf U).trans (inf_comm _ _))).inv ≫
      (k.left.opens.ι ⁻¹ᵁ U).ι =
      X.homOfLE (U := U ⊓ k.left.opens) (V := k.left.opens) inf_le_right := by
    rw [← cancel_mono k.left.opens.ι]; simp
  simp only [stalkOpensStageIso, stalkOpensTopToNhds, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hmap, Iso.inv_hom_id_assoc, reassoc_of% hfac, hfk]

private theorem stalkOpensStageIso_hom_map_toOpen {W₀ : X.AffineOpenNhds s}
    {k : Over W₀} (fk : k ⟶ Over.mk (𝟙 W₀)) :
    (stalkOpensStageIso U k).hom ≫
        (stalkOpensDiagram X U s W₀).map fk ≫ stalkOpensTopToOpen U W₀ =
      X.homOfLE (U := U ⊓ k.left.opens) (V := U) inf_le_left := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, stalkOpensTopToOpen_ι,
    ← Category.assoc ((stalkOpensDiagram X U s W₀).map fk),
    ← Category.assoc (stalkOpensStageIso U k).hom, stalkOpensStageIso_hom_map_toNhds,
    Category.assoc, X.homOfLE_ι, X.homOfLE_ι, X.homOfLE_ι]

end StalkOpens

/-- Given an open `U : X.Opens` with `[QuasiCompact U.ι]`, a point `s : X`, a finite étale scheme
`V` over `U.toScheme`, a finite étale scheme `Ys` over `Spec (X.presheaf.stalk s)`, and an
isomorphism between their pullbacks to `(X.fromSpecStalk s ⁻¹ᵁ U).toScheme`, there exist an affine
open neighborhood `W : X.AffineOpenNhds s` and a finite étale scheme `V'` over
`(U ⊔ W.opens).toScheme` whose restriction to `U.toScheme` is isomorphic to `V`. -/
@[stacks 0BQ5, stacks 0EY3]
theorem exists_spread_fromSpecStalk {X : Scheme.{u}} {U : X.Opens} [QuasiCompact U.ι]
    {s : X} (V : FiniteEtaleScheme U.toScheme)
    (Ys : FiniteEtaleScheme (Spec (X.presheaf.stalk s)))
    (e₀ :
      (pullback ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl)).obj V ≅
        (pullback (X.fromSpecStalk s ⁻¹ᵁ U).ι).obj Ys) :
    ∃ (W : X.AffineOpenNhds s) (V' : FiniteEtaleScheme (U ⊔ W.opens).toScheme),
      Nonempty ((pullback (X.homOfLE le_sup_left)).obj V' ≅ V) := by
  obtain ⟨W₀, YW₀, ⟨eW₀⟩⟩ := exists_pullback_fromSpecStalkOfMem_iso s Ys
  have hU₀_compact :
      IsCompact ((W₀.opens.ι ⁻¹ᵁ U : ((X.affineOpenNhdsDiagram s).obj W₀).Opens) :
        Set ((X.affineOpenNhdsDiagram s).obj W₀)) :=
    W₀.opens.isCompact_ι_preimage_of_quasiCompact U W₀.isAffineOpen.isCompact
  let DO := stalkOpensDiagram X U s W₀
  let cO := stalkOpensCone X U s W₀
  have (j : Over W₀) : CompactSpace (DO.obj j) :=
    isCompact_iff_compactSpace.mp
      (((X.affineOpenNhdsDiagram s).map j.hom).isCompact_preimage hU₀_compact)
  have (j : Over W₀) : QuasiSeparatedSpace (DO.obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _
      ((X.affineOpenNhdsDiagram s).map j.hom ⁻¹ᵁ (W₀.opens.ι ⁻¹ᵁ U)).2).mp
      (.of_quasiSeparatedSpace _)
  let j₀ : Over W₀ := Over.mk (𝟙 W₀)
  let fV := stalkOpensTopToOpen U W₀
  let fW := stalkOpensTopToNhds U W₀
  let iPt := (stalkOpensConePtIso U W₀).hom
  obtain ⟨eLim⟩ :
      Nonempty ((pullback (cO.π.app j₀)).obj ((pullback fV).obj V) ≅
        (pullback (cO.π.app j₀)).obj ((pullback fW).obj YW₀)) :=
    ⟨(pullbackCompIsoOfEq (cO.π.app j₀) fV _ (stalkOpensCone_π_top_toOpen U W₀)).app V ≪≫
      ((pullbackCompIsoOfEq iPt
        ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl) _ rfl).app V).symm ≪≫
      (pullback iPt).mapIso e₀ ≪≫
      (pullbackCompIsoOfEq iPt (X.fromSpecStalk s ⁻¹ᵁ U).ι _ rfl).app Ys ≪≫
      (pullback (iPt ≫ (X.fromSpecStalk s ⁻¹ᵁ U).ι)).mapIso eW₀.symm ≪≫
      (pullbackCompIsoOfEq (iPt ≫ (X.fromSpecStalk s ⁻¹ᵁ U).ι)
        (W₀.opens.fromSpecStalkOfMem s W₀.mem) _ rfl).app YW₀ ≪≫
      ((pullbackCompIsoOfEq (cO.π.app j₀) fW _ (stalkOpensCone_π_top_toNhds U W₀)).app YW₀).symm⟩
  obtain ⟨k, fk, ⟨ek⟩⟩ :=
    exists_iso_pullback_of_isLimit DO cO
      (isLimitOpensCone (X.affineOpenNhdsDiagram s) (X.specStalkCone s)
        (X.isLimitSpecStalkCone s) W₀ (W₀.opens.ι ⁻¹ᵁ U))
      ((pullback fV).obj V) ((pullback fW).obj YW₀) eLim
  let W : X.AffineOpenNhds s := k.left
  let mapk : W.opens.toScheme ⟶ W₀.opens.toScheme :=
    X.homOfLE (Scheme.AffineOpenNhds.le_iff.mp (leOfHom k.hom))
  let YW : FiniteEtaleScheme W.opens.toScheme := (pullback mapk).obj YW₀
  let eRange := stalkOpensStageIso U k
  obtain ⟨eGlue⟩ :
      Nonempty ((pullback (X.homOfLE (U := U ⊓ W.opens) (V := U) inf_le_left)).obj V ≅
        (pullback (X.homOfLE (U := U ⊓ W.opens) (V := W.opens) inf_le_right)).obj YW) :=
    ⟨((pullbackCompIsoOfEq eRange.hom (DO.map fk ≫ fV) _
        (stalkOpensStageIso_hom_map_toOpen U fk)).app V).symm ≪≫
      (pullback eRange.hom).mapIso
        ((pullbackComp (DO.map fk) fV).app V ≪≫ ek ≪≫
          ((pullbackComp (DO.map fk) fW).app YW₀).symm) ≪≫
      (pullbackCompIsoOfEq eRange.hom (DO.map fk ≫ fW) _
        (stalkOpensStageIso_hom_map_toNhds U fk)).app YW₀ ≪≫
      (pullbackComp (X.homOfLE inf_le_right) mapk).app YW₀⟩
  obtain ⟨V', hV'⟩ := exists_sup_of_iso_inf V YW eGlue
  exact ⟨W, V', hV'⟩

end SpreadAndGlue

end TauCeti.FiniteEtaleScheme
