/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.NoetherianSpace
public import TauCeti.AlgebraicGeometry.FiniteEtale.MorphismProperty
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
public import TauCeti.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import Mathlib.Tactic.Observe
import TauCeti.AlgebraicGeometry.Gluing
import TauCeti.RingTheory.Etale.DirectLimit

/-!
# Spreading out finite étale schemes from stalks and globalizing local purity

Let `X` be a scheme, `U : X.Opens` an open subscheme, and `s : X` a point. This file establishes
two spreading and extension principles for finite étale schemes:

1. **Spreading from the local scheme `Spec O_{X,s}`** (`exists_pullback_fromSpecStalkOfMem_iso`,
   `exists_iso_pullback_of_isLimit`, `exists_spread_fromSpecStalk`):
   - Every finite étale scheme over `Spec (X.presheaf.stalk s)` descends to an affine open
     neighborhood `W₀ : X.AffineOpenNhds s`, by identifying `X.presheaf.stalk s` with the direct
     limit of coordinate rings `Γ(X, W.opens)` (`X.stalkRingEquivDirectLimit s`) and applying
     `Ring.DirectLimit.finiteEtale_essSurj`.
   - Along any cofiltered limit of quasi-compact quasi-separated schemes with affine transition
     morphisms, morphisms and isomorphisms between pulled-back finite étale schemes descend to a
     finite stage, via `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` and
     `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`.
   - When `U.ι` is quasi-compact, a finite étale scheme `V` over `U.toScheme` whose pullback to
     `(X.fromSpecStalk s ⁻¹ᵁ U).toScheme` extends across `Spec (X.presheaf.stalk s)` spreads and
     glues (via `TauCeti.BinaryOpenGluingData`) to a finite étale scheme over
     `(U ⊔ W.opens).toScheme` for some affine open neighborhood `W : X.AffineOpenNhds s`.

2. **Globalization of local purity across an open subscheme** (`finiteEtale_extend_of_purity`,
   `finiteEtaleOver_extend_of_purity`):
   If `X` is a Noetherian topological space (`[NoetherianSpace X]`) and local purity holds at every
   point `s ∉ U` (`TauCeti.IsLocalRing.PurityHolds (X.presheaf.stalk s)`), then restriction of
   finite étale schemes along `U.ι : U.toScheme ⟶ X` is essentially surjective. By Noetherian
   induction on `X.Opens`, if a current domain `U'` is proper, choosing a point `s ∉ U'` whose
   proper specializations lie in `U'` identifies `X.fromSpecStalk s ⁻¹ᵁ U'` with the punctured
   spectrum of `X.presheaf.stalk s`; local purity extends the cover over
   `Spec (X.presheaf.stalk s)`, and spreading and gluing strictly enlarges `U'` to `U' ⊔ W.opens`.

## Main results

* `TauCeti.FiniteEtaleScheme.pullbackSpecObjIso`: base change of `FiniteEtaleScheme.spec` along
  `Spec (algebraMap R S)` agrees with `CommAlgCat.FiniteEtale.baseChange R S`.
* `TauCeti.FiniteEtaleScheme.exists_pullback_fromSpecStalkOfMem_iso`: every finite étale scheme over
  `Spec (X.presheaf.stalk s)` is the pullback of a finite étale scheme over some
  `W₀ : X.AffineOpenNhds s`.
* `TauCeti.FiniteEtaleScheme.exists_iso_pullback_of_isLimit`: an isomorphism between pullbacks of
  two finite étale schemes to a cofiltered affine-transition limit of qcqs schemes descends to a
  finite stage.
* `TauCeti.FiniteEtaleScheme.exists_sup_of_iso_inf` and
  `TauCeti.FiniteEtaleScheme.exists_spread_fromSpecStalk`: binary open gluing over `U ⊔ W` and
  spreading a finite étale scheme from `U` and `Spec (X.presheaf.stalk s)` to `U ⊔ W.opens`.
* `TauCeti.finiteEtale_extend_of_purity` and `TauCeti.finiteEtaleOver_extend_of_purity`: essential
  surjectivity of restriction to `U` when local purity holds at all points outside `U`.

## References

* [Stacks Project, Lemma 32.20.3](https://stacks.math.columbia.edu/tag/0BQ5)
* [Stacks Project, Lemma 32.20.4](https://stacks.math.columbia.edu/tag/0EY3)
* [Stacks Project, Lemma 58.21.6](https://stacks.math.columbia.edu/tag/0EY7)
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace TauCeti.FiniteEtaleScheme

section BaseChangeHelpers

variable {U T S : Scheme.{u}}

/-- Pullback functors along equal base morphisms are naturally isomorphic. -/
def pullbackCongr {f₁ f₂ : T ⟶ S} (h : f₁ = f₂) : pullback f₁ ≅ pullback f₂ :=
  eqToIso (by subst h; rfl)

/-- Natural isomorphism `pullback g ⋙ pullback f ≅ pullback fg` attached to an equality
`f ≫ g = fg`. -/
def pullbackCompIsoOfEq (f : U ⟶ T) (g : T ⟶ S) (fg : U ⟶ S) (h : f ≫ g = fg) :
    pullback g ⋙ pullback f ≅ pullback fg :=
  (pullbackComp f g).symm ≪≫ pullbackCongr h

/-- Essential surjectivity of `TauCeti.FiniteEtaleScheme.pullback f` is equivalent to essential
surjectivity of Mathlib's `MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ f`. -/
theorem essSurj_pullback_iff (f : T ⟶ S) :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (pullback f).EssSurj ↔
      (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ f).EssSurj := by
  let : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  constructor
  · intro _
    have : (pullback f ⋙ (equivOver T).functor).EssSurj := inferInstance
    have : ((equivOver S).functor ⋙
        MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ f).EssSurj :=
      Functor.essSurj_of_iso (pullbackCompEquivOver f)
    have : ((equivOver S).inverse ⋙ (equivOver S).functor ⋙
        MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ f).EssSurj := inferInstance
    exact Functor.essSurj_of_iso
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (equivOver S).counitIso _ ≪≫ Functor.leftUnitor _)
  · intro _
    have : ((equivOver S).functor ⋙
        MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ f).EssSurj := inferInstance
    have : (pullback f ⋙ (equivOver T).functor).EssSurj :=
      Functor.essSurj_of_iso (pullbackCompEquivOver f).symm
    have : ((pullback f ⋙ (equivOver T).functor) ⋙ (equivOver T).inverse).EssSurj := inferInstance
    exact Functor.essSurj_of_iso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (equivOver T).unitIso.symm ≪≫ Functor.rightUnitor _)

end BaseChangeHelpers

section StalkObjectDescent

/-- Pulling `FiniteEtaleScheme.spec` back along `Spec (algebraMap R S)` agrees up to canonical
isomorphism with `CommAlgCat.FiniteEtale.baseChange R S`. -/
def pullbackSpecObjIso {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (A : CommAlgCat.FiniteEtale.{u} R) :
    (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
      ((spec (.of R)).obj (op A)) ≅
    (spec (.of S)).obj (op ((CommAlgCat.FiniteEtale.baseChange R S).obj A)) := by
  let eOver :
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
          ((algSpec (.of R)).obj (op A.obj)) ≅
        (algSpec (.of S)).obj (op ((CommAlgCat.FiniteEtale.baseChange R S).obj A).obj) :=
    Over.isoMk (Limits.pullbackSymmetry _ _ ≪≫ AlgebraicGeometry.pullbackSpecIso R S A.obj) (by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((Limits.pullbackSymmetry _ _).hom ≫ ·)
        (AlgebraicGeometry.pullbackSpecIso_hom_fst' R S A.obj)).trans ?_
      exact Limits.pullbackSymmetry_hom_comp_fst _ _)
  exact ObjectProperty.isoMk _
    (eqToIso (by simp only [pullback_obj_obj, spec_obj_obj]) ≪≫ eOver ≪≫
      eqToIso (by simp only [spec_obj_obj]))

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

private abbrev pullbackDiagram (i₀ : I) (Y : FiniteEtaleScheme (D.obj i₀)) :
    Over i₀ ⥤ Scheme.{u} where
  obj j := Limits.pullback Y.obj.hom (D.map j.hom)
  map {j k} f :=
    Limits.pullback.map Y.obj.hom (D.map j.hom) Y.obj.hom (D.map k.hom)
      (𝟙 _) (D.map f.left) (𝟙 _) (by simp) (by simp [← D.map_comp])
  map_id j := by apply Limits.pullback.hom_ext <;> simp
  map_comp f g := by apply Limits.pullback.hom_ext <;> simp

private abbrev pullbackDiagramSnd (i₀ : I) (Y : FiniteEtaleScheme (D.obj i₀)) :
    pullbackDiagram D i₀ Y ⟶ Over.forget i₀ ⋙ D where
  app j := Limits.pullback.snd Y.obj.hom (D.map j.hom)
  naturality f := by simp [pullbackDiagram]

private abbrev pullbackDiagramToBase (i₀ : I) (Y : FiniteEtaleScheme (D.obj i₀)) :
    pullbackDiagram D i₀ Y ⟶ (Functor.const (Over i₀)).obj (D.obj i₀) where
  app j := Limits.pullback.snd Y.obj.hom (D.map j.hom) ≫ D.map j.hom
  naturality f := by simp [pullbackDiagram, ← D.map_comp]

private abbrev pullbackDiagramCone (i₀ : I) (Y : FiniteEtaleScheme (D.obj i₀)) :
    Limits.Cone (pullbackDiagram D i₀ Y) where
  pt := Limits.pullback Y.obj.hom (c.π.app i₀)
  π :=
    { app := fun j ↦
        Limits.pullback.map Y.obj.hom (c.π.app i₀) Y.obj.hom (D.map j.hom)
          (𝟙 _) (c.π.app j.left) (𝟙 _) (by simp) (by simp [c.w])
      naturality := fun {_ _} f ↦ by
        dsimp [pullbackDiagram]
        apply Limits.pullback.hom_ext <;> simp [c.w] }

private theorem isPullback_pullbackDiagram_map {i₀ : I} (Y : FiniteEtaleScheme (D.obj i₀))
    {j k : Over i₀} (f : j ⟶ k) :
    IsPullback ((pullbackDiagram D i₀ Y).map f)
      (Limits.pullback.snd Y.obj.hom (D.map j.hom))
      (Limits.pullback.snd Y.obj.hom (D.map k.hom))
      (D.map f.left) := by
  refine IsPullback.of_right ?_ (by simp [pullbackDiagram])
    (IsPullback.of_hasPullback Y.obj.hom (D.map k.hom))
  have h1 :
      (pullbackDiagram D i₀ Y).map f ≫ Limits.pullback.fst Y.obj.hom (D.map k.hom) =
        Limits.pullback.fst Y.obj.hom (D.map j.hom) := by
    simp [pullbackDiagram]
  have h2 : D.map f.left ≫ D.map k.hom = D.map j.hom := by
    rw [← D.map_comp, Over.w f]
  rw [h1, h2]
  exact IsPullback.of_hasPullback Y.obj.hom (D.map j.hom)

private instance isAffineHom_pullbackDiagram_map
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i₀ : I} (Y : FiniteEtaleScheme (D.obj i₀)) {j k : Over i₀} (f : j ⟶ k) :
    IsAffineHom ((pullbackDiagram D i₀ Y).map f) :=
  MorphismProperty.of_isPullback (isPullback_pullbackDiagram_map D Y f).flip inferInstance

private instance compactSpace_pullbackDiagram_obj [∀ i, CompactSpace (D.obj i)]
    {i₀ : I} (Y : FiniteEtaleScheme (D.obj i₀)) (j : Over i₀) :
    CompactSpace ((pullbackDiagram D i₀ Y).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.snd Y.obj.hom (D.map j.hom))

private instance quasiSeparatedSpace_pullbackDiagram_obj [∀ i, QuasiSeparatedSpace (D.obj i)]
    {i₀ : I} (Y : FiniteEtaleScheme (D.obj i₀)) (j : Over i₀) :
    QuasiSeparatedSpace ((pullbackDiagram D i₀ Y).obj j) :=
  quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd Y.obj.hom (D.map j.hom))

private def isLimitPullbackDiagramCone [IsCofiltered I] (hc : Limits.IsLimit c)
    (i₀ : I) (Y : FiniteEtaleScheme (D.obj i₀)) :
    Limits.IsLimit (pullbackDiagramCone D c i₀ Y) := by
  have : IsConnected (Over i₀) := isConnected_of_hasTerminal (Over i₀)
  refine Limits.isLimitOfIsPullbackOfIsConnected
    (pullbackDiagramSnd D i₀ Y)
    (pullbackDiagramCone D c i₀ Y)
    (c.whisker (Over.forget i₀))
    { hom := Limits.pullback.snd Y.obj.hom (c.π.app i₀)
      w := fun j ↦ by simp [pullbackDiagramCone, pullbackDiagramSnd] }
    (fun j ↦ ?_)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc)
  refine IsPullback.of_right ?_ (by simp [pullbackDiagramCone])
    (IsPullback.of_hasPullback Y.obj.hom (D.map j.hom))
  have h1 :
      (pullbackDiagramCone D c i₀ Y).π.app j ≫ Limits.pullback.fst Y.obj.hom (D.map j.hom) =
        Limits.pullback.fst Y.obj.hom (c.π.app i₀) := by
    simp [pullbackDiagramCone]
  have h2 : (c.whisker (Over.forget i₀)).π.app j = c.π.app j.left := rfl
  rw [h1, h2, c.w j.hom]
  exact IsPullback.of_hasPullback Y.obj.hom (c.π.app i₀)

private def homLeft {Z S : Scheme.{u}} {g : Z ⟶ S} {Y₁ Y₂ : FiniteEtaleScheme S}
    (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    Limits.pullback Y₁.obj.hom g ⟶ Limits.pullback Y₂.obj.hom g :=
  β.hom.left

private theorem homLeft_id {Z S : Scheme.{u}} {g : Z ⟶ S} (Y : FiniteEtaleScheme S) :
    homLeft (𝟙 ((pullback g).obj Y)) = 𝟙 (Limits.pullback Y.obj.hom g) :=
  rfl

private theorem homLeft_comp {Z S : Scheme.{u}} {g : Z ⟶ S} {Y₁ Y₂ Y₃ : FiniteEtaleScheme S}
    (β₁ : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂)
    (β₂ : (pullback g).obj Y₂ ⟶ (pullback g).obj Y₃) :
    homLeft (β₁ ≫ β₂) = homLeft β₁ ≫ homLeft β₂ :=
  rfl

private theorem homLeft_snd {Z S : Scheme.{u}} {g : Z ⟶ S} {Y₁ Y₂ : FiniteEtaleScheme S}
    (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    homLeft β ≫ Limits.pullback.snd Y₂.obj.hom g = Limits.pullback.snd Y₁.obj.hom g :=
  Over.w β.hom

private def fstProj {Z S : Scheme.{u}} {g : Z ⟶ S} {Y₁ Y₂ : FiniteEtaleScheme S}
    (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    Limits.pullback Y₁.obj.hom g ⟶ Y₂.obj.left :=
  homLeft β ≫ Limits.pullback.fst Y₂.obj.hom g

private theorem fstProj_comp_hom {Z S : Scheme.{u}} {g : Z ⟶ S} {Y₁ Y₂ : FiniteEtaleScheme S}
    (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    fstProj β ≫ Y₂.obj.hom = Limits.pullback.snd Y₁.obj.hom g ≫ g := by
  rw [fstProj, Category.assoc, Limits.pullback.condition, ← Category.assoc, homLeft_snd]

private def mkOfFstProj {Z S : Scheme.{u}} {g : Z ⟶ S} {Y₁ Y₂ : FiniteEtaleScheme S}
    (a : Limits.pullback Y₁.obj.hom g ⟶ Y₂.obj.left)
    (ha : a ≫ Y₂.obj.hom = Limits.pullback.snd Y₁.obj.hom g ≫ g) :
    (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂ :=
  ObjectProperty.homMk <|
    Over.homMk (Limits.pullback.lift a (Limits.pullback.snd Y₁.obj.hom g) ha)
      (Limits.pullback.lift_snd a (Limits.pullback.snd Y₁.obj.hom g) ha)

private theorem homLeft_mkOfFstProj {Z S : Scheme.{u}} {g : Z ⟶ S} {Y₁ Y₂ : FiniteEtaleScheme S}
    (a : Limits.pullback Y₁.obj.hom g ⟶ Y₂.obj.left)
    (ha : a ≫ Y₂.obj.hom = Limits.pullback.snd Y₁.obj.hom g ≫ g) :
    homLeft (Y₁ := Y₁) (Y₂ := Y₂) (mkOfFstProj a ha) =
      Limits.pullback.lift a (Limits.pullback.snd Y₁.obj.hom g) ha :=
  rfl

private theorem fstProj_mkOfFstProj {Z S : Scheme.{u}} {g : Z ⟶ S} {Y₁ Y₂ : FiniteEtaleScheme S}
    (a : Limits.pullback Y₁.obj.hom g ⟶ Y₂.obj.left)
    (ha : a ≫ Y₂.obj.hom = Limits.pullback.snd Y₁.obj.hom g ≫ g) :
    fstProj (Y₁ := Y₁) (Y₂ := Y₂) (mkOfFstProj a ha) = a :=
  Limits.pullback.lift_fst _ _ _

private theorem hom_ext_of_fstProj {Z S : Scheme.{u}} {g : Z ⟶ S} {Y₁ Y₂ : FiniteEtaleScheme S}
    {β₁ β₂ : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂}
    (h : fstProj β₁ = fstProj β₂) : β₁ = β₂ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact Limits.pullback.hom_ext h ((homLeft_snd β₁).trans (homLeft_snd β₂).symm)

private def resStageHom {i₀ : I} {Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀)} {k j : Over i₀}
    (u : k ⟶ j)
    (β : (pullback (D.map j.hom)).obj Y₁ ⟶ (pullback (D.map j.hom)).obj Y₂) :
    (pullback (D.map k.hom)).obj Y₁ ⟶ (pullback (D.map k.hom)).obj Y₂ :=
  mkOfFstProj ((pullbackDiagram D i₀ Y₁).map u ≫ fstProj β) (by
    rw [Category.assoc, fstProj_comp_hom]
    simp [pullbackDiagram, ← D.map_comp])

private theorem fstProj_resStageHom {i₀ : I} {Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀)}
    {k j : Over i₀} (u : k ⟶ j)
    (β : (pullback (D.map j.hom)).obj Y₁ ⟶ (pullback (D.map j.hom)).obj Y₂) :
    fstProj (resStageHom D u β) = (pullbackDiagram D i₀ Y₁).map u ≫ fstProj β :=
  fstProj_mkOfFstProj _ _

private theorem resStageHom_id {i₀ : I} {Y : FiniteEtaleScheme (D.obj i₀)}
    {k j : Over i₀} (u : k ⟶ j) :
    resStageHom D u (𝟙 ((pullback (D.map j.hom)).obj Y)) =
      𝟙 ((pullback (D.map k.hom)).obj Y) := by
  apply hom_ext_of_fstProj
  rw [fstProj_resStageHom, fstProj, fstProj, homLeft_id, homLeft_id]
  simp [pullbackDiagram]

private theorem resStageHom_comp {i₀ : I} {Y₁ Y₂ Y₃ : FiniteEtaleScheme (D.obj i₀)}
    {k j : Over i₀} (u : k ⟶ j)
    (β₁ : (pullback (D.map j.hom)).obj Y₁ ⟶ (pullback (D.map j.hom)).obj Y₂)
    (β₂ : (pullback (D.map j.hom)).obj Y₂ ⟶ (pullback (D.map j.hom)).obj Y₃) :
    resStageHom D u (β₁ ≫ β₂) = resStageHom D u β₁ ≫ resStageHom D u β₂ := by
  apply hom_ext_of_fstProj
  have hcomm :
      homLeft (resStageHom D u β₁) ≫ (pullbackDiagram D i₀ Y₂).map u =
        (pullbackDiagram D i₀ Y₁).map u ≫ homLeft β₁ := by
    rw [resStageHom, homLeft_mkOfFstProj]
    apply Limits.pullback.hom_ext
    · simp [pullbackDiagram, fstProj]
    · simp [pullbackDiagram, homLeft_snd]
  rw [fstProj_resStageHom, fstProj, fstProj, homLeft_comp, homLeft_comp,
    Category.assoc (homLeft (resStageHom D u β₁)),
    show homLeft (resStageHom D u β₂) ≫ Limits.pullback.fst Y₃.obj.hom (D.map k.hom) =
      (pullbackDiagram D i₀ Y₂).map u ≫ fstProj β₂ from fstProj_resStageHom D u β₂,
    ← Category.assoc (homLeft (resStageHom D u β₁)), hcomm,
    Category.assoc ((pullbackDiagram D i₀ Y₁).map u), fstProj, Category.assoc]

/-- Along a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
morphisms, any isomorphism between the pullbacks of two finite étale schemes `Y₁, Y₂` from a stage
`i₀` to the limit descends to an isomorphism over some stage `k` mapping to `i₀`. -/
@[stacks 0BQ5, stacks 0EY3]
theorem exists_iso_pullback_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : Limits.IsLimit c) {i₀ : I}
    (Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀))
    (e : (pullback (c.π.app i₀)).obj Y₁ ≅ (pullback (c.π.app i₀)).obj Y₂) :
    ∃ (k : I) (fk : k ⟶ i₀),
      Nonempty ((pullback (D.map fk)).obj Y₁ ≅ (pullback (D.map fk)).obj Y₂) := by
  have spread_hom :
      ∀ {Z₁ Z₂ : FiniteEtaleScheme (D.obj i₀)}
        (α : (pullback (c.π.app i₀)).obj Z₁ ⟶ (pullback (c.π.app i₀)).obj Z₂),
        ∃ (j : Over i₀)
          (β : (pullback (D.map j.hom)).obj Z₁ ⟶ (pullback (D.map j.hom)).obj Z₂),
          (pullbackDiagramCone D c i₀ Z₁).π.app j ≫ fstProj β = fstProj α := by
    intro Z₁ Z₂ α
    have ha :
        (pullbackDiagramCone D c i₀ Z₁).π ≫ pullbackDiagramToBase D i₀ Z₁ =
          (Functor.const (Over i₀)).map (fstProj α ≫ Z₂.obj.hom) := by
      ext j
      dsimp [pullbackDiagramCone, pullbackDiagramToBase]
      rw [fstProj_comp_hom, Limits.pullback.lift_snd_assoc, Category.assoc, c.w j.hom]
    obtain ⟨j, g, hg₁, hg₂⟩ :=
      Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
        (pullbackDiagram D i₀ Z₁) (pullbackDiagramToBase D i₀ Z₁) Z₂.obj.hom
        (pullbackDiagramCone D c i₀ Z₁) (isLimitPullbackDiagramCone D c hc i₀ Z₁)
        (fstProj α) ha
    exact ⟨j, mkOfFstProj g hg₂, by rw [fstProj_mkOfFstProj, hg₁]⟩
  have eq_hom :
      ∀ {Z₁ Z₂ : FiniteEtaleScheme (D.obj i₀)} (j : Over i₀)
        (β₁ β₂ : (pullback (D.map j.hom)).obj Z₁ ⟶ (pullback (D.map j.hom)).obj Z₂),
        (pullbackDiagramCone D c i₀ Z₁).π.app j ≫ fstProj β₁ =
          (pullbackDiagramCone D c i₀ Z₁).π.app j ≫ fstProj β₂ →
        ∃ (k : Over i₀) (u : k ⟶ j), resStageHom D u β₁ = resStageHom D u β₂ := by
    intro Z₁ Z₂ j β₁ β₂ hπ
    obtain ⟨k, u, hu⟩ :=
      Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
        (pullbackDiagram D i₀ Z₁) (pullbackDiagramToBase D i₀ Z₁) Z₂.obj.hom
        (pullbackDiagramCone D c i₀ Z₁) (isLimitPullbackDiagramCone D c hc i₀ Z₁)
        (fstProj β₁) (fstProj β₂)
        (fstProj_comp_hom β₁).symm (fstProj_comp_hom β₂).symm hπ
    refine ⟨k, u, hom_ext_of_fstProj ?_⟩
    rw [fstProj_resStageHom, fstProj_resStageHom, hu]
  obtain ⟨j₁, φ₁, hφ₁⟩ := spread_hom e.hom
  obtain ⟨j₂, ψ₂, hψ₂⟩ := spread_hom e.inv
  let j₃ : Over i₀ := IsCofiltered.min j₁ j₂
  let u₁ : j₃ ⟶ j₁ := IsCofiltered.minToLeft j₁ j₂
  let u₂ : j₃ ⟶ j₂ := IsCofiltered.minToRight j₁ j₂
  let φ₃ := resStageHom D u₁ φ₁
  let ψ₃ := resStageHom D u₂ ψ₂
  have hφ₃ : (pullbackDiagramCone D c i₀ Y₁).π.app j₃ ≫ fstProj φ₃ = fstProj e.hom := by
    rw [fstProj_resStageHom, ← Category.assoc, (pullbackDiagramCone D c i₀ Y₁).w u₁, hφ₁]
  have hψ₃ : (pullbackDiagramCone D c i₀ Y₂).π.app j₃ ≫ fstProj ψ₃ = fstProj e.inv := by
    rw [fstProj_resStageHom, ← Category.assoc, (pullbackDiagramCone D c i₀ Y₂).w u₂, hψ₂]
  have π_comp :
      ∀ {Z₁ Z₂ Z₃ : FiniteEtaleScheme (D.obj i₀)} {j : Over i₀}
        (α : (pullback (c.π.app i₀)).obj Z₁ ⟶ (pullback (c.π.app i₀)).obj Z₂)
        (γ : (pullback (c.π.app i₀)).obj Z₂ ⟶ (pullback (c.π.app i₀)).obj Z₃)
        (βα : (pullback (D.map j.hom)).obj Z₁ ⟶ (pullback (D.map j.hom)).obj Z₂)
        (βγ : (pullback (D.map j.hom)).obj Z₂ ⟶ (pullback (D.map j.hom)).obj Z₃),
        (pullbackDiagramCone D c i₀ Z₁).π.app j ≫ fstProj βα = fstProj α →
        (pullbackDiagramCone D c i₀ Z₂).π.app j ≫ fstProj βγ = fstProj γ →
        (pullbackDiagramCone D c i₀ Z₁).π.app j ≫ fstProj (βα ≫ βγ) = fstProj (α ≫ γ) := by
    intro Z₁ Z₂ Z₃ j α γ βα βγ hβα hβγ
    have hcomm :
        (pullbackDiagramCone D c i₀ Z₁).π.app j ≫ homLeft βα =
          homLeft α ≫ (pullbackDiagramCone D c i₀ Z₂).π.app j := by
      dsimp [pullbackDiagramCone]
      apply Limits.pullback.hom_ext
      · simpa [fstProj] using hβα
      · rw [Category.assoc, homLeft_snd, Limits.pullback.lift_snd,
          Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, homLeft_snd]
    rw [fstProj, fstProj, homLeft_comp, homLeft_comp,
      ← Category.assoc ((pullbackDiagramCone D c i₀ Z₁).π.app j),
      ← Category.assoc ((pullbackDiagramCone D c i₀ Z₁).π.app j),
      hcomm, Category.assoc, Category.assoc]
    exact congr(homLeft α ≫ $hβγ)
  have hcomp₁ :
      (pullbackDiagramCone D c i₀ Y₁).π.app j₃ ≫ fstProj (φ₃ ≫ ψ₃) =
        (pullbackDiagramCone D c i₀ Y₁).π.app j₃ ≫ fstProj (𝟙 _) := by
    rw [π_comp e.hom e.inv φ₃ ψ₃ hφ₃ hψ₃, e.hom_inv_id, fstProj, fstProj, homLeft_id, homLeft_id]
    simp [pullbackDiagramCone]
  obtain ⟨j₄, u₃, hu₃⟩ := eq_hom j₃ (φ₃ ≫ ψ₃) (𝟙 _) hcomp₁
  let φ₄ := resStageHom D u₃ φ₃
  let ψ₄ := resStageHom D u₃ ψ₃
  have hφ₄ψ₄ : φ₄ ≫ ψ₄ = 𝟙 _ := by
    rw [← resStageHom_comp, hu₃, resStageHom_id]
  have hφ₄ : (pullbackDiagramCone D c i₀ Y₁).π.app j₄ ≫ fstProj φ₄ = fstProj e.hom := by
    rw [fstProj_resStageHom, ← Category.assoc, (pullbackDiagramCone D c i₀ Y₁).w u₃, hφ₃]
  have hψ₄ : (pullbackDiagramCone D c i₀ Y₂).π.app j₄ ≫ fstProj ψ₄ = fstProj e.inv := by
    rw [fstProj_resStageHom, ← Category.assoc, (pullbackDiagramCone D c i₀ Y₂).w u₃, hψ₃]
  have hcomp₂ :
      (pullbackDiagramCone D c i₀ Y₂).π.app j₄ ≫ fstProj (ψ₄ ≫ φ₄) =
        (pullbackDiagramCone D c i₀ Y₂).π.app j₄ ≫ fstProj (𝟙 _) := by
    rw [π_comp e.inv e.hom ψ₄ φ₄ hψ₄ hφ₄, e.inv_hom_id, fstProj, fstProj, homLeft_id, homLeft_id]
    simp [pullbackDiagramCone]
  obtain ⟨j₅, u₄, hu₄⟩ := eq_hom j₄ (ψ₄ ≫ φ₄) (𝟙 _) hcomp₂
  let φ₅ := resStageHom D u₄ φ₄
  let ψ₅ := resStageHom D u₄ ψ₄
  refine ⟨j₅.left, j₅.hom, ⟨{
    hom := φ₅
    inv := ψ₅
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
    (eGlue :
      (pullback (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left)).obj V ≅
        (pullback (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right)).obj YW) :
    ∃ V' : FiniteEtaleScheme (U ⊔ W).toScheme,
      Nonempty ((pullback (X.homOfLE le_sup_left)).obj V' ≅ V) := by
  let Dglue : BinaryOpenGluingData U W :=
    { left := V.obj.left
      leftHom := V.obj.hom
      right := YW.obj.left
      rightHom := YW.obj.hom
      iso :=
        { hom := eGlue.hom.hom.left
          inv := eGlue.inv.hom.left
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
  let eLeft :
      (Over.pullback (X.homOfLE (U := U) (V := U ⊔ W) le_sup_left)).obj
          (Over.mk Dglue.toBase) ≅ V.obj :=
    Over.isoMk Dglue.pullbackLeftIso Dglue.pullbackLeftIso_hom_leftHom
  exact ⟨ofHom Dglue.toBase,
    ⟨ObjectProperty.isoMk _ (eqToIso (by simp only [pullback_obj_obj, ofHom_obj]) ≪≫ eLeft)⟩⟩

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
  let U₀' : W₀.opens.toScheme.Opens := W₀.opens.ι ⁻¹ᵁ U
  have hU₀_compact' : IsCompact (U₀' : Set W₀.opens.toScheme) := by
    have hUW : IsCompact ((U.ι ⁻¹ᵁ W₀.opens : U.toScheme.Opens) : Set U.toScheme) :=
      U.ι.isCompact_preimage W₀.isAffineOpen.isCompact
    have himg :
        W₀.opens.ι.base '' (U₀' : Set W₀.opens.toScheme) =
          U.ι.base '' ((U.ι ⁻¹ᵁ W₀.opens : U.toScheme.Opens) : Set U.toScheme) := by
      ext x
      constructor
      · rintro ⟨⟨y, hyW⟩, hyU, rfl⟩
        exact ⟨⟨y, hyU⟩, hyW, rfl⟩
      · rintro ⟨⟨y, hyU⟩, hyW, rfl⟩
        exact ⟨⟨y, hyW⟩, hyU, rfl⟩
    exact W₀.opens.ι.isOpenEmbedding.isInducing.isCompact_iff.mpr (himg ▸ hUW.image U.ι.continuous)
  let U₀ : ((X.affineOpenNhdsDiagram s).obj W₀).Opens := U₀'
  have hU₀_compact : IsCompact (U₀ : Set ((X.affineOpenNhdsDiagram s).obj W₀)) := hU₀_compact'
  let DO := opensDiagram (X.affineOpenNhdsDiagram s) W₀ U₀
  let cO := opensCone (X.affineOpenNhdsDiagram s) (X.specStalkCone s) W₀ U₀
  have (j : Over W₀) : CompactSpace (DO.obj j) :=
    isCompact_iff_compactSpace.mp
      (((X.affineOpenNhdsDiagram s).map j.hom).isCompact_preimage hU₀_compact)
  have (j : Over W₀) : QuasiSeparatedSpace (DO.obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _
      ((X.affineOpenNhdsDiagram s).map j.hom ⁻¹ᵁ U₀).2).mp (.of_quasiSeparatedSpace _)
  let j₀ : Over W₀ := Over.mk (𝟙 W₀)
  let U₁' : W₀.opens.toScheme.Opens :=
    X.homOfLE (U := W₀.opens) (V := W₀.opens) (leOfHom (𝟙 W₀)) ⁻¹ᵁ U₀'
  let ej₀ : DO.obj j₀ ≅ U₁'.toScheme := eqToIso rfl
  let fV : DO.obj j₀ ⟶ U.toScheme :=
    ej₀.hom ≫
      (X.homOfLE (U := W₀.opens) (V := W₀.opens) (leOfHom (𝟙 W₀))).resLE U₀' U₁' le_rfl ≫
      W₀.opens.ι.resLE U U₀' le_rfl
  let fW : DO.obj j₀ ⟶ W₀.opens.toScheme :=
    ej₀.hom ≫
      (X.homOfLE (U := W₀.opens) (V := W₀.opens) (leOfHom (𝟙 W₀))).resLE U₀' U₁' le_rfl ≫
      U₀'.ι
  have hfVW : fV ≫ U.ι = fW ≫ W₀.opens.ι := by
    dsimp only [fV, fW]
    rw [Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc]
  let Y₁ : FiniteEtaleScheme (DO.obj j₀) := (pullback fV).obj V
  let Y₂ : FiniteEtaleScheme (DO.obj j₀) := (pullback fW).obj YW₀
  let Us' : (Spec (X.presheaf.stalk s)).Opens := W₀.opens.fromSpecStalkOfMem s W₀.mem ⁻¹ᵁ U₀'
  let ePt : Us'.toScheme ≅ cO.pt := eqToIso rfl
  have hpt' : Us' = X.fromSpecStalk s ⁻¹ᵁ U := by
    dsimp only [Us', U₀']
    rw [← Scheme.Hom.comp_preimage, Scheme.Opens.fromSpecStalkOfMem_ι]
  let iPt : cO.pt ⟶ (X.fromSpecStalk s ⁻¹ᵁ U).toScheme :=
    ePt.inv ≫ (Spec (X.presheaf.stalk s)).homOfLE hpt'.le
  have hπW' :
      (ePt.hom ≫ cO.π.app j₀ ≫ ej₀.hom) ≫
          (X.homOfLE (U := W₀.opens) (V := W₀.opens) (leOfHom (𝟙 W₀))).resLE U₀' U₁' le_rfl ≫
          U₀'.ι =
        ((Spec (X.presheaf.stalk s)).homOfLE hpt'.le ≫ (X.fromSpecStalk s ⁻¹ᵁ U).ι) ≫
          W₀.opens.fromSpecStalkOfMem s W₀.mem := by
    have heq :
        ePt.hom ≫ cO.π.app j₀ ≫ ej₀.hom =
          (W₀.opens.fromSpecStalkOfMem s W₀.mem).resLE U₁' Us'
            (by rw [← Scheme.Hom.comp_preimage, X.homOfLE_rfl W₀.opens, Category.comp_id]) := by
      simp only [ePt, ej₀]
      rfl
    rw [heq, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
      X.homOfLE_rfl W₀.opens, Category.comp_id, Scheme.homOfLE_ι]
  have hπW :
      cO.π.app j₀ ≫ fW =
        (iPt ≫ (X.fromSpecStalk s ⁻¹ᵁ U).ι) ≫ W₀.opens.fromSpecStalkOfMem s W₀.mem := by
    calc cO.π.app j₀ ≫ fW
      _ = ePt.inv ≫ (ePt.hom ≫ cO.π.app j₀ ≫ ej₀.hom) ≫
            (X.homOfLE (U := W₀.opens) (V := W₀.opens) (leOfHom (𝟙 W₀))).resLE U₀' U₁' le_rfl ≫
            U₀'.ι := by
          simp only [fW, Category.assoc, Iso.inv_hom_id_assoc]
      _ = ePt.inv ≫ ((Spec (X.presheaf.stalk s)).homOfLE hpt'.le ≫ (X.fromSpecStalk s ⁻¹ᵁ U).ι) ≫
            W₀.opens.fromSpecStalkOfMem s W₀.mem := congrArg (ePt.inv ≫ ·) hπW'
      _ = (iPt ≫ (X.fromSpecStalk s ⁻¹ᵁ U).ι) ≫ W₀.opens.fromSpecStalkOfMem s W₀.mem := by
          simp only [iPt, Category.assoc]
  have hπV :
      cO.π.app j₀ ≫ fV =
        iPt ≫ (X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl := by
    rw [← cancel_mono U.ι, Category.assoc, hfVW, ← Category.assoc (cO.π.app j₀), hπW,
      Category.assoc, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc iPt, Scheme.Hom.resLE_comp_ι]
  obtain ⟨eLim⟩ : Nonempty ((pullback (cO.π.app j₀)).obj Y₁ ≅ (pullback (cO.π.app j₀)).obj Y₂) :=
    ⟨(pullbackCompIsoOfEq (cO.π.app j₀) fV _ hπV).app V ≪≫
      ((pullbackCompIsoOfEq iPt
        ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl) _ rfl).app V).symm ≪≫
      (pullback iPt).mapIso e₀ ≪≫
      (pullbackCompIsoOfEq iPt (X.fromSpecStalk s ⁻¹ᵁ U).ι _ rfl).app Ys ≪≫
      (pullback (iPt ≫ (X.fromSpecStalk s ⁻¹ᵁ U).ι)).mapIso eW₀.symm ≪≫
      (pullbackCompIsoOfEq (iPt ≫ (X.fromSpecStalk s ⁻¹ᵁ U).ι)
        (W₀.opens.fromSpecStalkOfMem s W₀.mem) _ rfl).app YW₀ ≪≫
      ((pullbackCompIsoOfEq (cO.π.app j₀) fW _ hπW).app YW₀).symm⟩
  obtain ⟨k, fk, ⟨ek⟩⟩ :=
    exists_iso_pullback_of_isLimit DO cO
      (isLimitOpensCone (X.affineOpenNhdsDiagram s) (X.specStalkCone s)
        (X.isLimitSpecStalkCone s) W₀ U₀)
      Y₁ Y₂ eLim
  let W : X.AffineOpenNhds s := k.left
  let mapk : W.opens.toScheme ⟶ W₀.opens.toScheme :=
    X.homOfLE (U := W.opens) (V := W₀.opens) (leOfHom k.hom)
  let YW : FiniteEtaleScheme W.opens.toScheme := (pullback mapk).obj YW₀
  have hrange :
      Set.range (X.homOfLE (U := U ⊓ W.opens) (V := W.opens) inf_le_right).base =
        Set.range (W.opens.ι ⁻¹ᵁ U).ι.base := by
    rw [← Scheme.Hom.coe_opensRange ((W.opens.ι ⁻¹ᵁ U).ι), Scheme.Opens.opensRange_ι]
    ext w
    simp only [Set.mem_range, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨x, hxU, hxW⟩, hxw⟩
      have hw : x = w.1 := by simpa [Scheme.homOfLE_apply] using congrArg Subtype.val hxw
      subst hw
      exact hxU
    · intro hw
      exact ⟨⟨w.1, hw, w.2⟩, Subtype.ext (Scheme.homOfLE_apply inf_le_right ⟨w.1, hw, w.2⟩)⟩
  let eRange₀ : (U ⊓ W.opens).toScheme ≅ (W.opens.ι ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.isoOfRangeEq
      (X.homOfLE (U := U ⊓ W.opens) (V := W.opens) inf_le_right)
      (W.opens.ι ⁻¹ᵁ U).ι hrange
  let Uk'' : W.opens.toScheme.Opens := mapk ⁻¹ᵁ U₀'
  have hUk' : Uk'' = W.opens.ι ⁻¹ᵁ U := by
    dsimp only [Uk'', mapk, U₀']
    rw [← Scheme.Hom.comp_preimage, X.homOfLE_ι]
  let ekObj : Uk''.toScheme ≅ DO.obj k := eqToIso rfl
  let eRange : (U ⊓ W.opens).toScheme ≅ DO.obj k :=
    eRange₀ ≪≫ W.opens.toScheme.isoOfEq hUk'.symm ≪≫ ekObj
  have hkhom :
      X.homOfLE (U := W.opens) (V := W₀.opens) (leOfHom fk.left) ≫
          X.homOfLE (U := W₀.opens) (V := W₀.opens) (leOfHom (𝟙 W₀)) = mapk :=
    X.homOfLE_homOfLE _ _
  have hmap :
      ekObj.hom ≫ DO.map fk ≫ ej₀.hom =
        (X.homOfLE (U := W.opens) (V := W₀.opens) (leOfHom fk.left)).resLE U₁' Uk''
          (by rw [← Scheme.Hom.comp_preimage, hkhom]) := by
    simp only [ekObj, ej₀]
    rfl
  have heW₀ :
      eRange₀.hom ≫ (W.opens.toScheme.isoOfEq hUk'.symm).hom ≫
          (ekObj.hom ≫ DO.map fk ≫ ej₀.hom) ≫
          (X.homOfLE (U := W₀.opens) (V := W₀.opens) (leOfHom (𝟙 W₀))).resLE U₀' U₁' le_rfl ≫
          U₀'.ι =
        X.homOfLE (U := U ⊓ W.opens) (V := W.opens) inf_le_right ≫ mapk := by
    rw [hmap, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, hkhom,
      Scheme.isoOfEq_hom_ι_assoc, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
  have heW :
      eRange.hom ≫ DO.map fk ≫ fW =
        X.homOfLE (U := U ⊓ W.opens) (V := W.opens) inf_le_right ≫ mapk := by
    calc eRange.hom ≫ DO.map fk ≫ fW
      _ = eRange₀.hom ≫ (W.opens.toScheme.isoOfEq hUk'.symm).hom ≫
            (ekObj.hom ≫ DO.map fk ≫ ej₀.hom) ≫
            (X.homOfLE (U := W₀.opens) (V := W₀.opens) (leOfHom (𝟙 W₀))).resLE U₀' U₁' le_rfl ≫
            U₀'.ι := by
          simp only [eRange, fW, Iso.trans_hom, Category.assoc]
      _ = X.homOfLE (U := U ⊓ W.opens) (V := W.opens) inf_le_right ≫ mapk := heW₀
  have heV :
      eRange.hom ≫ DO.map fk ≫ fV = X.homOfLE (U := U ⊓ W.opens) (V := U) inf_le_left := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hfVW,
      ← Category.assoc (DO.map fk), ← Category.assoc eRange.hom, heW,
      Category.assoc, X.homOfLE_ι, X.homOfLE_ι, X.homOfLE_ι]
  obtain ⟨eGlue⟩ :
      Nonempty ((pullback (X.homOfLE (U := U ⊓ W.opens) (V := U) inf_le_left)).obj V ≅
        (pullback (X.homOfLE (U := U ⊓ W.opens) (V := W.opens) inf_le_right)).obj YW) :=
    ⟨((pullbackCompIsoOfEq eRange.hom (DO.map fk ≫ fV) _ heV).app V).symm ≪≫
      (pullback eRange.hom).mapIso
        ((pullbackComp (DO.map fk) fV).app V ≪≫ ek ≪≫
          ((pullbackComp (DO.map fk) fW).app YW₀).symm) ≪≫
      (pullbackCompIsoOfEq eRange.hom (DO.map fk ≫ fW) _ heW).app YW₀ ≪≫
      (pullbackComp (X.homOfLE inf_le_right) mapk).app YW₀⟩
  obtain ⟨V', hV'⟩ := exists_sup_of_iso_inf V YW eGlue
  exact ⟨W, V', hV'⟩

/-- One extension step across a point `s ∉ U` whose proper specializations all lie in `U` and at
which local purity holds. -/
theorem exists_extend_of_purity_at_point {X : Scheme.{u}} {U : X.Opens} [QuasiCompact U.ι]
    {s : X} (hsU : s ∉ U) (hspec : ∀ ⦃t : X⦄, t ⤳ s → t ≠ s → t ∈ U)
    (hpurity : IsLocalRing.PurityHolds (X.presheaf.stalk s))
    (V : FiniteEtaleScheme U.toScheme) :
    ∃ (W : X.AffineOpenNhds s) (V' : FiniteEtaleScheme (U ⊔ W.opens).toScheme),
      Nonempty ((pullback (X.homOfLE le_sup_left)).obj V' ≅ V) := by
  have hpunc :
      X.fromSpecStalk s ⁻¹ᵁ U = IsLocalRing.puncturedSpectrum (X.presheaf.stalk s) :=
    fromSpecStalk_preimage_eq_puncturedSpectrum_of_specializes hsU hspec
  let toOs :
      (IsLocalRing.puncturedSpectrum (X.presheaf.stalk s)).toScheme ⟶
        (X.fromSpecStalk s ⁻¹ᵁ U).toScheme :=
    (Spec (X.presheaf.stalk s)).homOfLE hpunc.ge
  let fromOs :
      (X.fromSpecStalk s ⁻¹ᵁ U).toScheme ⟶
        (IsLocalRing.puncturedSpectrum (X.presheaf.stalk s)).toScheme :=
    (Spec (X.presheaf.stalk s)).homOfLE hpunc.le
  let gU := (X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl
  obtain ⟨Ys, ⟨eYs⟩⟩ :=
    (IsLocalRing.purityHolds_iff (X.presheaf.stalk s)).mp hpurity ((pullback (toOs ≫ gU)).obj V)
  have hfb : fromOs ≫ toOs = 𝟙 _ := by
    rw [(Spec (X.presheaf.stalk s)).homOfLE_homOfLE, (Spec (X.presheaf.stalk s)).homOfLE_rfl]
  have hfi :
      fromOs ≫ (IsLocalRing.puncturedSpectrum (X.presheaf.stalk s)).ι =
        (X.fromSpecStalk s ⁻¹ᵁ U).ι :=
    (Spec (X.presheaf.stalk s)).homOfLE_ι hpunc.le
  have hgU : fromOs ≫ toOs ≫ gU = gU := by
    rw [← Category.assoc, hfb, Category.id_comp]
  obtain ⟨e₀⟩ : Nonempty ((pullback gU).obj V ≅ (pullback (X.fromSpecStalk s ⁻¹ᵁ U).ι).obj Ys) :=
    ⟨((pullbackCompIsoOfEq fromOs (toOs ≫ gU) gU hgU).app V).symm ≪≫
      (pullback fromOs).mapIso eYs.symm ≪≫
      (pullbackCompIsoOfEq fromOs
        (IsLocalRing.puncturedSpectrum (X.presheaf.stalk s)).ι _ hfi).app Ys⟩
  exact exists_spread_fromSpecStalk V Ys e₀

end SpreadAndGlue

end TauCeti.FiniteEtaleScheme

namespace TauCeti

/-- **Globalization of local purity** (Stacks Project, Lemma 58.21.6): if `X` is a scheme whose
underlying topological space is Noetherian, `U : X.Opens` is an open subscheme, and local purity
holds for `X.presheaf.stalk s` at every point `s ∉ U`, then restriction of finite étale schemes
along `U.ι : U.toScheme ⟶ X` is essentially surjective. -/
@[stacks 0EY7]
theorem finiteEtale_extend_of_purity {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens)
    (hpurity : ∀ s : X, s ∉ U → IsLocalRing.PurityHolds (X.presheaf.stalk s)) :
    (FiniteEtaleScheme.pullback U.ι).EssSurj := by
  suffices h :
      ∀ (U' : X.Opens), U ≤ U' →
        ∀ V' : FiniteEtaleScheme U'.toScheme,
          ∃ Y : FiniteEtaleScheme X, Nonempty ((FiniteEtaleScheme.pullback U'.ι).obj Y ≅ V') from
    ⟨h U le_rfl⟩
  intro U'
  refine WellFounded.fix
    (C := fun U' : X.Opens ↦
      U ≤ U' →
        ∀ V' : FiniteEtaleScheme U'.toScheme,
          ∃ Y : FiniteEtaleScheme X, Nonempty ((FiniteEtaleScheme.pullback U'.ι).obj Y ≅ V'))
    (wellFounded_gt (α := X.Opens)) (fun U' ih hUU' V' ↦ ?_) U'
  by_cases htop : U' = ⊤
  · have hrange : U'.ι.opensRange = ⊤ := by simp [htop]
    have : IsIso U'.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top U'.ι hrange
    refine ⟨(FiniteEtaleScheme.pullback (inv U'.ι)).obj V', ⟨?_⟩⟩
    exact (FiniteEtaleScheme.pullbackCompIsoOfEq U'.ι (inv U'.ι) (𝟙 _) (IsIso.hom_inv_id _)).app V'
      ≪≫ FiniteEtaleScheme.pullbackId.app V'
  · obtain ⟨s, hsU', hspec⟩ := U'.exists_notMem_specializes_imp_mem htop
    have hsU : s ∉ U := fun hs ↦ hsU' (hUU' hs)
    have : NoetherianSpace U'.toScheme := U'.ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact U'.ι := ⟨fun _ _ _ ↦ NoetherianSpace.isCompact _⟩
    obtain ⟨W, V'', ⟨eV''⟩⟩ :=
      FiniteEtaleScheme.exists_extend_of_purity_at_point hsU' hspec (hpurity s hsU) V'
    have hlt : U' < U' ⊔ W.opens := by
      refine lt_of_le_of_ne le_sup_left fun heq ↦ hsU' ?_
      have hsUW : s ∈ U' ⊔ W.opens := Or.inr W.mem
      rwa [← heq] at hsUW
    obtain ⟨Y, ⟨eY⟩⟩ := ih (U' ⊔ W.opens) hlt (hUU'.trans le_sup_left) V''
    refine ⟨Y, ⟨?_⟩⟩
    exact ((FiniteEtaleScheme.pullbackCompIsoOfEq
        (X.homOfLE (U := U') (V := U' ⊔ W.opens) le_sup_left)
        (U' ⊔ W.opens).ι U'.ι (X.homOfLE_ι le_sup_left)).app Y).symm ≪≫
      (FiniteEtaleScheme.pullback (X.homOfLE le_sup_left)).mapIso eY ≪≫ eV''

/-- Formulation of `TauCeti.finiteEtale_extend_of_purity` for Mathlib's morphism-property over
category `(@IsFinite ⊓ @Etale).Over ⊤`. -/
@[stacks 0EY7]
theorem finiteEtaleOver_extend_of_purity {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens)
    (hpurity : ∀ s : X, s ∉ U → IsLocalRing.PurityHolds (X.presheaf.stalk s)) :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι).EssSurj :=
  (FiniteEtaleScheme.essSurj_pullback_iff U.ι).mp (finiteEtale_extend_of_purity U hpurity)

end TauCeti
