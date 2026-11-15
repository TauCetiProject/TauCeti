/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Stalk
import TauCeti.AlgebraicGeometry.FiniteEtale.BaseChange
import TauCeti.AlgebraicGeometry.Gluing.BinaryOpen
import TauCeti.RingTheory.Etale.DirectLimit

/-!
# Spreading out finite étale schemes from stalks and cofiltered limits

Let `X` be a scheme, `U : X.Opens` an open subscheme, and `s : X` a point. This file establishes
the spreading-and-gluing theory for finite étale covers around `Spec 𝒪_{X,s}`:

* **Stalk object descent** (`exists_pullback_fromSpecStalkOfMem_iso`): every finite étale scheme
  over `Spec (X.presheaf.stalk s)` is the pullback of a finite étale scheme over some affine open
  neighbourhood `W₀ : X.AffineOpenNhds s`, obtained from `X.directLimitRingEquivStalk s` and
  `Ring.DirectLimit.finiteEtale_essSurj`.
* **Cofiltered affine-transition limit descent** (`exists_hom_pullback_of_isLimit`,
  `exists_pullback_map_eq_of_isLimit`, `exists_iso_pullback_of_isLimit`): along any cofiltered limit
  of quasi-compact quasi-separated schemes with affine transition morphisms, morphisms, morphism
  equalities, and isomorphisms between pulled-back finite étale schemes descend to a finite stage
  while preserving the limit morphism.
* **Binary open gluing and stalk spreading** (`exists_sup_of_iso_inf`,
  `exists_spread_fromSpecStalk`): when `U.ι` is quasi-compact, a finite étale scheme `V` over
  `U.toScheme` whose pullback to `(X.fromSpecStalk s ⁻¹ᵁ U).toScheme` extends across
  `Spec (X.presheaf.stalk s)` spreads and glues (via `TauCeti.BinaryOpenGluingData`) to a finite
  étale scheme over `(U ⊔ W.opens).toScheme` for some `W : X.AffineOpenNhds s`, compatibly with
  both `V` and the stalk extension.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Lemma 32.4.18](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Lemma 32.10.1](https://stacks.math.columbia.edu/tag/01ZM)
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
@[stacks 01Z4 "for finite étale schemes"]
theorem exists_pullback_fromSpecStalkOfMem_iso {X : Scheme.{u}} (s : X)
    (Ys : FiniteEtaleScheme (Spec (X.presheaf.stalk s))) :
    ∃ (W₀ : X.AffineOpenNhds s) (YW₀ : FiniteEtaleScheme W₀.opens.toScheme),
      Nonempty ((pullback (W₀.opens.fromSpecStalkOfMem s W₀.mem)).obj YW₀ ≅ Ys) := by
  let L := Ring.DirectLimit (X.stalkDirectSystemObj s) (fun U V h ↦ X.stalkDirectSystemMap s U V h)
  let eR : L ≃+* X.presheaf.stalk s := X.directLimitRingEquivStalk s
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
    (specCompPullbackIso (X.stalkDirectSystemObj s W₀) L).app (op AW₀) ≪≫
      (spec (.of L)).mapIso (Iso.op eAW₀).symm ≪≫ eAL
  have hgerm :
      Spec.map φ.hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap (X.stalkDirectSystemObj s W₀) L)) =
        W₀.opens.fromSpecStalkOfMem s W₀.mem ≫ W₀.opens.toSpecΓ := by
    rw [← Spec.map_comp, Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]
    congr 1
    ext x
    exact X.directLimitRingEquivStalk_of s W₀ x
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

private theorem conj_compIso_hom {A B S : Scheme.{u}} {m : A ⟶ B} {g : B ⟶ S} {mg : A ⟶ S}
    (h : m ≫ g = mg) {Y₁ Y₂ : FiniteEtaleScheme S}
    (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    ((pullbackCompIsoOfEq m g mg h).inv.app Y₁ ≫
        (pullback m).map β ≫
        (pullbackCompIsoOfEq m g mg h).hom.app Y₂).hom =
      (Over.pullbackCompIsoOfEq m g mg h).inv.app Y₁.obj ≫
        (Over.pullback m).map β.hom ≫
        (Over.pullbackCompIsoOfEq m g mg h).hom.app Y₂.obj := by
  change ((pullbackCompIsoOfEq m g mg h).inv.app Y₁).hom ≫
      ((pullback m).map β).hom ≫
      ((pullbackCompIsoOfEq m g mg h).hom.app Y₂).hom = _
  rw [pullbackCompIsoOfEq_inv_app_hom, pullback_map_hom, pullbackCompIsoOfEq_hom_app_hom]
  rfl

/-- Along a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
morphisms, any morphism between the pullbacks of two finite étale schemes `Y₁, Y₂` from a stage `i₀`
to the limit descends to a morphism over some stage `j` mapping to `i₀`. -/
@[stacks 01ZM "for finite étale schemes"]
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
  obtain ⟨j, fj, β, hβ⟩ :=
    Scheme.exists_hom_pullback_of_isLimit D c hc Y₁.obj Y₂.obj α.hom
  let β' : (pullback (D.map fj)).obj Y₁ ⟶ (pullback (D.map fj)).obj Y₂ :=
    (finiteEtaleSchemeProperty (D.obj j)).homMk β
  exact ⟨j, fj, β', ObjectProperty.hom_ext _ ((conj_compIso_hom (c.w fj) β').trans hβ)⟩

/-- Along a cofiltered limit of quasi-compact schemes with affine transition morphisms, two
morphisms between finite étale schemes at stage `i₀` that become equal on the limit already become
equal at some stage `k` mapping to `i₀`. -/
@[stacks 01ZM "for finite étale schemes"]
theorem exists_pullback_map_eq_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    (hc : Limits.IsLimit c) {i₀ : I} {Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀)} (β₁ β₂ : Y₁ ⟶ Y₂)
    (h : (pullback (c.π.app i₀)).map β₁ = (pullback (c.π.app i₀)).map β₂) :
    ∃ (k : I) (fk : k ⟶ i₀), (pullback (D.map fk)).map β₁ = (pullback (D.map fk)).map β₂ := by
  obtain ⟨k, fk, hfk⟩ :=
    Scheme.exists_pullback_map_eq_of_isLimit D c hc β₁.hom β₂.hom congr(($h).hom)
  exact ⟨k, fk, ObjectProperty.hom_ext _ hfk⟩

/-- Along a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
morphisms, an isomorphism `e` on the limit between the pullbacks of two finite étale schemes
`Y₁, Y₂` at stage `i₀` descends to an isomorphism `ek` at some stage `k` mapping to `i₀` whose
pullback to the limit recovers `e.hom`. -/
@[stacks 01ZM "for finite étale schemes"]
theorem exists_iso_pullback_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : Limits.IsLimit c) {i₀ : I} (Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀))
    (e : (pullback (c.π.app i₀)).obj Y₁ ≅ (pullback (c.π.app i₀)).obj Y₂) :
    ∃ (k : I) (fk : k ⟶ i₀)
      (ek : (pullback (D.map fk)).obj Y₁ ≅ (pullback (D.map fk)).obj Y₂),
      (pullbackCompIsoOfEq (c.π.app k) (D.map fk) (c.π.app i₀) (c.w fk)).inv.app Y₁ ≫
          (pullback (c.π.app k)).map ek.hom ≫
          (pullbackCompIsoOfEq (c.π.app k) (D.map fk) (c.π.app i₀) (c.w fk)).hom.app Y₂ =
        e.hom := by
  let eOver : (Over.pullback (c.π.app i₀)).obj Y₁.obj ≅
      (Over.pullback (c.π.app i₀)).obj Y₂.obj :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congr(($e.hom_inv_id).hom)
      inv_hom_id := congr(($e.inv_hom_id).hom) }
  obtain ⟨k, fk, ek, hek⟩ :=
    Scheme.exists_iso_pullback_of_isLimit D c hc Y₁.obj Y₂.obj eOver
  let ek' : (pullback (D.map fk)).obj Y₁ ≅ (pullback (D.map fk)).obj Y₂ :=
    (finiteEtaleSchemeProperty (D.obj k)).isoMk ek
  exact ⟨k, fk, ek', ObjectProperty.hom_ext _ ((conj_compIso_hom (c.w fk) ek'.hom).trans hek)⟩

end LimitSpreading

section SpreadAndGlue

section PullbackProj

private def pfst {B S : Scheme.{u}} (Y : FiniteEtaleScheme S) (f : B ⟶ S) :
    ((pullback f).obj Y).obj.left ⟶ Y.obj.left :=
  Limits.pullback.fst Y.obj.hom f

private def psnd {B S : Scheme.{u}} (Y : FiniteEtaleScheme S) (f : B ⟶ S) :
    ((pullback f).obj Y).obj.left ⟶ B :=
  Limits.pullback.snd Y.obj.hom f

private theorem pullback_hom_ext {Z B S : Scheme.{u}} {Y : FiniteEtaleScheme S} {f : B ⟶ S}
    {u₁ u₂ : Z ⟶ ((pullback f).obj Y).obj.left}
    (h₁ : u₁ ≫ pfst Y f = u₂ ≫ pfst Y f) (h₂ : u₁ ≫ psnd Y f = u₂ ≫ psnd Y f) :
    u₁ = u₂ :=
  Limits.pullback.hom_ext h₁ h₂

private def pm {A B S : Scheme.{u}} (Y : FiniteEtaleScheme S) (fA : A ⟶ S) (fB : B ⟶ S)
    (m : A ⟶ B) (hm : m ≫ fB = fA) :
    ((pullback fA).obj Y).obj.left ⟶ ((pullback fB).obj Y).obj.left :=
  Limits.pullback.map Y.obj.hom fA Y.obj.hom fB (𝟙 Y.obj.left) m (𝟙 S) (by simp) (by simp [hm])

@[reassoc (attr := simp)]
private theorem pm_pfst {A B S : Scheme.{u}} (Y : FiniteEtaleScheme S) (fA : A ⟶ S) (fB : B ⟶ S)
    (m : A ⟶ B) (hm : m ≫ fB = fA) :
    pm Y fA fB m hm ≫ pfst Y fB = pfst Y fA := by
  change Limits.pullback.map Y.obj.hom fA Y.obj.hom fB (𝟙 Y.obj.left) m (𝟙 S)
        (by simp) (by simp [hm]) ≫
      Limits.pullback.fst Y.obj.hom fB =
    Limits.pullback.fst Y.obj.hom fA
  simp

@[reassoc (attr := simp)]
private theorem pm_psnd {A B S : Scheme.{u}} (Y : FiniteEtaleScheme S) (fA : A ⟶ S) (fB : B ⟶ S)
    (m : A ⟶ B) (hm : m ≫ fB = fA) :
    pm Y fA fB m hm ≫ psnd Y fB = psnd Y fA ≫ m := by
  change Limits.pullback.map Y.obj.hom fA Y.obj.hom fB (𝟙 Y.obj.left) m (𝟙 S)
        (by simp) (by simp [hm]) ≫
      Limits.pullback.snd Y.obj.hom fB =
    Limits.pullback.snd Y.obj.hom fA ≫ m
  simp

private theorem pm_id {A S : Scheme.{u}} (Y : FiniteEtaleScheme S) (f : A ⟶ S) :
    pm Y f f (𝟙 A) (Category.id_comp f) = 𝟙 _ := by
  apply pullback_hom_ext <;> simp

@[reassoc]
private theorem pm_comp {A B C S : Scheme.{u}} (Y : FiniteEtaleScheme S)
    {fA : A ⟶ S} {fB : B ⟶ S} {fC : C ⟶ S} {m₁ : A ⟶ B} {m₂ : B ⟶ C}
    (hm₁ : m₁ ≫ fB = fA) (hm₂ : m₂ ≫ fC = fB) :
    pm Y fA fB m₁ hm₁ ≫ pm Y fB fC m₂ hm₂ =
      pm Y fA fC (m₁ ≫ m₂) (by rw [Category.assoc, hm₂, hm₁]) := by
  apply pullback_hom_ext <;> simp

private theorem pm_congr {A B S : Scheme.{u}} (Y : FiniteEtaleScheme S) (fA : A ⟶ S) (fB : B ⟶ S)
    {m₁ m₂ : A ⟶ B} (h : m₁ = m₂) (hm₁ : m₁ ≫ fB = fA) (hm₂ : m₂ ≫ fB = fA) :
    pm Y fA fB m₁ hm₁ = pm Y fA fB m₂ hm₂ := by
  subst h; rfl

private def proj {B S : Scheme.{u}} {g : B ⟶ S} {Z : FiniteEtaleScheme B}
    {Y : FiniteEtaleScheme S} (φ : Z ⟶ (pullback g).obj Y) : Z.obj.left ⟶ Y.obj.left :=
  φ.hom.left ≫ pfst Y g

private theorem proj_comp {B S : Scheme.{u}} {g : B ⟶ S}
    {X Z : FiniteEtaleScheme B} {Y : FiniteEtaleScheme S}
    (α : X ⟶ Z) (β : Z ⟶ (pullback g).obj Y) :
    proj (α ≫ β) = α.hom.left ≫ proj β :=
  Category.assoc _ _ _

private theorem hom_ext_proj {B S : Scheme.{u}} {g : B ⟶ S} {Z : FiniteEtaleScheme B}
    {Y : FiniteEtaleScheme S} {φ₁ φ₂ : Z ⟶ (pullback g).obj Y}
    (h : proj φ₁ = proj φ₂) : φ₁ = φ₂ :=
  ObjectProperty.hom_ext _ <| Over.OverMorphism.ext <|
    pullback_hom_ext h ((Over.w φ₁.hom).trans (Over.w φ₂.hom).symm)

@[reassoc]
private theorem pullback_map_pfst {B S : Scheme.{u}} (f : B ⟶ S)
    {Y₁ Y₂ : FiniteEtaleScheme S} (α : Y₁ ⟶ Y₂) :
    ((pullback f).map α).hom.left ≫ pfst Y₂ f = pfst Y₁ f ≫ α.hom.left :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
private theorem pullback_map_psnd {B S : Scheme.{u}} (f : B ⟶ S)
    {Y₁ Y₂ : FiniteEtaleScheme S} (α : Y₁ ⟶ Y₂) :
    ((pullback f).map α).hom.left ≫ psnd Y₂ f = psnd Y₁ f :=
  Limits.pullback.lift_snd _ _ _

@[reassoc]
private theorem comp_compIso_hom_left_pfst {A B C : Scheme.{u}}
    {m : A ⟶ B} {b : B ⟶ C} {ab : A ⟶ C} (hab : m ≫ b = ab)
    {Z : FiniteEtaleScheme A} (Y : FiniteEtaleScheme C)
    (ψ : Z ⟶ (pullback m).obj ((pullback b).obj Y)) :
    (ψ ≫ (pullbackCompIsoOfEq m b ab hab).hom.app Y).hom.left ≫ pfst Y ab =
      ψ.hom.left ≫ pfst ((pullback b).obj Y) m ≫ pfst Y b :=
  calc
    (ψ.hom.left ≫ ((pullbackCompIsoOfEq m b ab hab).hom.app Y).hom.left) ≫ pfst Y ab
      = ψ.hom.left ≫ (((pullbackCompIsoOfEq m b ab hab).hom.app Y).hom.left ≫ pfst Y ab) :=
        Category.assoc _ _ _
    _ = ψ.hom.left ≫ (pfst ((pullback b).obj Y) m ≫ pfst Y b) :=
        congrArg (ψ.hom.left ≫ ·) (pullbackCompIsoOfEq_hom_app_hom_left_fst hab Y)

@[reassoc]
private theorem compIso_inv_map_left_pfst {A B C : Scheme.{u}}
    {m : A ⟶ B} {b : B ⟶ C} {ab : A ⟶ C} (hab : m ≫ b = ab)
    (Y : FiniteEtaleScheme C) {Z : FiniteEtaleScheme B} (φ : (pullback b).obj Y ⟶ Z) :
    ((pullbackCompIsoOfEq m b ab hab).inv.app Y ≫ (pullback m).map φ).hom.left ≫ pfst Z m =
      pm Y ab b m hab ≫ φ.hom.left :=
  calc
    (((pullbackCompIsoOfEq m b ab hab).inv.app Y).hom.left ≫ ((pullback m).map φ).hom.left) ≫
        pfst Z m
      = ((pullbackCompIsoOfEq m b ab hab).inv.app Y).hom.left ≫
          (((pullback m).map φ).hom.left ≫ pfst Z m) := Category.assoc _ _ _
    _ = ((pullbackCompIsoOfEq m b ab hab).inv.app Y).hom.left ≫
          (Limits.pullback.fst (Limits.pullback.snd Y.obj.hom b) m ≫ φ.hom.left) :=
        congrArg _ (pullback_map_pfst m φ)
    _ = (((pullbackCompIsoOfEq m b ab hab).inv.app Y).hom.left ≫
          Limits.pullback.fst (Limits.pullback.snd Y.obj.hom b) m) ≫ φ.hom.left :=
        (Category.assoc _ _ _).symm
    _ = pm Y ab b m hab ≫ φ.hom.left :=
        congrArg (· ≫ φ.hom.left) (pullbackCompIsoOfEq_inv_app_hom_left_fst hab Y)

@[reassoc]
private theorem compIso_inv_map_left_psnd {A B C : Scheme.{u}}
    {m : A ⟶ B} {b : B ⟶ C} {ab : A ⟶ C} (hab : m ≫ b = ab)
    (Y : FiniteEtaleScheme C) {Z : FiniteEtaleScheme B} (φ : (pullback b).obj Y ⟶ Z) :
    ((pullbackCompIsoOfEq m b ab hab).inv.app Y ≫ (pullback m).map φ).hom.left ≫ psnd Z m =
      psnd Y ab :=
  calc
    (((pullbackCompIsoOfEq m b ab hab).inv.app Y).hom.left ≫ ((pullback m).map φ).hom.left) ≫
        psnd Z m
      = ((pullbackCompIsoOfEq m b ab hab).inv.app Y).hom.left ≫
          (((pullback m).map φ).hom.left ≫ psnd Z m) := Category.assoc _ _ _
    _ = ((pullbackCompIsoOfEq m b ab hab).inv.app Y).hom.left ≫
          Limits.pullback.snd (Limits.pullback.snd Y.obj.hom b) m :=
        congrArg _ (pullback_map_psnd m φ)
    _ = psnd Y ab := pullbackCompIsoOfEq_inv_app_hom_left_snd hab Y

private theorem proj_conj_compIso {A B S₁ S₂ : Scheme.{u}} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {h₁ : A ⟶ S₁} {h₂ : A ⟶ S₂}
    (hm₁ : m ≫ g₁ = h₁) (hm₂ : m ≫ g₂ = h₂)
    {Y₁ : FiniteEtaleScheme S₁} {Y₂ : FiniteEtaleScheme S₂}
    (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    proj ((pullbackCompIsoOfEq m g₁ h₁ hm₁).inv.app Y₁ ≫
        (pullback m).map φ ≫
        (pullbackCompIsoOfEq m g₂ h₂ hm₂).hom.app Y₂) =
      pm Y₁ h₁ g₁ m hm₁ ≫ proj φ :=
  calc
    proj ((pullbackCompIsoOfEq m g₁ h₁ hm₁).inv.app Y₁ ≫
        (pullback m).map φ ≫
        (pullbackCompIsoOfEq m g₂ h₂ hm₂).hom.app Y₂)
      = proj (((pullbackCompIsoOfEq m g₁ h₁ hm₁).inv.app Y₁ ≫ (pullback m).map φ) ≫
          (pullbackCompIsoOfEq m g₂ h₂ hm₂).hom.app Y₂) :=
        congrArg proj (Category.assoc _ _ _).symm
    _ = ((pullbackCompIsoOfEq m g₁ h₁ hm₁).inv.app Y₁ ≫ (pullback m).map φ).hom.left ≫
          pfst ((pullback g₂).obj Y₂) m ≫ pfst Y₂ g₂ :=
        comp_compIso_hom_left_pfst hm₂ Y₂ _
    _ = pm Y₁ h₁ g₁ m hm₁ ≫ proj φ := by
        rw [compIso_inv_map_left_pfst_assoc]; rfl

private def cInv {A B S : Scheme.{u}} (a : A ⟶ B) (f : B ⟶ S) (Y : FiniteEtaleScheme S) :
    ((pullback (a ≫ f)).obj Y).obj.left ⟶ ((pullback a).obj ((pullback f).obj Y)).obj.left :=
  ((pullbackCompIsoOfEq a f (a ≫ f) rfl).inv.app Y).hom.left

@[reassoc (attr := simp)]
private theorem cInv_pfst {A B S : Scheme.{u}} (a : A ⟶ B) (f : B ⟶ S)
    (Y : FiniteEtaleScheme S) :
    cInv a f Y ≫ pfst ((pullback f).obj Y) a = pm Y (a ≫ f) f a rfl :=
  pullbackCompIsoOfEq_inv_app_hom_left_fst rfl Y

@[reassoc (attr := simp)]
private theorem cInv_psnd {A B S : Scheme.{u}} (a : A ⟶ B) (f : B ⟶ S)
    (Y : FiniteEtaleScheme S) :
    cInv a f Y ≫ psnd ((pullback f).obj Y) a = psnd Y (a ≫ f) :=
  pullbackCompIsoOfEq_inv_app_hom_left_snd rfl Y

@[reassoc]
private theorem pm_cInv {A₁ A₂ B S : Scheme.{u}}
    {k : A₁ ⟶ A₂} {a₂ : A₂ ⟶ B} {a₁ : A₁ ⟶ B} (hk : k ≫ a₂ = a₁)
    (f : B ⟶ S) (Y : FiniteEtaleScheme S) :
    pm Y (a₁ ≫ f) (a₂ ≫ f) k (by rw [← Category.assoc, hk]) ≫ cInv a₂ f Y =
      cInv a₁ f Y ≫ pm ((pullback f).obj Y) a₁ a₂ k hk := by
  apply pullback_hom_ext <;> simp [pm_comp, pm_congr Y _ _ hk]

private theorem proj_flat {A B S₁ S₂ : Scheme.{u}} (a : A ⟶ B) (f₁ : B ⟶ S₁) (f₂ : B ⟶ S₂)
    {Y₁ : FiniteEtaleScheme S₁} {Y₂ : FiniteEtaleScheme S₂}
    (u : (pullback a).obj ((pullback f₁).obj Y₁) ⟶ (pullback a).obj ((pullback f₂).obj Y₂)) :
    proj ((pullbackCompIsoOfEq a f₁ (a ≫ f₁) rfl).inv.app Y₁ ≫
        u ≫
        (pullbackCompIsoOfEq a f₂ (a ≫ f₂) rfl).hom.app Y₂) =
      cInv a f₁ Y₁ ≫ proj u ≫ pfst Y₂ f₂ :=
  calc
    proj ((pullbackCompIsoOfEq a f₁ (a ≫ f₁) rfl).inv.app Y₁ ≫
        u ≫
        (pullbackCompIsoOfEq a f₂ (a ≫ f₂) rfl).hom.app Y₂)
      = proj (((pullbackCompIsoOfEq a f₁ (a ≫ f₁) rfl).inv.app Y₁ ≫ u) ≫
          (pullbackCompIsoOfEq a f₂ (a ≫ f₂) rfl).hom.app Y₂) :=
        congrArg proj (Category.assoc _ _ _).symm
    _ = (cInv a f₁ Y₁ ≫ u.hom.left) ≫ (pfst ((pullback f₂).obj Y₂) a ≫ pfst Y₂ f₂) :=
        comp_compIso_hom_left_pfst rfl Y₂ _
    _ = cInv a f₁ Y₁ ≫ proj u ≫ pfst Y₂ f₂ :=
        (Category.assoc _ _ _).trans
          (congrArg (cInv a f₁ Y₁ ≫ ·) (Category.assoc _ _ _).symm)

private theorem pm_comp_compIso_inv_map {A₀ A B C : Scheme.{u}}
    {n : A₀ ⟶ A} {m : A ⟶ B} {b : B ⟶ C} {ab : A ⟶ C} {a₀b : A₀ ⟶ C} {nm : A₀ ⟶ B}
    (hab : m ≫ b = ab) (hn_ab : n ≫ ab = a₀b) (hnm : n ≫ m = nm) (hnm_b : nm ≫ b = a₀b)
    (Y : FiniteEtaleScheme C) {Z : FiniteEtaleScheme B} (φ : (pullback b).obj Y ⟶ Z) :
    pm Y a₀b ab n hn_ab ≫
        ((pullbackCompIsoOfEq m b ab hab).inv.app Y ≫ (pullback m).map φ).hom.left =
      ((pullbackCompIsoOfEq nm b a₀b hnm_b).inv.app Y ≫ (pullback nm).map φ).hom.left ≫
        pm Z nm m n hnm := by
  apply pullback_hom_ext
  · rw [Category.assoc, compIso_inv_map_left_pfst, Category.assoc, pm_pfst,
      compIso_inv_map_left_pfst, pm_comp_assoc Y, pm_congr Y _ _ hnm]
  · rw [Category.assoc, compIso_inv_map_left_psnd, pm_psnd, Category.assoc, pm_psnd,
      compIso_inv_map_left_psnd_assoc]

end PullbackProj

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
      (pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
          (X.homOfLE le_sup_left)
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
          (X.homOfLE_homOfLE _ _)).inv.app V' ≫
        (pullback (X.homOfLE inf_le_left)).map eU.hom ≫ eGlue.hom =
      (pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right)
          (X.homOfLE le_sup_right)
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
          (X.homOfLE_homOfLE _ _)).inv.app V' ≫
        (pullback (X.homOfLE inf_le_right)).map eW.hom := by
  let Dglue : BinaryOpenGluingData U W :=
    { left := V.obj.left, leftHom := V.obj.hom, right := YW.obj.left, rightHom := YW.obj.hom
      iso := { hom := eGlue.hom.hom.left, inv := eGlue.inv.hom.left
               hom_inv_id := congr(($eGlue.hom_inv_id).hom.left)
               inv_hom_id := congr(($eGlue.inv_hom_id).hom.left) }
      iso_hom_snd := Over.w eGlue.hom.hom }
  have : IsZariskiLocalAtTarget @IsIntegralHom.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  have : IsZariskiLocalAtTarget @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FiniteType)
  have : IsZariskiLocalAtTarget @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.Etale)
  have : IsFinite Dglue.toBase :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType Dglue.toBase).mpr
      ⟨Dglue.morphismProperty_toBase (@IsIntegralHom) inferInstance inferInstance,
       Dglue.morphismProperty_toBase (@LocallyOfFiniteType) inferInstance inferInstance⟩
  have : Etale Dglue.toBase :=
    Dglue.morphismProperty_toBase (@Etale) inferInstance inferInstance
  let V' : FiniteEtaleScheme (U ⊔ W).toScheme :=
    ⟨Over.mk Dglue.toBase,
      (finiteEtaleSchemeProperty_iff _).mpr ⟨‹IsFinite Dglue.toBase›, ‹Etale Dglue.toBase›⟩⟩
  let eU : (pullback (X.homOfLE le_sup_left)).obj V' ≅ V :=
    (finiteEtaleSchemeProperty U.toScheme).isoMk
      (Over.isoMk Dglue.pullbackLeftIso Dglue.pullbackLeftIso_hom_leftHom)
  let eW : (pullback (X.homOfLE le_sup_right)).obj V' ≅ YW :=
    (finiteEtaleSchemeProperty W.toScheme).isoMk
      (Over.isoMk Dglue.pullbackRightIso Dglue.pullbackRightIso_hom_rightHom)
  refine ⟨V', eU, eW, hom_ext_proj ?_⟩
  rw [← cancel_mono Dglue.ιRight]
  have hL : eU.hom.hom.left ≫ Dglue.ιLeft = pfst V' (X.homOfLE le_sup_left) :=
    Dglue.pullbackLeftIso_hom_ιLeft
  have hR : eW.hom.hom.left ≫ Dglue.ιRight = pfst V' (X.homOfLE le_sup_right) :=
    Dglue.pullbackRightIso_hom_ιRight
  have hglue :
      proj eGlue.hom ≫ Dglue.ιRight =
        pfst V (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ≫ Dglue.ιLeft := by
    change (Dglue.iso.hom ≫
        Limits.pullback.fst Dglue.rightHom (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right)) ≫
        Dglue.ιRight =
      Limits.pullback.fst Dglue.leftHom (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ≫ Dglue.ιLeft
    exact (Category.assoc _ _ _).trans Dglue.fst_ιLeft.symm
  rw [← Category.assoc ((pullbackCompIsoOfEq (X.homOfLE inf_le_left) _ _ _).inv.app V'),
    proj_comp, Category.assoc, hglue, compIso_inv_map_left_pfst_assoc, hL, pm_pfst]
  rw [proj, Category.assoc, compIso_inv_map_left_pfst_assoc, hR, pm_pfst]

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
    (e₀ :
      (pullback ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl)).obj V ≅
        (pullback (X.fromSpecStalk s ⁻¹ᵁ U).ι).obj Ys) :
    ∃ (W : X.AffineOpenNhds s) (V' : FiniteEtaleScheme (U ⊔ W.opens).toScheme)
      (eU : (pullback (X.homOfLE le_sup_left)).obj V' ≅ V)
      (es :
        (pullback ((U ⊔ W.opens).fromSpecStalkOfMem s
          (show s ∈ U ⊔ W.opens from Or.inr W.mem))).obj V' ≅ Ys),
      (pullbackCompIsoOfEq ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl)
          (X.homOfLE le_sup_left)
          ((X.fromSpecStalk s ⁻¹ᵁ U).ι ≫
            (U ⊔ W.opens).fromSpecStalkOfMem s (show s ∈ U ⊔ W.opens from Or.inr W.mem))
          (by
            rw [← cancel_mono (U ⊔ W.opens).ι, Category.assoc, Category.assoc, X.homOfLE_ι,
              Scheme.Hom.resLE_comp_ι, (U ⊔ W.opens).fromSpecStalkOfMem_ι])).inv.app V' ≫
        (pullback ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl)).map eU.hom ≫
        e₀.hom =
      (pullbackCompIsoOfEq (X.fromSpecStalk s ⁻¹ᵁ U).ι
          ((U ⊔ W.opens).fromSpecStalkOfMem s (show s ∈ U ⊔ W.opens from Or.inr W.mem))
          _ rfl).inv.app V' ≫
        (pullback (X.fromSpecStalk s ⁻¹ᵁ U).ι).map es.hom := by
  obtain ⟨W₀, YW₀, ⟨eW₀⟩⟩ := exists_pullback_fromSpecStalkOfMem_iso s Ys
  let DO := X.stalkOpensDiagram U s W₀
  let cO := X.stalkOpensCone U s W₀
  let j₀ : Over W₀ := Over.mk (𝟙 W₀)
  let fV := X.stalkOpensTopToOpen U s W₀
  let fW := X.stalkOpensTopToNhds U s W₀
  let iPt := (X.stalkOpensConePtIso U s W₀).hom
  let iPtInv := (X.stalkOpensConePtIso U s W₀).inv
  let gU := (X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl
  let ιOs := (X.fromSpecStalk s ⁻¹ᵁ U).ι
  let sW₀ := W₀.opens.fromSpecStalkOfMem s W₀.mem
  let e₀' : (pullback gU).obj V ≅ (pullback (ιOs ≫ sW₀)).obj YW₀ :=
    e₀ ≪≫ (pullback ιOs).mapIso eW₀.symm ≪≫
      (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).app YW₀
  have htopV : iPt ≫ gU = cO.π.app j₀ ≫ fV := (X.stalkOpensCone_π_top_toOpen U s W₀).symm
  have htopW : iPt ≫ (ιOs ≫ sW₀) = cO.π.app j₀ ≫ fW := by
    simpa only [Category.assoc] using (X.stalkOpensCone_π_top_toNhds U s W₀).symm
  let eLimFlat : (pullback (cO.π.app j₀ ≫ fV)).obj V ≅
      (pullback (cO.π.app j₀ ≫ fW)).obj YW₀ :=
    ((pullbackCompIsoOfEq iPt gU _ htopV).app V).symm ≪≫
      (pullback iPt).mapIso e₀' ≪≫
      (pullbackCompIsoOfEq iPt (ιOs ≫ sW₀) _ htopW).app YW₀
  let eLim : (pullback (cO.π.app j₀)).obj ((pullback fV).obj V) ≅
      (pullback (cO.π.app j₀)).obj ((pullback fW).obj YW₀) :=
    (pullbackCompIsoOfEq (cO.π.app j₀) fV _ rfl).app V ≪≫
      eLimFlat ≪≫
      ((pullbackCompIsoOfEq (cO.π.app j₀) fW _ rfl).app YW₀).symm
  obtain ⟨k, fk, ek, hek⟩ :=
    exists_iso_pullback_of_isLimit DO cO (X.isLimitStalkOpensCone U s W₀)
      ((pullback fV).obj V) ((pullback fW).obj YW₀) eLim
  let W : X.AffineOpenNhds s := k.left
  let mapk : W.opens.toScheme ⟶ W₀.opens.toScheme :=
    X.homOfLE (Scheme.AffineOpenNhds.le_iff.mp (leOfHom k.hom))
  let YW : FiniteEtaleScheme W.opens.toScheme := (pullback mapk).obj YW₀
  let eRange := X.stalkOpensStageIso U s k
  let iU := X.homOfLE (U := U ⊓ W.opens) (V := U) inf_le_left
  let iW := X.homOfLE (U := U ⊓ W.opens) (V := W.opens) inf_le_right
  let ekFlat : (pullback (DO.map fk ≫ fV)).obj V ≅ (pullback (DO.map fk ≫ fW)).obj YW₀ :=
    ((pullbackCompIsoOfEq (DO.map fk) fV _ rfl).app V).symm ≪≫
      ek ≪≫
      (pullbackCompIsoOfEq (DO.map fk) fW _ rfl).app YW₀
  have hstageV : eRange.hom ≫ (DO.map fk ≫ fV) = iU := X.stalkOpensStageIso_hom_map_toOpen U s fk
  have hstageW : eRange.hom ≫ (DO.map fk ≫ fW) = iW ≫ mapk :=
    X.stalkOpensStageIso_hom_map_toNhds U s fk
  let eGlueFlat : (pullback iU).obj V ≅ (pullback (iW ≫ mapk)).obj YW₀ :=
    ((pullbackCompIsoOfEq eRange.hom (DO.map fk ≫ fV) iU hstageV).app V).symm ≪≫
      (pullback eRange.hom).mapIso ekFlat ≪≫
      (pullbackCompIsoOfEq eRange.hom (DO.map fk ≫ fW) (iW ≫ mapk) hstageW).app YW₀
  let eGlue : (pullback iU).obj V ≅ (pullback iW).obj YW :=
    eGlueFlat ≪≫ ((pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).app YW₀).symm
  obtain ⟨V', eU, eW, hglueSup⟩ := exists_sup_of_iso_inf V YW eGlue
  let jU := X.homOfLE (U := U) (V := U ⊔ W.opens) le_sup_left
  let jW := X.homOfLE (U := W.opens) (V := U ⊔ W.opens) le_sup_right
  let sW := W.opens.fromSpecStalkOfMem s W.mem
  let sUW := (U ⊔ W.opens).fromSpecStalkOfMem s (show s ∈ U ⊔ W.opens from Or.inr W.mem)
  have hsW_jW : sW ≫ jW = sUW := by
    rw [← cancel_mono (U ⊔ W.opens).ι]; simp [sW, jW, sUW]
  have hsW_mapk : sW ≫ mapk = sW₀ := by rw [← cancel_mono W₀.opens.ι]; simp [sW, mapk, sW₀]
  let es : (pullback sUW).obj V' ≅ Ys :=
    ((pullbackCompIsoOfEq sW jW sUW hsW_jW).app V').symm ≪≫
      (pullback sW).mapIso eW ≪≫
      (pullbackCompIsoOfEq sW mapk sW₀ hsW_mapk).app YW₀ ≪≫
      eW₀
  refine ⟨W, V', eU, es, ?_⟩
  -- Reduce compatibility over `(X.fromSpecStalk s ⁻¹ᵁ U).toScheme` to projected morphisms into
  -- `YW₀.obj.left` after transporting along `eW₀.symm`.
  let tailIso : (pullback ιOs).obj Ys ≅ (pullback (ιOs ≫ sW₀)).obj YW₀ :=
    (pullback ιOs).mapIso eW₀.symm ≪≫ (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).app YW₀
  rw [← cancel_mono tailIso.hom]
  apply hom_ext_proj
  -- Step 1: `ekFlat` lifts `eLimFlat` on projected morphisms.
  have hekProj :
      pm V (cO.π.app j₀ ≫ fV) (DO.map fk ≫ fV) (cO.π.app k)
          (by rw [← Category.assoc, cO.w fk]) ≫
        proj ekFlat.hom =
      proj eLimFlat.hom := by
    have heLimF : eLimFlat.hom =
        (pullbackCompIsoOfEq (cO.π.app j₀) fV _ rfl).inv.app V ≫ eLim.hom ≫
          (pullbackCompIsoOfEq (cO.π.app j₀) fW _ rfl).hom.app YW₀ := by simp [eLim]
    have hekF : ekFlat.hom =
        (pullbackCompIsoOfEq (DO.map fk) fV _ rfl).inv.app V ≫ ek.hom ≫
          (pullbackCompIsoOfEq (DO.map fk) fW _ rfl).hom.app YW₀ := by simp [ekFlat]
    have hekP : proj eLim.hom =
        pm ((pullback fV).obj V) (cO.π.app j₀) (DO.map fk) (cO.π.app k) (cO.w fk) ≫
          proj ek.hom :=
      (congrArg proj hek).symm.trans (proj_conj_compIso (cO.w fk) (cO.w fk) ek.hom)
    rw [heLimF, hekF, proj_flat, proj_flat, pm_cInv_assoc (cO.w fk), hekP, Category.assoc]
  -- Step 2: Pulling `eGlueFlat` back along `m : (X.fromSpecStalk s ⁻¹ᵁ U).toScheme ⟶ U ⊓ W.opens`
  -- recovers `e₀'`.
  let m : (X.fromSpecStalk s ⁻¹ᵁ U).toScheme ⟶ (U ⊓ W.opens).toScheme :=
    iPtInv ≫ cO.π.app k ≫ eRange.inv
  have hmU : m ≫ iU = gU := X.stalkOpensConePtIso_inv_π_stageIso_inv U s k
  have hmW : m ≫ iW = ιOs ≫ sW := X.stalkOpensConePtIso_inv_π_stageIso_inv_nhds U s k
  have hmGlue : pm V gU iU m hmU ≫ proj eGlueFlat.hom = proj e₀'.hom := by
    have hGF : proj eGlueFlat.hom =
        pm V iU (DO.map fk ≫ fV) eRange.hom hstageV ≫ proj ekFlat.hom :=
      proj_conj_compIso hstageV hstageW ekFlat.hom
    have hLF : proj eLimFlat.hom =
        pm V (cO.π.app j₀ ≫ fV) gU iPt htopV ≫ proj e₀'.hom :=
      proj_conj_compIso htopV htopW e₀'.hom
    have hm_eRange : m ≫ eRange.hom = iPtInv ≫ cO.π.app k := by simp [m]
    rw [hGF, pm_comp_assoc V hmU hstageV,
      pm_congr V gU (DO.map fk ≫ fV) hm_eRange _
        (by rw [Category.assoc, ← Category.assoc (cO.π.app k), cO.w fk, ← htopV,
          Iso.inv_hom_id_assoc]),
      ← pm_comp_assoc V (fB := cO.π.app j₀ ≫ fV) (by rw [← htopV, Iso.inv_hom_id_assoc])
        (by rw [← Category.assoc, cO.w fk]),
      hekProj, hLF, pm_comp_assoc V,
      pm_congr V gU gU (X.stalkOpensConePtIso U s W₀).inv_hom_id _ (Category.id_comp gU),
      pm_id, Category.id_comp]
  -- Step 3: Base-change the overlap compatibility `hglueSup` along `m`.
  let ij := X.homOfLE (U := U ⊓ W.opens) (V := U ⊔ W.opens) (inf_le_left.trans le_sup_left)
  have hgU_jU : gU ≫ jU = ιOs ≫ sUW := by
    rw [← cancel_mono (U ⊔ W.opens).ι]; simp [gU, jU, ιOs, sUW]
  have hm_ij : m ≫ ij = ιOs ≫ sUW := by
    rw [show ij = iU ≫ jU from (X.homOfLE_homOfLE inf_le_left le_sup_left).symm,
      ← Category.assoc, hmU, hgU_jU]
  have hSupFlat :=
    congrArg (fun u ↦ proj (u ≫ (pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).hom.app YW₀))
      hglueSup
  have heGlue :
      eGlue.hom ≫ (pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).hom.app YW₀ = eGlueFlat.hom := by
    simp [eGlue]
  simp only [Category.assoc] at hSupFlat
  rw [heGlue] at hSupFlat
  have hBase := congrArg (pm V' (ιOs ≫ sUW) ij m hm_ij ≫ ·) hSupFlat
  -- Identify LHS and RHS of `hBase` with the two projected sides of our goal.
  have hLHS :
      pm V' (ιOs ≫ sUW) ij m hm_ij ≫
          proj ((pullbackCompIsoOfEq iU jU ij (X.homOfLE_homOfLE _ _)).inv.app V' ≫
            (pullback iU).map eU.hom ≫ eGlueFlat.hom) =
        proj (((pullbackCompIsoOfEq gU jU (ιOs ≫ sUW) hgU_jU).inv.app V' ≫
          (pullback gU).map eU.hom ≫ e₀.hom) ≫ tailIso.hom) := by
    have he₀' : e₀.hom ≫ tailIso.hom = e₀'.hom := by simp [e₀', tailIso]
    rw [Category.assoc, Category.assoc, he₀',
      ← Category.assoc ((pullbackCompIsoOfEq iU jU ij _).inv.app V'), proj_comp,
      ← Category.assoc ((pullbackCompIsoOfEq gU jU _ _).inv.app V'), proj_comp,
      ← Category.assoc,
      pm_comp_compIso_inv_map (X.homOfLE_homOfLE _ _) hm_ij hmU hgU_jU V' eU.hom,
      Category.assoc, hmGlue]
  have hRHS :
      pm V' (ιOs ≫ sUW) ij m hm_ij ≫
          proj ((pullbackCompIsoOfEq iW jW ij (X.homOfLE_homOfLE _ _)).inv.app V' ≫
            (pullback iW).map eW.hom ≫
            (pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).hom.app YW₀) =
        proj (((pullbackCompIsoOfEq ιOs sUW _ rfl).inv.app V' ≫
          (pullback ιOs).map es.hom) ≫ tailIso.hom) := by
    have hprojW : ∀ {B : Scheme.{u}} {a : B ⟶ W.opens.toScheme}
        {aj : B ⟶ (U ⊔ W.opens).toScheme} {am : B ⟶ W₀.opens.toScheme}
        (haj : a ≫ jW = aj) (ham : a ≫ mapk = am),
        proj ((pullbackCompIsoOfEq a jW aj haj).inv.app V' ≫
            (pullback a).map eW.hom ≫
            (pullbackCompIsoOfEq a mapk am ham).hom.app YW₀) =
          pm V' aj jW a haj ≫ eW.hom.hom.left ≫ pfst YW₀ mapk := by
      intro B a aj am haj ham
      rw [← Category.assoc ((pullbackCompIsoOfEq a jW aj haj).inv.app V'),
        proj, comp_compIso_hom_left_pfst ham YW₀, compIso_inv_map_left_pfst_assoc haj V' eW.hom]
    have hesTail :
        (pullback ιOs).map es.hom ≫ tailIso.hom =
          (pullback ιOs).map
              ((pullbackCompIsoOfEq sW jW sUW hsW_jW).inv.app V' ≫
                (pullback sW).map eW.hom ≫
                (pullbackCompIsoOfEq sW mapk sW₀ hsW_mapk).hom.app YW₀) ≫
            (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).hom.app YW₀ := by
      simp only [es, tailIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
        Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc]
    rw [Category.assoc, hesTail, proj_conj_compIso rfl rfl,
      hprojW (X.homOfLE_homOfLE _ _) rfl, hprojW hsW_jW hsW_mapk,
      pm_comp_assoc V', pm_comp_assoc V', pm_congr V' (ιOs ≫ sUW) jW hmW]
  exact hLHS.symm.trans (hBase.trans hRHS)

end SpreadAndGlue

end TauCeti.FiniteEtaleScheme
