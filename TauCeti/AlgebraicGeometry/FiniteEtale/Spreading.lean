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
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Section
import TauCeti.RingTheory.Etale.DirectLimit

/-!
# Spreading out finite étale schemes from stalks and cofiltered limits

For a scheme `X`, an open `U : X.Opens`, and `s : X`, this file proves stalk object descent
(`exists_pullback_fromSpecStalkOfMem_iso`), cofiltered affine-transition limit descent
(`exists_hom_pullback_of_isLimit`, `exists_pullback_map_eq_of_isLimit`,
`exists_iso_pullback_of_isLimit`), binary open gluing (`exists_sup_of_iso_inf`), and spreading of
finite étale extensions from `Spec (X.presheaf.stalk s)` (`exists_spread_fromSpecStalk`;
[Stacks Project](https://stacks.math.columbia.edu/tag/0BQ5), Tags 01LH, 01Z4, 01ZM, 0BQ5, 0EY3).
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

section LimitSpreading

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Limits.Cone D)

private theorem conj_compIso_hom {A B S : Scheme.{u}} {m : A ⟶ B} {g : B ⟶ S} {mg : A ⟶ S}
    (h : m ≫ g = mg) {Y₁ Y₂ : FiniteEtaleScheme S} (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    ((pullbackCompIsoOfEq m g mg h).inv.app Y₁ ≫ (pullback m).map β ≫
      (pullbackCompIsoOfEq m g mg h).hom.app Y₂).hom =
      (Over.pullbackCompIsoOfEq m g mg h).inv.app Y₁.obj ≫ (Over.pullback m).map β.hom ≫
      (Over.pullbackCompIsoOfEq m g mg h).hom.app Y₂.obj := by
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackCompIsoOfEq_inv_app_hom,
    pullback_map_hom, pullbackCompIsoOfEq_hom_app_hom]
  -- `((pullback g).obj Y).obj` and `(Over.pullback g).obj Y.obj` are definitionally equal.
  rfl

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
  let ⟨j, fj, β, hβ⟩ := Scheme.exists_hom_pullback_of_isLimit D c hc Y₁.obj Y₂.obj α.hom
  ⟨j, fj, (finiteEtaleSchemeProperty (D.obj j)).homMk β,
    ObjectProperty.hom_ext _ ((conj_compIso_hom (c.w fj) _).trans hβ)⟩

/-- Along a cofiltered limit of quasi-compact schemes with affine transition morphisms, two
morphisms between finite étale schemes at stage `i₀` that become equal on the limit already become
equal at some stage `k` mapping to `i₀`. -/
@[stacks 01ZM "for finite étale schemes"]
theorem exists_pullback_map_eq_of_isLimit (hc : Limits.IsLimit c) {i₀ : I}
    {Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀)} (β₁ β₂ : Y₁ ⟶ Y₂)
    (h : (pullback (c.π.app i₀)).map β₁ = (pullback (c.π.app i₀)).map β₂) :
    ∃ (k : I) (fk : k ⟶ i₀), (pullback (D.map fk)).map β₁ = (pullback (D.map fk)).map β₂ :=
  let ⟨k, fk, hfk⟩ :=
    Scheme.exists_pullback_map_eq_of_isLimit D c hc β₁.hom β₂.hom congr(($h).hom)
  ⟨k, fk, ObjectProperty.hom_ext _ hfk⟩

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
        (pullbackCompIsoOfEq (c.π.app k) (D.map fk) (c.π.app i₀) (c.w fk)).hom.app Y₂ = e.hom :=
  let ⟨k, fk, ek, hek⟩ := Scheme.exists_iso_pullback_of_isLimit D c hc Y₁.obj Y₂.obj
    { hom := e.hom.hom, inv := e.inv.hom, hom_inv_id := congr(($e.hom_inv_id).hom)
      inv_hom_id := congr(($e.inv_hom_id).hom) }
  ⟨k, fk, (finiteEtaleSchemeProperty (D.obj k)).isoMk ek,
    ObjectProperty.hom_ext _ ((conj_compIso_hom (c.w fk) _).trans hek)⟩

end LimitSpreading

section PullbackProj
variable {A₀ A B C S S₁ S₂ : Scheme.{u}}
private def pfst (Y : FiniteEtaleScheme S) (f : B ⟶ S) :
    ((pullback f).obj Y).obj.left ⟶ Y.obj.left := Limits.pullback.fst Y.obj.hom f
private def psnd (Y : FiniteEtaleScheme S) (f : B ⟶ S) :
    ((pullback f).obj Y).obj.left ⟶ B := Limits.pullback.snd Y.obj.hom f
private theorem pullback_hom_ext {Y : FiniteEtaleScheme S} {f : B ⟶ S}
    {u₁ u₂ : A ⟶ ((pullback f).obj Y).obj.left}
    (h₁ : u₁ ≫ pfst Y f = u₂ ≫ pfst Y f) (h₂ : u₁ ≫ psnd Y f = u₂ ≫ psnd Y f) : u₁ = u₂ :=
  Limits.pullback.hom_ext h₁ h₂
private def pm (Y : FiniteEtaleScheme S) (fA : A ⟶ S) (fB : B ⟶ S) (m : A ⟶ B) (hm : m ≫ fB = fA) :
    ((pullback fA).obj Y).obj.left ⟶ ((pullback fB).obj Y).obj.left :=
  Limits.pullback.mapSnd Y.obj.hom fB fA m hm
@[reassoc (attr := simp)] private theorem pm_pfst {Y : FiniteEtaleScheme S} {fA : A ⟶ S}
    {fB : B ⟶ S} {m : A ⟶ B} {hm : m ≫ fB = fA} : pm Y fA fB m hm ≫ pfst Y fB = pfst Y fA :=
  Limits.pullback.mapSnd_fst ..
@[reassoc (attr := simp)] private theorem pm_psnd {Y : FiniteEtaleScheme S} {fA : A ⟶ S}
    {fB : B ⟶ S} {m : A ⟶ B} {hm : m ≫ fB = fA} : pm Y fA fB m hm ≫ psnd Y fB = psnd Y fA ≫ m :=
  Limits.pullback.mapSnd_snd ..
private theorem pm_id (Y : FiniteEtaleScheme S) (f : A ⟶ S) :
    pm Y f f (𝟙 A) (Category.id_comp f) = 𝟙 _ := Limits.pullback.mapSnd_id ..
@[reassoc] private theorem pm_comp (Y : FiniteEtaleScheme S) {fA : A ⟶ S} {fB : B ⟶ S} {fC : C ⟶ S}
    {m₁ : A ⟶ B} {m₂ : B ⟶ C} (hm₁ : m₁ ≫ fB = fA) (hm₂ : m₂ ≫ fC = fB) :
    pm Y fA fB m₁ hm₁ ≫ pm Y fB fC m₂ hm₂ =
      pm Y fA fC (m₁ ≫ m₂) (by rw [Category.assoc, hm₂, hm₁]) :=
  Limits.pullback.mapSnd_comp Y.obj.hom fC fB fA m₂ hm₂ m₁ hm₁
private theorem pm_congr (Y : FiniteEtaleScheme S) (fA : A ⟶ S) (fB : B ⟶ S) {m₁ m₂ : A ⟶ B}
    (h : m₁ = m₂) (hm₁ hm₂) : pm Y fA fB m₁ hm₁ = pm Y fA fB m₂ hm₂ := by subst h; rfl
private def proj {g : B ⟶ S} {Z : FiniteEtaleScheme B} {Y : FiniteEtaleScheme S}
    (φ : Z ⟶ (pullback g).obj Y) : Z.obj.left ⟶ Y.obj.left := φ.hom.left ≫ pfst Y g
private theorem proj_comp {g : B ⟶ S} {X Z : FiniteEtaleScheme B} {Y : FiniteEtaleScheme S}
    (α : X ⟶ Z) (β : Z ⟶ (pullback g).obj Y) : proj (α ≫ β) = α.hom.left ≫ proj β := by
  rw [proj, ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc, proj]
private theorem hom_ext_proj {g : B ⟶ S} {Z : FiniteEtaleScheme B} {Y : FiniteEtaleScheme S}
    {φ₁ φ₂ : Z ⟶ (pullback g).obj Y} (h : proj φ₁ = proj φ₂) : φ₁ = φ₂ :=
  ObjectProperty.hom_ext _ <| Over.OverMorphism.ext <|
    pullback_hom_ext h ((Over.w φ₁.hom).trans (Over.w φ₂.hom).symm)
@[reassoc] private theorem pullback_map_pfst (f : B ⟶ S) {Y₁ Y₂ : FiniteEtaleScheme S}
    (α : Y₁ ⟶ Y₂) : ((pullback f).map α).hom.left ≫ pfst Y₂ f = pfst Y₁ f ≫ α.hom.left := by
  simp only [pullback_map_hom, Over.pullback_map_left, pfst]; exact Limits.pullback.lift_fst _ _ _
@[reassoc] private theorem pullback_map_psnd (f : B ⟶ S) {Y₁ Y₂ : FiniteEtaleScheme S}
    (α : Y₁ ⟶ Y₂) : ((pullback f).map α).hom.left ≫ psnd Y₂ f = psnd Y₁ f := by
  simp only [pullback_map_hom, Over.pullback_map_left, psnd]; exact Limits.pullback.lift_snd _ _ _
section CompIso
variable {m : A ⟶ B} {b : B ⟶ C} {ab : A ⟶ C}
@[reassoc] private theorem comp_compIso_hom_left_pfst (hab : m ≫ b = ab) {Z : FiniteEtaleScheme A}
    (Y : FiniteEtaleScheme C) (ψ : Z ⟶ (pullback m).obj ((pullback b).obj Y)) :
    (ψ ≫ (pullbackCompIsoOfEq m b ab hab).hom.app Y).hom.left ≫ pfst Y ab =
      ψ.hom.left ≫ pfst ((pullback b).obj Y) m ≫ pfst Y b := by
  rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc]
  exact congrArg (ψ.hom.left ≫ ·) (pullbackCompIsoOfEq_hom_app_hom_left_fst hab Y)
@[reassoc] private theorem compIso_inv_left_pfst (hab : m ≫ b = ab) (Y : FiniteEtaleScheme C) :
    ((pullbackCompIsoOfEq m b ab hab).inv.app Y).hom.left ≫ pfst ((pullback b).obj Y) m =
      pm Y ab b m hab :=
  (pullbackCompIsoOfEq_inv_app_hom_left_fst hab Y).trans <| by apply Limits.pullback.hom_ext <;>
    simp [pm]
@[reassoc] private theorem compIso_inv_left_psnd (hab : m ≫ b = ab) (Y : FiniteEtaleScheme C) :
    ((pullbackCompIsoOfEq m b ab hab).inv.app Y).hom.left ≫ psnd ((pullback b).obj Y) m =
      psnd Y ab := pullbackCompIsoOfEq_inv_app_hom_left_snd hab Y
@[reassoc] private theorem compIso_inv_map_left_pfst (hab : m ≫ b = ab) (Y : FiniteEtaleScheme C)
    {Z : FiniteEtaleScheme B} (φ : (pullback b).obj Y ⟶ Z) :
    ((pullbackCompIsoOfEq m b ab hab).inv.app Y ≫ (pullback m).map φ).hom.left ≫ pfst Z m =
      pm Y ab b m hab ≫ φ.hom.left := by
  rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc, pullback_map_pfst,
    compIso_inv_left_pfst_assoc]
@[reassoc] private theorem compIso_inv_map_left_psnd (hab : m ≫ b = ab) (Y : FiniteEtaleScheme C)
    {Z : FiniteEtaleScheme B} (φ : (pullback b).obj Y ⟶ Z) :
    ((pullbackCompIsoOfEq m b ab hab).inv.app Y ≫ (pullback m).map φ).hom.left ≫ psnd Z m =
      psnd Y ab := by
  rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc, pullback_map_psnd,
    compIso_inv_left_psnd]
end CompIso
private theorem proj_conj_compIso {m : A ⟶ B} {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {h₁ : A ⟶ S₁}
    {h₂ : A ⟶ S₂} (hm₁ : m ≫ g₁ = h₁) (hm₂ : m ≫ g₂ = h₂) {Y₁ : FiniteEtaleScheme S₁}
    {Y₂ : FiniteEtaleScheme S₂} (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    proj ((pullbackCompIsoOfEq m g₁ h₁ hm₁).inv.app Y₁ ≫ (pullback m).map φ ≫
        (pullbackCompIsoOfEq m g₂ h₂ hm₂).hom.app Y₂) = pm Y₁ h₁ g₁ m hm₁ ≫ proj φ := by
  rw [← Category.assoc ((pullbackCompIsoOfEq m g₁ h₁ hm₁).inv.app Y₁), proj,
    comp_compIso_hom_left_pfst hm₂ Y₂, compIso_inv_map_left_pfst_assoc, proj]
private theorem proj_conj_compIso_iso {m : A ⟶ B} {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {h₁ : A ⟶ S₁}
    {h₂ : A ⟶ S₂} (hm₁ : m ≫ g₁ = h₁) (hm₂ : m ≫ g₂ = h₂) {Y₁ : FiniteEtaleScheme S₁}
    {Y₂ : FiniteEtaleScheme S₂} (φ : (pullback g₁).obj Y₁ ≅ (pullback g₂).obj Y₂) :
    proj ((((pullbackCompIsoOfEq m g₁ h₁ hm₁).app Y₁).symm ≪≫ (pullback m).mapIso φ ≪≫
        (pullbackCompIsoOfEq m g₂ h₂ hm₂).app Y₂).hom) = pm Y₁ h₁ g₁ m hm₁ ≫ proj φ.hom := by
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom] using
    proj_conj_compIso hm₁ hm₂ φ.hom
@[reassoc] private theorem pm_comp_compIso_inv_rfl {k : A₀ ⟶ A} {a₂ : A ⟶ B} {a₁ : A₀ ⟶ B}
    (hk : k ≫ a₂ = a₁) (f : B ⟶ S) (Y : FiniteEtaleScheme S) :
    pm Y (a₁ ≫ f) (a₂ ≫ f) k (by rw [← Category.assoc, hk]) ≫
        ((pullbackCompIsoOfEq a₂ f (a₂ ≫ f) rfl).inv.app Y).hom.left =
      ((pullbackCompIsoOfEq a₁ f (a₁ ≫ f) rfl).inv.app Y).hom.left ≫
        pm ((pullback f).obj Y) a₁ a₂ k hk :=
  pullback_hom_ext (by simp only [Category.assoc, compIso_inv_left_pfst, pm_pfst]; rw [pm_comp,
    pm_congr Y _ _ hk]) (by simp only [Category.assoc, compIso_inv_left_psnd, pm_psnd,
      compIso_inv_left_psnd_assoc])
private theorem proj_flat (a : A ⟶ B) (f₁ : B ⟶ S₁) (f₂ : B ⟶ S₂) {Y₁ : FiniteEtaleScheme S₁}
    {Y₂ : FiniteEtaleScheme S₂}
    (u : (pullback a).obj ((pullback f₁).obj Y₁) ⟶ (pullback a).obj ((pullback f₂).obj Y₂)) :
    proj ((pullbackCompIsoOfEq a f₁ (a ≫ f₁) rfl).inv.app Y₁ ≫ u ≫
        (pullbackCompIsoOfEq a f₂ (a ≫ f₂) rfl).hom.app Y₂) =
      ((pullbackCompIsoOfEq a f₁ (a ≫ f₁) rfl).inv.app Y₁).hom.left ≫ proj u ≫ pfst Y₂ f₂ := by
  rw [← Category.assoc ((pullbackCompIsoOfEq a f₁ (a ≫ f₁) rfl).inv.app Y₁), proj,
    comp_compIso_hom_left_pfst rfl Y₂, ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
    proj, Category.assoc, Category.assoc]
private theorem pm_comp_compIso_inv_map {n : A₀ ⟶ A} {m : A ⟶ B} {b : B ⟶ C} {ab : A ⟶ C}
    {a₀b : A₀ ⟶ C} {nm : A₀ ⟶ B} (hab : m ≫ b = ab) (hn_ab : n ≫ ab = a₀b) (hnm : n ≫ m = nm)
    (hnm_b : nm ≫ b = a₀b) (Y : FiniteEtaleScheme C) {Z : FiniteEtaleScheme B}
    (φ : (pullback b).obj Y ⟶ Z) :
    pm Y a₀b ab n hn_ab ≫
        ((pullbackCompIsoOfEq m b ab hab).inv.app Y ≫ (pullback m).map φ).hom.left =
      ((pullbackCompIsoOfEq nm b a₀b hnm_b).inv.app Y ≫ (pullback nm).map φ).hom.left ≫
        pm Z nm m n hnm :=
  pullback_hom_ext (by rw [Category.assoc, compIso_inv_map_left_pfst, Category.assoc, pm_pfst,
    compIso_inv_map_left_pfst, pm_comp_assoc Y, pm_congr Y _ _ hnm]) (by rw [Category.assoc,
      compIso_inv_map_left_psnd, pm_psnd, Category.assoc, pm_psnd, compIso_inv_map_left_psnd_assoc])
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
      (pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left) (X.homOfLE le_sup_left)
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
          (X.homOfLE_homOfLE _ _)).inv.app V' ≫
        (pullback (X.homOfLE inf_le_left)).map eU.hom ≫ eGlue.hom =
      (pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right) (X.homOfLE le_sup_right)
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
          (X.homOfLE_homOfLE _ _)).inv.app V' ≫
        (pullback (X.homOfLE inf_le_right)).map eW.hom := by
  let Dglue : BinaryOpenGluingData U W :=
    { left := V.obj.left, leftHom := V.obj.hom, right := YW.obj.left, rightHom := YW.obj.hom
      iso := { hom := eGlue.hom.hom.left, inv := eGlue.inv.hom.left
               hom_inv_id := congr(($eGlue.hom_inv_id).hom.left)
               inv_hom_id := congr(($eGlue.inv_hom_id).hom.left) }
      iso_hom_snd := Over.w eGlue.hom.hom }
  have := @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty.{u}
  have := HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFiniteType.{u}
    (Q := @RingHom.FiniteType)
  have := HasRingHomProperty.instIsZariskiLocalAtTarget @Etale.{u} (Q := @RingHom.Etale)
  let V' : FiniteEtaleScheme (U ⊔ W).toScheme := ⟨Over.mk Dglue.toBase,
    (finiteEtaleSchemeProperty_iff _).mpr
      ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType Dglue.toBase).mpr
        ⟨Dglue.morphismProperty_toBase (@IsIntegralHom) inferInstance inferInstance,
         Dglue.morphismProperty_toBase (@LocallyOfFiniteType) inferInstance inferInstance⟩,
       Dglue.morphismProperty_toBase (@Etale) inferInstance inferInstance⟩⟩
  let eU : (pullback (X.homOfLE le_sup_left)).obj V' ≅ V := (finiteEtaleSchemeProperty _).isoMk
    (Over.isoMk Dglue.pullbackLeftIso Dglue.pullbackLeftIso_hom_leftHom)
  let eW : (pullback (X.homOfLE le_sup_right)).obj V' ≅ YW := (finiteEtaleSchemeProperty _).isoMk
    (Over.isoMk Dglue.pullbackRightIso Dglue.pullbackRightIso_hom_rightHom)
  refine ⟨V', eU, eW, hom_ext_proj ?_⟩
  rw [← cancel_mono Dglue.ιRight]
  have hglue : proj eGlue.hom ≫ Dglue.ιRight =
      pfst V (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ≫ Dglue.ιLeft :=
    (Category.assoc eGlue.hom.hom.left _ _).trans Dglue.fst_ιLeft.symm
  -- `eU.hom.hom.left` is `Dglue.pullbackLeftIso.hom` and `pfst V'` is
  -- `Limits.pullback.fst Dglue.toBase _`; similarly for `eW` on the right chart.
  have heU : eU.hom.hom.left ≫ Dglue.ιLeft = pfst V' (X.homOfLE le_sup_left) :=
    Dglue.pullbackLeftIso_hom_ιLeft
  have heW : eW.hom.hom.left ≫ Dglue.ιRight = pfst V' (X.homOfLE le_sup_right) :=
    Dglue.pullbackRightIso_hom_ιRight
  rw [← Category.assoc ((pullbackCompIsoOfEq (X.homOfLE inf_le_left) _ _ _).inv.app V'),
    proj_comp, Category.assoc, hglue, compIso_inv_map_left_pfst_assoc, heU, pm_pfst, proj,
    Category.assoc, compIso_inv_map_left_pfst_assoc, heW, pm_pfst]

/-- Limit-to-overlap compatibility: if `ek` at a finite stage `B` pulls back along `a : A ⟶ B`
to the cone-vertex transport of `e₀'`, then transporting `ek` along `eRange : Stage ≅ B` and
pulling back along `m = iPt.inv ≫ a ≫ eRange.inv` recovers `proj e₀'`. -/
private theorem proj_overlap_of_limit_desc {Pt Stage A B C S₁ S₂ : Scheme.{u}}
    {a : A ⟶ B} {b : B ⟶ C} {ab : A ⟶ C} (hab : a ≫ b = ab) {f₁ : C ⟶ S₁} {f₂ : C ⟶ S₂}
    (iPt : A ≅ Pt) (eRange : Stage ≅ B) {g₁ : Pt ⟶ S₁} {g₂ : Pt ⟶ S₂} {i₁ : Stage ⟶ S₁}
    {i₂ : Stage ⟶ S₂} (htop₁ : iPt.hom ≫ g₁ = ab ≫ f₁) (htop₂ : iPt.hom ≫ g₂ = ab ≫ f₂)
    (hstage₁ : eRange.hom ≫ (b ≫ f₁) = i₁) (hstage₂ : eRange.hom ≫ (b ≫ f₂) = i₂)
    (hm₁ : (iPt.inv ≫ a ≫ eRange.inv) ≫ i₁ = g₁) {Y₁ : FiniteEtaleScheme S₁}
    {Y₂ : FiniteEtaleScheme S₂} (e₀' : (pullback g₁).obj Y₁ ≅ (pullback g₂).obj Y₂)
    (ek : (pullback b).obj ((pullback f₁).obj Y₁) ≅ (pullback b).obj ((pullback f₂).obj Y₂))
    (hek : (pullbackCompIsoOfEq a b ab hab).inv.app ((pullback f₁).obj Y₁) ≫
        (pullback a).map ek.hom ≫ (pullbackCompIsoOfEq a b ab hab).hom.app ((pullback f₂).obj Y₂) =
      ((pullbackCompIsoOfEq ab f₁ (ab ≫ f₁) rfl).app Y₁ ≪≫
        (((pullbackCompIsoOfEq iPt.hom g₁ _ htop₁).app Y₁).symm ≪≫ (pullback iPt.hom).mapIso e₀' ≪≫
          (pullbackCompIsoOfEq iPt.hom g₂ _ htop₂).app Y₂) ≪≫
        ((pullbackCompIsoOfEq ab f₂ (ab ≫ f₂) rfl).app Y₂).symm).hom) :
    pm Y₁ g₁ i₁ (iPt.inv ≫ a ≫ eRange.inv) hm₁ ≫
        proj ((((pullbackCompIsoOfEq eRange.hom (b ≫ f₁) i₁ hstage₁).app Y₁).symm ≪≫
          (pullback eRange.hom).mapIso (((pullbackCompIsoOfEq b f₁ _ rfl).app Y₁).symm ≪≫ ek ≪≫
            (pullbackCompIsoOfEq b f₂ _ rfl).app Y₂) ≪≫
          (pullbackCompIsoOfEq eRange.hom (b ≫ f₂) i₂ hstage₂).app Y₂).hom) = proj e₀'.hom := by
  let eLimFlat := ((pullbackCompIsoOfEq iPt.hom g₁ _ htop₁).app Y₁).symm ≪≫
    (pullback iPt.hom).mapIso e₀' ≪≫ (pullbackCompIsoOfEq iPt.hom g₂ _ htop₂).app Y₂
  let eLim := (pullbackCompIsoOfEq ab f₁ _ rfl).app Y₁ ≪≫ eLimFlat ≪≫
    ((pullbackCompIsoOfEq ab f₂ _ rfl).app Y₂).symm
  let ekFlat := ((pullbackCompIsoOfEq b f₁ _ rfl).app Y₁).symm ≪≫ ek ≪≫
    (pullbackCompIsoOfEq b f₂ _ rfl).app Y₂
  -- Flatten `hek` from double pullbacks to single pullbacks.
  have hekProj : pm Y₁ (ab ≫ f₁) (b ≫ f₁) a (by rw [← Category.assoc, hab]) ≫ proj ekFlat.hom =
      proj eLimFlat.hom := by
    rw [show eLimFlat.hom = (pullbackCompIsoOfEq ab f₁ _ rfl).inv.app Y₁ ≫ eLim.hom ≫
          (pullbackCompIsoOfEq ab f₂ _ rfl).hom.app Y₂ by simp [eLim],
      show ekFlat.hom = (pullbackCompIsoOfEq b f₁ _ rfl).inv.app Y₁ ≫ ek.hom ≫
          (pullbackCompIsoOfEq b f₂ _ rfl).hom.app Y₂ by simp [ekFlat],
      proj_flat, proj_flat, pm_comp_compIso_inv_rfl_assoc hab,
      (congrArg proj hek).symm.trans (proj_conj_compIso hab hab ek.hom), Category.assoc]
  -- Cancel `eRange` and `iPt` along `m = iPt.inv ≫ a ≫ eRange.inv`.
  rw [proj_conj_compIso_iso hstage₁ hstage₂ ekFlat, pm_comp_assoc Y₁ hm₁ hstage₁,
    pm_congr Y₁ g₁ (b ≫ f₁) (by simp : (iPt.inv ≫ a ≫ eRange.inv) ≫ eRange.hom = iPt.inv ≫ a) _
      (by rw [Category.assoc, ← Category.assoc a, hab, ← htop₁, Iso.inv_hom_id_assoc]),
    ← pm_comp_assoc Y₁ (fB := ab ≫ f₁) (by rw [← htop₁, Iso.inv_hom_id_assoc])
      (by rw [← Category.assoc, hab]),
    hekProj, proj_conj_compIso_iso htop₁ htop₂ e₀', pm_comp_assoc Y₁,
    pm_congr Y₁ g₁ g₁ iPt.inv_hom_id _ (Category.id_comp g₁), pm_id, Category.id_comp]

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
    (hmGlue : pm V gU iU m hmU ≫ proj eGlueFlat.hom = proj (e₀ ≪≫ (pullback ιOs).mapIso eW₀.symm ≪≫
      (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).app YW₀).hom) :
    (pullbackCompIsoOfEq gU jU (ιOs ≫ sUW) hgUjU).inv.app V' ≫ (pullback gU).map eU.hom ≫ e₀.hom =
      (pullbackCompIsoOfEq ιOs sUW (ιOs ≫ sUW) rfl).inv.app V' ≫ (pullback ιOs).map
        (((pullbackCompIsoOfEq sW jW sUW hsWjW).app V').symm ≪≫ (pullback sW).mapIso eW ≪≫
          (pullbackCompIsoOfEq sW mapk sW₀ hsWmapk).app YW₀ ≪≫ eW₀).hom := by
  let tailIso := (pullback ιOs).mapIso eW₀.symm ≪≫
    (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).app YW₀
  rw [← cancel_mono tailIso.hom]; apply hom_ext_proj
  have hm_ij : m ≫ ij = ιOs ≫ sUW := by rw [← hiUjU, ← Category.assoc, hmU, hgUjU]
  -- Flatten `hglueSup` on `Inf` and pull both sides back along `m : O ⟶ Inf`.
  have hSupFlat := congrArg
    (fun u ↦ proj (u ≫ (pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).hom.app YW₀)) hglueSup
  simp only [Category.assoc, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.inv_hom_id_app, Category.comp_id] at hSupFlat
  have hesTail : (pullback ιOs).map (((pullbackCompIsoOfEq sW jW sUW hsWjW).app V').symm ≪≫
        (pullback sW).mapIso eW ≪≫ (pullbackCompIsoOfEq sW mapk sW₀ hsWmapk).app YW₀ ≪≫ eW₀).hom ≫
        tailIso.hom =
      (pullback ιOs).map ((pullbackCompIsoOfEq sW jW sUW hsWjW).inv.app V' ≫
        (pullback sW).map eW.hom ≫ (pullbackCompIsoOfEq sW mapk sW₀ hsWmapk).hom.app YW₀) ≫
        (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).hom.app YW₀ := by
    simp only [tailIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc]
  rw [Category.assoc, Category.assoc, ← Iso.trans_hom e₀ tailIso,
    ← Category.assoc ((pullbackCompIsoOfEq gU jU _ hgUjU).inv.app V'), proj_comp, ← hmGlue,
    ← Category.assoc, ← pm_comp_compIso_inv_map hiUjU hm_ij hmU hgUjU V' eU.hom, Category.assoc,
    ← proj_comp, Category.assoc, hSupFlat, Category.assoc, hesTail, proj_conj_compIso rfl rfl,
    proj_conj_compIso hiWjW rfl eW.hom, proj_conj_compIso hsWjW hsWmapk eW.hom,
    pm_comp_assoc V', pm_comp_assoc V', pm_congr V' (ιOs ≫ sUW) jW hmW]

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
  let es := ((pullbackCompIsoOfEq sW (X.homOfLE le_sup_right) sUW hsW_jW).app V').symm ≪≫
    (pullback sW).mapIso eW ≪≫ (pullbackCompIsoOfEq sW mapk sW₀ hsW_mapk).app YW₀ ≪≫ eW₀
  refine ⟨W, V', eU, es, spread_gluing_compat (X.homOfLE_homOfLE _ _) (X.homOfLE_homOfLE _ _)
    hgU_jU hsW_jW hsW_mapk (X.stalkOpensConePtIso_inv_π_stageIso_inv U s k)
    (X.stalkOpensConePtIso_inv_π_stageIso_inv_nhds U s k) eW₀ e₀ eGlueFlat eU eW hglueSup
    (proj_overlap_of_limit_desc (cO.w fk) iPt eRange htopV htopW hstageV hstageW
      (X.stalkOpensConePtIso_inv_π_stageIso_inv U s k) e₀' ek hek)⟩

end TauCeti.FiniteEtaleScheme
