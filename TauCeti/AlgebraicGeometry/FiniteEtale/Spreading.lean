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

section LimitSpreading

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Limits.Cone D)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
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
        (pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).hom.app Y₂ = α := by
  have : QuasiCompact Y₁.obj.hom := inferInstance
  have : QuasiSeparated Y₁.obj.hom := inferInstance
  have : LocallyOfFinitePresentation Y₂.obj.hom := inferInstance
  obtain ⟨j, fj, β, hβ⟩ := hc.exists_hom_overPullback_of_isLimit Y₁.obj Y₂.obj α.hom
  refine ⟨j, fj, (finiteEtaleSchemeProperty (D.obj j)).homMk β, ObjectProperty.hom_ext _ ?_⟩
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackCompIsoOfEq_inv_app_hom,
    pullbackCompIsoOfEq_hom_app_hom, pullback_map_hom]
  exact (Over.pullbackTransport_def (c.w fj) (c.w fj) β).symm.trans hβ

/-- Along a cofiltered limit of quasi-compact schemes with affine transition morphisms, two
morphisms between finite étale schemes at stage `i₀` that become equal on the limit already become
equal at some stage `k` mapping to `i₀`. -/
@[stacks 01ZM "for finite étale schemes"]
theorem exists_pullback_map_eq_of_isLimit (hc : Limits.IsLimit c) {i₀ : I}
    {Y₁ Y₂ : FiniteEtaleScheme (D.obj i₀)} (β₁ β₂ : Y₁ ⟶ Y₂)
    (h : (pullback (c.π.app i₀)).map β₁ = (pullback (c.π.app i₀)).map β₂) :
    ∃ (k : I) (fk : k ⟶ i₀), (pullback (D.map fk)).map β₁ = (pullback (D.map fk)).map β₂ := by
  have : QuasiCompact Y₁.obj.hom := inferInstance
  have : LocallyOfFiniteType Y₂.obj.hom := inferInstance
  obtain ⟨k, fk, hk⟩ :=
    hc.exists_overPullback_map_eq_of_isLimit β₁.hom β₂.hom (congrArg (·.hom) h)
  exact ⟨k, fk, ObjectProperty.hom_ext _ hk⟩

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
  have : QuasiCompact Y₁.obj.hom := inferInstance
  have : QuasiSeparated Y₁.obj.hom := inferInstance
  have : LocallyOfFinitePresentation Y₁.obj.hom := inferInstance
  have : QuasiCompact Y₂.obj.hom := inferInstance
  have : QuasiSeparated Y₂.obj.hom := inferInstance
  have : LocallyOfFinitePresentation Y₂.obj.hom := inferInstance
  obtain ⟨k, fk, ek, hek⟩ := hc.exists_iso_overPullback_of_isLimit Y₁.obj Y₂.obj
    ((finiteEtaleSchemeProperty _).ι.mapIso e)
  refine ⟨k, fk, ObjectProperty.isoMk _ ek, ObjectProperty.hom_ext _ ?_⟩
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackCompIsoOfEq_inv_app_hom,
    pullbackCompIsoOfEq_hom_app_hom, pullback_map_hom]
  exact (Over.pullbackTransport_def (c.w fk) (c.w fk) ek.hom).symm.trans hek

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
  exact exists_pullbackCompIsoOfEq_of_isPullback hpb hcover
    (X.homOfLE_homOfLE _ _) (X.homOfLE_homOfLE _ _) eGlue

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
    (hek : pullbackTransport hab hab ek.hom =
      ((pullbackCompIsoOfEq ab f₁ (ab ≫ f₁) rfl).app Y₁ ≪≫
        pullbackTransportIso htop₁ htop₂ e₀' ≪≫
        ((pullbackCompIsoOfEq ab f₂ (ab ≫ f₂) rfl).app Y₂).symm).hom) :
    pullbackTransport hm₁ hm₂ (pullbackTransportIso hstage₁ hstage₂
        (((pullbackCompIsoOfEq b f₁ _ rfl).app Y₁).symm ≪≫ ek ≪≫
          (pullbackCompIsoOfEq b f₂ _ rfl).app Y₂)).hom =
      e₀'.hom := by
  let ekFlat := ((pullbackCompIsoOfEq b f₁ _ rfl).app Y₁).symm ≪≫ ek ≪≫
    (pullbackCompIsoOfEq b f₂ _ rfl).app Y₂
  have hab₁ : a ≫ (b ≫ f₁) = ab ≫ f₁ := by rw [← Category.assoc, hab]
  have hab₂ : a ≫ (b ≫ f₂) = ab ≫ f₂ := by rw [← Category.assoc, hab]
  have hekFlat :
      pullbackTransport hab₁ hab₂ ekFlat.hom = pullbackTransport htop₁ htop₂ e₀'.hom := by
    rw [← pullbackTransportIso_hom htop₁ htop₂ e₀']
    simpa [ekFlat] using
      (pullbackTransport_pullbackCompIsoOfEq_conj hab rfl rfl hab₁ hab₂ rfl rfl ek.hom).trans <|
        by rw [hek]; simp
  have hae₁ : (iPt.inv ≫ a) ≫ (b ≫ f₁) = g₁ := by
    rw [Category.assoc, hab₁, ← htop₁, Iso.inv_hom_id_assoc]
  have hae₂ : (iPt.inv ≫ a) ≫ (b ≫ f₂) = g₂ := by
    rw [Category.assoc, hab₂, ← htop₂, Iso.inv_hom_id_assoc]
  have ha₁ : iPt.inv ≫ (ab ≫ f₁) = g₁ := by rw [← htop₁, Iso.inv_hom_id_assoc]
  have ha₂ : iPt.inv ≫ (ab ≫ f₂) = g₂ := by rw [← htop₂, Iso.inv_hom_id_assoc]
  have hinv_id₁ : (iPt.inv ≫ iPt.hom) ≫ g₁ = g₁ := by rw [iPt.inv_hom_id, Category.id_comp]
  have hinv_id₂ : (iPt.inv ≫ iPt.hom) ≫ g₂ = g₂ := by rw [iPt.inv_hom_id, Category.id_comp]
  have hm_eRange : (iPt.inv ≫ a ≫ eRange.inv) ≫ eRange.hom = iPt.inv ≫ a := by simp
  rw [pullbackTransportIso_hom,
    pullbackTransport_comp hm_eRange hstage₁ hstage₂ hm₁ hm₂ hae₁ hae₂ ekFlat.hom,
    ← pullbackTransport_comp rfl hab₁ hab₂ ha₁ ha₂ hae₁ hae₂ ekFlat.hom,
    hekFlat,
    pullbackTransport_comp rfl htop₁ htop₂ ha₁ ha₂ hinv_id₁ hinv_id₂ e₀'.hom,
    pullbackTransport_of_eq_id iPt.inv_hom_id hinv_id₁ hinv_id₂ e₀'.hom]

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
    (hmGlue : pullbackTransport hmU
          (by rw [← Category.assoc, hmW, Category.assoc, hsWmapk]) eGlueFlat.hom =
      (e₀ ≪≫ (pullback ιOs).mapIso eW₀.symm ≪≫
        (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).app YW₀).hom) :
    (pullbackCompIsoOfEq gU jU (ιOs ≫ sUW) hgUjU).inv.app V' ≫ (pullback gU).map eU.hom ≫ e₀.hom =
      (pullbackCompIsoOfEq ιOs sUW (ιOs ≫ sUW) rfl).inv.app V' ≫ (pullback ιOs).map
        (pullbackTransportIso hsWjW hsWmapk eW ≪≫ eW₀).hom := by
  let tailIso := (pullback ιOs).mapIso eW₀.symm ≪≫
    (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).app YW₀
  rw [← cancel_mono tailIso.hom]
  have hm_ij : m ≫ ij = ιOs ≫ sUW := by rw [← hiUjU, ← Category.assoc, hmU, hgUjU]
  have hm_sW₀ : m ≫ (iW ≫ mapk) = ιOs ≫ sW₀ := by
    rw [← Category.assoc, hmW, Category.assoc, hsWmapk]
  have hOsW_jW : (ιOs ≫ sW) ≫ jW = ιOs ≫ sUW := by rw [Category.assoc, hsWjW]
  have hOsW_mapk : (ιOs ≫ sW) ≫ mapk = ιOs ≫ sW₀ := by rw [Category.assoc, hsWmapk]
  have hSup : ((pullbackCompIsoOfEq iU jU ij hiUjU).inv.app V' ≫ (pullback iU).map eU.hom) ≫
        eGlueFlat.hom = pullbackTransport hiWjW rfl eW.hom := by
    have h := congrArg (· ≫ (pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).hom.app YW₀) hglueSup
    simpa only [pullbackTransport_def, Category.assoc, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
      Iso.inv_hom_id_app, Category.comp_id] using h
  have hRHS :
      (pullbackCompIsoOfEq ιOs sUW (ιOs ≫ sUW) rfl).inv.app V' ≫
          (pullback ιOs).map (pullbackTransportIso hsWjW hsWmapk eW ≪≫ eW₀).hom ≫ tailIso.hom =
        pullbackTransport hOsW_jW hOsW_mapk eW.hom := by
    have hes : (pullback ιOs).map (pullbackTransportIso hsWjW hsWmapk eW ≪≫ eW₀).hom ≫
          tailIso.hom =
        (pullback ιOs).map (pullbackTransport hsWjW hsWmapk eW.hom) ≫
          (pullbackCompIsoOfEq ιOs sW₀ (ιOs ≫ sW₀) rfl).hom.app YW₀ := by
      simp [tailIso, ← (pullback ιOs).map_comp_assoc]
    rw [hes]
    exact (pullbackTransport_def rfl rfl (pullbackTransport hsWjW hsWmapk eW.hom)).symm.trans
      (pullbackTransport_comp rfl hsWjW hsWmapk rfl rfl hOsW_jW hOsW_mapk eW.hom)
  have hLHS :
      (pullbackCompIsoOfEq gU jU (ιOs ≫ sUW) hgUjU).inv.app V' ≫
          (pullback gU).map eU.hom ≫ e₀.hom ≫ tailIso.hom =
        pullbackTransport hOsW_jW hOsW_mapk eW.hom := by
    rw [← Iso.trans_hom e₀ tailIso, ← hmGlue,
      pullbackTransport_comp_map_inv hmU hiUjU hm_ij hgUjU hm_sW₀ eU.hom eGlueFlat.hom,
      ← Category.assoc, hSup]
    exact pullbackTransport_comp hmW hiWjW rfl hm_ij hm_sW₀ hOsW_jW hOsW_mapk eW.hom
  simp only [Category.assoc]
  exact hLHS.trans hRHS.symm

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
        ((le_sup_right : W.opens ≤ U ⊔ W.opens) W.mem))).obj V' ≅ Ys),
      (pullbackCompIsoOfEq ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl)
          (X.homOfLE le_sup_left)
          ((X.fromSpecStalk s ⁻¹ᵁ U).ι ≫
            (U ⊔ W.opens).fromSpecStalkOfMem s ((le_sup_right : W.opens ≤ U ⊔ W.opens) W.mem))
          (by rw [← cancel_mono (U ⊔ W.opens).ι, Category.assoc, Category.assoc, X.homOfLE_ι,
                Scheme.Hom.resLE_comp_ι, (U ⊔ W.opens).fromSpecStalkOfMem_ι])).inv.app V' ≫
        (pullback ((X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl)).map eU.hom ≫
        e₀.hom =
      (pullbackCompIsoOfEq (X.fromSpecStalk s ⁻¹ᵁ U).ι
          ((U ⊔ W.opens).fromSpecStalkOfMem s ((le_sup_right : W.opens ≤ U ⊔ W.opens) W.mem))
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
      pullbackTransportIso htopV htopW e₀' ≪≫
      ((pullbackCompIsoOfEq (cO.π.app j₀) fW _ rfl).app YW₀).symm)
  -- Phase 3: Transport `ek` to `U ⊓ W` and glue `V` with `YW₀|_{W}` over `U ⊔ W`.
  let W : X.AffineOpenNhds s := k.left; let eRange := X.stalkOpensStageIso U s k
  let mapk := X.homOfLE (Scheme.AffineOpenNhds.le_iff.mp (leOfHom k.hom))
  let iU := X.homOfLE (U := U ⊓ W.opens) (V := U) inf_le_left
  let iW := X.homOfLE (U := U ⊓ W.opens) (V := W.opens) inf_le_right
  have hstageV : eRange.hom ≫ (DO.map fk ≫ fV) = iU := X.stalkOpensStageIso_hom_map_toOpen U s fk
  have hstageW := X.stalkOpensStageIso_hom_map_toNhds U s fk
  let ekFlat := ((pullbackCompIsoOfEq (DO.map fk) fV _ rfl).app V).symm ≪≫ ek ≪≫
    (pullbackCompIsoOfEq (DO.map fk) fW _ rfl).app YW₀
  let eGlueFlat := pullbackTransportIso hstageV hstageW ekFlat
  obtain ⟨V', eU, eW, hglueSup⟩ := exists_sup_of_iso_inf V ((pullback mapk).obj YW₀)
    (eGlueFlat ≪≫ ((pullbackCompIsoOfEq iW mapk (iW ≫ mapk) rfl).app YW₀).symm)
  -- Phase 4: Assemble the stalk isomorphism `es` and deduce overlap compatibility.
  let sW := W.opens.fromSpecStalkOfMem s W.mem
  let sUW := (U ⊔ W.opens).fromSpecStalkOfMem s ((le_sup_right : W.opens ≤ U ⊔ W.opens) W.mem)
  have hsW_jW : sW ≫ X.homOfLE le_sup_right = sUW := by
    rw [← cancel_mono (U ⊔ W.opens).ι]; simp [sW, sUW]
  have hsW_mapk : sW ≫ mapk = sW₀ := by rw [← cancel_mono W₀.opens.ι]; simp [sW, mapk, sW₀, W]
  have hgU_jU : gU ≫ X.homOfLE le_sup_left = ιOs ≫ sUW := by
    rw [← cancel_mono (U ⊔ W.opens).ι]; simp [gU, ιOs, sUW]
  have hm_mapk : (iPt.inv ≫ cO.π.app k ≫ eRange.inv) ≫ (iW ≫ mapk) = ιOs ≫ sW₀ := by
    rw [← Category.assoc, X.stalkOpensConePtIso_inv_π_stageIso_inv_nhds U s k, Category.assoc,
      hsW_mapk]
  let es := pullbackTransportIso hsW_jW hsW_mapk eW ≪≫ eW₀
  refine ⟨W, V', eU, es, spread_gluing_compat (X.homOfLE_homOfLE _ _) (X.homOfLE_homOfLE _ _)
    hgU_jU hsW_jW hsW_mapk (X.stalkOpensConePtIso_inv_π_stageIso_inv U s k)
    (X.stalkOpensConePtIso_inv_π_stageIso_inv_nhds U s k) eW₀ e₀ eGlueFlat eU eW hglueSup
    (overlap_of_limit_desc (cO.w fk) iPt eRange htopV htopW hstageV hstageW
      (X.stalkOpensConePtIso_inv_π_stageIso_inv U s k) hm_mapk e₀' ek
      ((pullbackTransport_def (cO.w fk) (cO.w fk) ek.hom).trans hek))⟩

end TauCeti.FiniteEtaleScheme
