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

section LimitSpreading

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Limits.Cone D)

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
          (Over.pullbackHomOfFstEq (D.map fj) b hb₁)
      (pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).inv.app Y₁ ≫
        (pullback (c.π.app j)).map β ≫
        (pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).hom.app Y₂ = α ∧
      Limits.pullback.map (c.π.app i₀) Y₁.obj.hom (D.map fj) Y₁.obj.hom (c.π.app j) (𝟙 _) (𝟙 _)
          (by simp) (by simp) ≫ b =
        Over.pullbackLeftSymm (c.π.app i₀) α.hom ≫
          Limits.pullback.map (c.π.app i₀) Y₂.obj.hom (D.map fj) Y₂.obj.hom (c.π.app j)
            (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  have : QuasiCompact Y₁.obj.hom := inferInstance
  have : QuasiSeparated Y₁.obj.hom := inferInstance
  have : LocallyOfFinitePresentation Y₂.obj.hom := inferInstance
  let α' : (Over.pullback (c.π.app i₀)).obj Y₁.obj ⟶
      (Over.pullback (c.π.app i₀)).obj Y₂.obj := α.hom
  let a := Over.pullbackLeftSymm (c.π.app i₀) α'
  have ha : a ≫ Limits.pullback.fst (c.π.app i₀) Y₂.obj.hom =
      Limits.pullback.fst (c.π.app i₀) Y₁.obj.hom :=
    Over.pullbackLeftSymm_fst (c.π.app i₀) α'
  obtain ⟨j, fj, b, hb₁, hb₂⟩ := hc.exists_pullbackMap_comp_eq a ha
  refine ⟨j, fj, b, hb₁, ObjectProperty.hom_ext _ ?_, hb₂⟩
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackCompIsoOfEq_inv_app_hom,
    pullbackCompIsoOfEq_hom_app_hom, pullback_map_hom]
  exact (Over.pullbackCompIsoOfEq_conj_hom_of_fstEq (c.w fj) hb₁ ha hb₂).trans
    (Over.pullbackHomOfFstEq_pullbackLeftSymm (c.π.app i₀) α')

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
  let eOver : (Over.pullback (c.π.app i₀)).obj Y₁.obj ≅
      (Over.pullback (c.π.app i₀)).obj Y₂.obj :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congr(($e.hom_inv_id).hom)
      inv_hom_id := congr(($e.inv_hom_id).hom) }
  let eSymm := Over.pullbackLeftSymmIso (c.π.app i₀) eOver
  have ha_iso : IsIso (Over.pullbackLeftSymm (c.π.app i₀) eOver.hom) := by
    rw [← Over.pullbackLeftSymmIso_hom (c.π.app i₀) eOver]
    exact eSymm.isIso_hom
  have : IsIso (Limits.pullback.map (c.π.app j) (Limits.pullback.fst (D.map fj) Y₁.obj.hom)
      (c.π.app j) (Limits.pullback.fst (D.map fj) Y₂.obj.hom) (𝟙 _) b (𝟙 _) (by simp)
      (by exact hb₁.symm)) :=
    (MorphismProperty.pullbackMap_iff_of_pullbackMap_comp_eq
      (.isomorphisms Scheme) fj (Over.pullbackLeftSymm_fst (c.π.app i₀) eOver.hom) hb₁ hb₂).mpr
      ha_iso
  obtain ⟨k, hkj, hk⟩ := hc.exists_isIso_pullbackMap b hb₁
  let β : (pullback (D.map fj)).obj Y₁ ⟶ (pullback (D.map fj)).obj Y₂ :=
    (finiteEtaleSchemeProperty (D.obj j)).homMk (Over.pullbackHomOfFstEq (D.map fj) b hb₁)
  let βK := (pullbackCompIsoOfEq (D.map hkj) (D.map fj) (D.map (hkj ≫ fj))
      (D.map_comp _ _).symm).inv.app Y₁ ≫
    (pullback (D.map hkj)).map β ≫
    (pullbackCompIsoOfEq (D.map hkj) (D.map fj) (D.map (hkj ≫ fj))
      (D.map_comp _ _).symm).hom.app Y₂
  let bK := Limits.pullback.map (D.map hkj) (Limits.pullback.fst (D.map fj) Y₁.obj.hom)
    (D.map hkj) (Limits.pullback.fst (D.map fj) Y₂.obj.hom) (𝟙 _) b (𝟙 _) (by simp)
    (by exact hb₁.symm)
  have : IsIso bK := hk
  let eIso := Limits.pullbackSymmetry Y₁.obj.hom (D.map (hkj ≫ fj)) ≪≫
    (Limits.pullbackRightPullbackFstIsoOfEq (D.map hkj) (D.map fj) (D.map (hkj ≫ fj))
      (D.map_comp hkj fj).symm Y₁.obj.hom).symm ≪≫
    asIso bK ≪≫
    Limits.pullbackRightPullbackFstIsoOfEq (D.map hkj) (D.map fj) (D.map (hkj ≫ fj))
      (D.map_comp hkj fj).symm Y₂.obj.hom ≪≫
    Limits.pullbackSymmetry (D.map (hkj ≫ fj)) Y₂.obj.hom
  have hbK : (Over.forget (D.obj k)).map βK.hom = eIso.hom := by
    simp only [βK, β, eIso, bK, ObjectProperty.FullSubcategory.comp_hom,
      pullbackCompIsoOfEq_inv_app_hom, pullbackCompIsoOfEq_hom_app_hom, pullback_map_hom,
      Iso.trans_hom, Iso.symm_hom, asIso_hom]
    exact Over.pullbackCompIsoOfEq_conj_left_eq_pullbackMap (D.map_comp hkj fj).symm b hb₁
  have : IsIso ((Over.forget (D.obj k)).map βK.hom) := by rw [hbK]; exact eIso.isIso_hom
  have : IsIso ((finiteEtaleSchemeProperty (D.obj k)).ι.map βK) :=
    isIso_of_reflects_iso βK.hom (Over.forget (D.obj k))
  have : IsIso βK := isIso_of_reflects_iso βK (finiteEtaleSchemeProperty (D.obj k)).ι
  refine ⟨k, hkj ≫ fj, asIso βK, ?_⟩
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
  have : IsIso eW.inv.hom := (finiteEtaleSchemeProperty _).ι.map_isIso eW.inv
  have : IsIso eW.inv.hom.left := (Over.forget _).map_isIso eW.inv.hom
  have : IsOpenImmersion (Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right)) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (IsPullback.of_hasPullback V'.obj.hom _).flip inferInstance
  have : Mono (Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right)) := IsOpenImmersion.mono _
  apply (cancel_mono eW.inv.hom.left).mp
  apply (cancel_mono (Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right))).mp
  have hLHS : ((pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
          (X.homOfLE le_sup_left)
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
          (X.homOfLE_homOfLE _ _)).inv.app V' ≫
        (pullback (X.homOfLE inf_le_left)).map eU.hom ≫ eGlue.hom).hom.left ≫
      Limits.pullback.fst YW.obj.hom (X.homOfLE inf_le_right) ≫
        eW.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right) =
      Limits.pullback.fst V'.obj.hom
        (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left)) := by
    have hstep : ((pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
            (X.homOfLE le_sup_left)
            (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
            (X.homOfLE_homOfLE _ _)).inv.app V' ≫
          (pullback (X.homOfLE inf_le_left)).map eU.hom ≫ eGlue.hom).hom.left ≫
        Limits.pullback.fst YW.obj.hom (X.homOfLE inf_le_right) ≫
          eW.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right) =
        ((pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
            (X.homOfLE le_sup_left)
            (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
            (X.homOfLE_homOfLE _ _)).inv.app V' ≫
          (pullback (X.homOfLE inf_le_left)).map eU.hom).hom.left ≫
        Limits.pullback.fst V.obj.hom (X.homOfLE inf_le_left) ≫
          eU.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_left) := by
      simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc]
      rw [← hcompat]
      rfl
    exact hstep.trans <|
      pullbackCompIsoOfEq_inv_map_hom_fst_inv_fst (X.homOfLE_homOfLE inf_le_left le_sup_left) eU
  have hRHS : ((pullbackCompIsoOfEq (X.homOfLE (U := U ⊓ W) (V := W) inf_le_right)
          (X.homOfLE le_sup_right)
          (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left))
          (X.homOfLE_homOfLE _ _)).inv.app V' ≫
        (pullback (X.homOfLE inf_le_right)).map eW.hom).hom.left ≫
      Limits.pullback.fst YW.obj.hom (X.homOfLE inf_le_right) ≫
        eW.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom (X.homOfLE le_sup_right) =
      Limits.pullback.fst V'.obj.hom
        (X.homOfLE (U := U ⊓ W) (V := U ⊔ W) (inf_le_left.trans le_sup_left)) :=
    pullbackCompIsoOfEq_inv_map_hom_fst_inv_fst
      (X.homOfLE_homOfLE (U := U ⊓ W) (V := W) (W := U ⊔ W) inf_le_right le_sup_right) eW
  exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    (hLHS.trans (hRHS.symm.trans ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm))))

/-- Transport a morphism between pullbacks of finite étale schemes along `m : A ⟶ B` using
identifications `h₁ : m ≫ g₁ = a₁` and `h₂ : m ≫ g₂ = a₂`. -/
private noncomputable def pullbackTransport {A B S₁ S₂ : Scheme.{u}} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂)
    {Y₁ : FiniteEtaleScheme S₁} {Y₂ : FiniteEtaleScheme S₂}
    (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    (pullback a₁).obj Y₁ ⟶ (pullback a₂).obj Y₂ :=
  (pullbackCompIsoOfEq m g₁ a₁ h₁).inv.app Y₁ ≫ (pullback m).map φ ≫
    (pullbackCompIsoOfEq m g₂ a₂ h₂).hom.app Y₂

/-- Transport an isomorphism between pullbacks of finite étale schemes along `m : A ⟶ B` using
identifications `h₁ : m ≫ g₁ = a₁` and `h₂ : m ≫ g₂ = a₂`. -/
private noncomputable def pullbackTransportIso {A B S₁ S₂ : Scheme.{u}} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂)
    {Y₁ : FiniteEtaleScheme S₁} {Y₂ : FiniteEtaleScheme S₂}
    (e : (pullback g₁).obj Y₁ ≅ (pullback g₂).obj Y₂) :
    (pullback a₁).obj Y₁ ≅ (pullback a₂).obj Y₂ :=
  ((pullbackCompIsoOfEq m g₁ a₁ h₁).app Y₁).symm ≪≫ (pullback m).mapIso e ≪≫
    (pullbackCompIsoOfEq m g₂ a₂ h₂).app Y₂

@[simp]
private theorem pullbackTransportIso_hom {A B S₁ S₂ : Scheme.{u}} {m : A ⟶ B}
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    (h₁ : m ≫ g₁ = a₁) (h₂ : m ≫ g₂ = a₂)
    {Y₁ : FiniteEtaleScheme S₁} {Y₂ : FiniteEtaleScheme S₂}
    (e : (pullback g₁).obj Y₁ ≅ (pullback g₂).obj Y₂) :
    (pullbackTransportIso h₁ h₂ e).hom = pullbackTransport h₁ h₂ e.hom :=
  rfl

private theorem pullbackTransport_comp {A B D S₁ S₂ : Scheme.{u}}
    {m₁ : A ⟶ B} {m₂ : B ⟶ D} {m : A ⟶ D}
    {g₁ : D ⟶ S₁} {g₂ : D ⟶ S₂} {b₁ : B ⟶ S₁} {b₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    (hm : m₁ ≫ m₂ = m) (hm₂₁ : m₂ ≫ g₁ = b₁) (hm₂₂ : m₂ ≫ g₂ = b₂)
    (hm₁₁ : m₁ ≫ b₁ = a₁) (hm₁₂ : m₁ ≫ b₂ = a₂) (ha₁ : m ≫ g₁ = a₁) (ha₂ : m ≫ g₂ = a₂)
    {Y₁ : FiniteEtaleScheme S₁} {Y₂ : FiniteEtaleScheme S₂}
    (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    pullbackTransport hm₁₁ hm₁₂ (pullbackTransport hm₂₁ hm₂₂ φ) = pullbackTransport ha₁ ha₂ φ :=
  pullbackCompIsoOfEq_conj_comp hm hm₂₁ hm₂₂ hm₁₁ hm₁₂ ha₁ ha₂ φ

private theorem pullbackTransport_of_eq_id {B S₁ S₂ : Scheme.{u}} {m : B ⟶ B} (hm : m = 𝟙 B)
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} (h₁ : m ≫ g₁ = g₁) (h₂ : m ≫ g₂ = g₂)
    {Y₁ : FiniteEtaleScheme S₁} {Y₂ : FiniteEtaleScheme S₂}
    (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    pullbackTransport h₁ h₂ φ = φ :=
  pullbackCompIsoOfEq_conj_of_eq_id hm h₁ h₂ φ

private theorem pullbackTransport_pullbackCompIsoOfEq_conj {A B C S₁ S₂ : Scheme.{u}}
    {a : A ⟶ B} {b : B ⟶ C} {ab : A ⟶ C} (hab : a ≫ b = ab)
    {f₁ : C ⟶ S₁} {f₂ : C ⟶ S₂} {bf₁ : B ⟶ S₁} {bf₂ : B ⟶ S₂} {abf₁ : A ⟶ S₁} {abf₂ : A ⟶ S₂}
    (hbf₁ : b ≫ f₁ = bf₁) (hbf₂ : b ≫ f₂ = bf₂) (habf₁ : a ≫ bf₁ = abf₁) (habf₂ : a ≫ bf₂ = abf₂)
    (hflat₁ : ab ≫ f₁ = abf₁) (hflat₂ : ab ≫ f₂ = abf₂)
    {Y₁ : FiniteEtaleScheme S₁} {Y₂ : FiniteEtaleScheme S₂}
    (φ : (pullback b).obj ((pullback f₁).obj Y₁) ⟶ (pullback b).obj ((pullback f₂).obj Y₂)) :
    pullbackTransport habf₁ habf₂
        ((pullbackCompIsoOfEq b f₁ bf₁ hbf₁).inv.app Y₁ ≫ φ ≫
          (pullbackCompIsoOfEq b f₂ bf₂ hbf₂).hom.app Y₂) =
      (pullbackCompIsoOfEq ab f₁ abf₁ hflat₁).inv.app Y₁ ≫
        pullbackTransport hab hab φ ≫
        (pullbackCompIsoOfEq ab f₂ abf₂ hflat₂).hom.app Y₂ := by
  simp only [pullbackTransport, Functor.map_comp, Category.assoc]
  rw [← pullbackCompIsoOfEq_comp_inv_app_assoc hab hbf₁ habf₁ hflat₁ Y₁,
    ← pullbackCompIsoOfEq_comp_hom_app hab hbf₂ habf₂ hflat₂ Y₂]

private theorem pullbackTransport_comp_map_inv {A B C D S₂ : Scheme.{u}}
    {m : A ⟶ B} {i₁ : B ⟶ C} {g₁ : A ⟶ C} {j₁ : C ⟶ D} {ij₁ : B ⟶ D} {gj₁ : A ⟶ D}
    {g₂ : B ⟶ S₂} {a₂ : A ⟶ S₂}
    (hmi : m ≫ i₁ = g₁) (hij : i₁ ≫ j₁ = ij₁) (hmij : m ≫ ij₁ = gj₁) (hgj : g₁ ≫ j₁ = gj₁)
    (h₂ : m ≫ g₂ = a₂)
    {Y₁ : FiniteEtaleScheme D} {Y₂ : FiniteEtaleScheme S₂}
    {V : FiniteEtaleScheme C} (e : (pullback j₁).obj Y₁ ⟶ V)
    (φ : (pullback i₁).obj V ⟶ (pullback g₂).obj Y₂) :
    (pullbackCompIsoOfEq g₁ j₁ gj₁ hgj).inv.app Y₁ ≫ (pullback g₁).map e ≫
        pullbackTransport hmi h₂ φ =
      pullbackTransport hmij h₂
        ((pullbackCompIsoOfEq i₁ j₁ ij₁ hij).inv.app Y₁ ≫ (pullback i₁).map e ≫ φ) := by
  simp only [pullbackTransport]
  rw [reassoc_of% ((pullbackCompIsoOfEq m i₁ g₁ hmi).inv.naturality e),
    pullbackCompIsoOfEq_comp_inv_app_assoc hmi hij hmij hgj Y₁,
    ← (pullback m).map_comp_assoc, ← (pullback m).map_comp_assoc, Category.assoc]

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
    simpa only [pullbackTransport, Category.assoc, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
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
    exact pullbackTransport_comp rfl hsWjW hsWmapk rfl rfl hOsW_jW hOsW_mapk eW.hom
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
      (X.stalkOpensConePtIso_inv_π_stageIso_inv U s k) hm_mapk e₀' ek hek)⟩

end TauCeti.FiniteEtaleScheme
