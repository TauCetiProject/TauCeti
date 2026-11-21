/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Gluing.Over
public import TauCeti.AlgebraicGeometry.Limits.Spreading
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.CategoryTheory.Comma.Over
import TauCeti.RingTheory.Etale.Localization

/-!
# Spreading finite étale schemes from local rings

This file spreads finite étale schemes from the local scheme `Spec 𝒪_{S, s}` of a point `s : S` to
an affine open neighbourhood of `s`, and glues them with data already given over a quasi-compact
open subscheme `U ⊆ S`.

## Main results

* `TauCeti.FiniteEtaleScheme.exists_spread_fromSpecStalk`: every finite étale scheme over
  `Spec 𝒪_{S, s}` is the base change of a finite étale scheme over an affine open neighbourhood of
  `s`.
* `TauCeti.FiniteEtaleScheme.exists_spread_of_iso_fromSpecStalk`: given a finite étale cover over
  a quasi-compact open `U ⊆ S` and a finite étale cover over `Spec 𝒪_{S, s}` together with an
  isomorphism over `Spec 𝒪_{S, s} ×_S U`, there is an affine open neighbourhood `W ∋ s` and a
  finite étale cover over `U ⊔ W` restricting to the two given covers (Stacks, Lemma 32.20.4,
  Tag 0EY3, in the finite étale case).

## References

* [The Stacks Project, Lemma 32.20.4](https://stacks.math.columbia.edu/tag/0EY3)
-/

public section

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.FiniteEtaleScheme

private lemma fromSpecStalkOfMem_comp_basicOpen_isoSpec {S : Scheme.{u}} {W₀ : S.Opens}
    (hW₀ : IsAffineOpen W₀) {s : S} (hs₀ : s ∈ W₀)
    (f : (hW₀.primeIdealOf ⟨s, hs₀⟩).asIdeal.primeCompl)
    (eLoc : Localization.Away (f : Γ(S, W₀)) ≃+* Γ(S, S.basicOpen (f : Γ(S, W₀))))
    (heLoc : ∀ r : Γ(S, W₀),
      eLoc (algebraMap Γ(S, W₀) (Localization.Away (f : Γ(S, W₀))) r) =
        S.presheaf.map (homOfLE (S.basicOpen_le (f : Γ(S, W₀)))).op r)
    (φ : Localization.Away (f : Γ(S, W₀)) →+* S.presheaf.stalk s)
    (hφ : ∀ r : Γ(S, W₀),
      φ (algebraMap Γ(S, W₀) (Localization.Away (f : Γ(S, W₀))) r) =
        S.presheaf.germ W₀ s hs₀ r) :
    let hsW : s ∈ S.basicOpen (f : Γ(S, W₀)) :=
      (hW₀.mem_basicOpen_iff_notMem_primeIdealOf ⟨s, hs₀⟩ (f : Γ(S, W₀))).mpr f.property
    (S.basicOpen (f : Γ(S, W₀))).fromSpecStalkOfMem s hsW ≫
        ((hW₀.basicOpen (f : Γ(S, W₀))).isoSpec ≪≫
          Scheme.Spec.mapIso eLoc.toCommRingCatIso.op).hom =
      Spec.map (CommRingCat.ofHom φ) := by
  intro hsW
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op,
    RingEquiv.toCommRingCatIso_hom, IsAffineOpen.isoSpec_hom, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_toSpecΓ, ← Spec.map_comp]
  congr 1
  ext : 1
  apply IsLocalization.ringHom_ext (Submonoid.powers (f : Γ(S, W₀)))
  ext r
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
    Function.comp_apply, RingEquiv.coe_toRingHom, heLoc r, hφ r]
  exact S.presheaf.germ_res_apply (homOfLE (S.basicOpen_le (f : Γ(S, W₀)))) s hsW r

/-- Every finite étale scheme over `Spec 𝒪_{S, s}` spreads out to a finite étale scheme over an
affine open neighbourhood of `s`. -/
theorem exists_spread_fromSpecStalk {S : Scheme.{u}} (s : S)
    (Y : FiniteEtaleScheme (Spec (S.presheaf.stalk s))) :
    ∃ (W : S.Opens) (_ : IsAffineOpen W) (hs : s ∈ W) (YW : FiniteEtaleScheme W.toScheme),
      Nonempty ((pullback (W.fromSpecStalkOfMem s hs)).obj YW ≅ Y) := by
  obtain ⟨_, ⟨W₀, hW₀_mem, rfl⟩, hs₀, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hW₀ : IsAffineOpen W₀ := hW₀_mem
  have := essSurj_spec (S.presheaf.stalk s)
  obtain ⟨B, ⟨eB⟩⟩ := Functor.EssSurj.mem_essImage (spec (S.presheaf.stalk s)) Y
  let _ : Algebra Γ(S, W₀) (S.presheaf.stalk s) := S.presheaf.algebra_section_stalk ⟨s, hs₀⟩
  have hlocStalk : IsLocalization (hW₀.primeIdealOf ⟨s, hs₀⟩).asIdeal.primeCompl
      (S.presheaf.stalk s) := hW₀.isLocalization_stalk ⟨s, hs₀⟩
  obtain ⟨f, Bf, _, _, _, _, ⟨eAlg⟩⟩ :=
    TauCeti.Algebra.exists_etale_finite_algEquiv_tensorProduct_localizationAway
      (R := Γ(S, W₀)) (S := S.presheaf.stalk s)
      B.unop.obj (hW₀.primeIdealOf ⟨s, hs₀⟩).asIdeal.primeCompl
  let φ : Localization.Away (f : Γ(S, W₀)) →+* S.presheaf.stalk s :=
    IsLocalization.Away.lift (S := Localization.Away (f : Γ(S, W₀))) (f : Γ(S, W₀))
      (g := algebraMap Γ(S, W₀) (S.presheaf.stalk s)) (IsLocalization.map_units _ f)
  let _ : Algebra (Localization.Away (f : Γ(S, W₀))) (S.presheaf.stalk s) := φ.toAlgebra
  let W : S.Opens := S.basicOpen (f : Γ(S, W₀))
  have hW : IsAffineOpen W := hW₀.basicOpen (f : Γ(S, W₀))
  have hsW : s ∈ W :=
    (hW₀.mem_basicOpen_iff_notMem_primeIdealOf ⟨s, hs₀⟩ (f : Γ(S, W₀))).mpr f.property
  have hlocW : IsLocalization.Away (f : Γ(S, W₀)) Γ(S, W) :=
    hW₀.isLocalization_basicOpen (f : Γ(S, W₀))
  let eLoc : Localization.Away (f : Γ(S, W₀)) ≃+* Γ(S, W) :=
    (IsLocalization.algEquiv (Submonoid.powers (f : Γ(S, W₀)))
      (Localization.Away (f : Γ(S, W₀))) Γ(S, W)).toRingEquiv
  let isoW : W.toScheme ≅ Spec (.of (Localization.Away (f : Γ(S, W₀)))) :=
    hW.isoSpec ≪≫ Scheme.Spec.mapIso eLoc.toCommRingCatIso.op
  have hcomm : W.fromSpecStalkOfMem s hsW ≫ isoW.hom = Spec.map (CommRingCat.ofHom φ) :=
    fromSpecStalkOfMem_comp_basicOpen_isoSpec hW₀ hs₀ f eLoc
      (fun r ↦ (IsLocalization.algEquiv (Submonoid.powers (f : Γ(S, W₀)))
        (Localization.Away (f : Γ(S, W₀))) Γ(S, W)).commutes r)
      φ (fun r ↦ by
        simpa [φ] using DFunLike.congr_fun
          (RingHom.algebraMap_toAlgebra (S.presheaf.germ W₀ s hs₀).hom) r)
  let Yloc : FiniteEtaleScheme (Spec (.of (Localization.Away (f : Γ(S, W₀))))) :=
    (spec (.of (Localization.Away (f : Γ(S, W₀))))).obj
      (op (CommAlgCat.FiniteEtale.of (CommRingCat.of (Localization.Away (f : Γ(S, W₀)))) Bf))
  let YW : FiniteEtaleScheme W.toScheme := (pullback isoW.hom).obj Yloc
  refine ⟨W, hW, hsW, YW, ⟨?_ ≪≫ eB⟩⟩
  refine ((pullbackComp (W.fromSpecStalkOfMem s hsW) isoW.hom).symm.app Yloc) ≪≫
    eqToIso (congrArg (fun g ↦ (pullback g).obj Yloc) hcomm) ≪≫ ?_
  apply ObjectProperty.isoMk
  rw [pullback_obj_obj, spec_obj_obj, spec_obj_obj]
  exact TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv
    (Localization.Away (f : Γ(S, W₀))) Bf (S.presheaf.stalk s) B.unop.obj eAlg.symm

-- `HasAffineProperty.instIsZariskiLocalAtTarget` and
-- `HasRingHomProperty.instIsZariskiLocalAtTarget` are defs rather than global instances (to avoid
-- instance loops on `MorphismProperty Scheme`), and `HasAffineProperty @IsFinite _` uses a custom
-- predicate in Mathlib rather than `affineAnd`, so `inferInstance` cannot synthesize
-- `IsZariskiLocalAtTarget @IsFinite` or `@Etale` directly.
private lemma isZariskiLocalAtTarget_isFinite : IsZariskiLocalAtTarget @IsFinite.{u} := by
  observe hfin_aff : HasAffineProperty @IsFinite.{u}
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  exact @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hfin_aff

private lemma isZariskiLocalAtTarget_etale : IsZariskiLocalAtTarget @Etale.{u} :=
  HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.Etale)

/-- **Spreading out a finite étale cover glued at a local ring.** Given a finite étale cover `YU`
over a quasi-compact open subscheme `U ⊆ S` and a finite étale cover `Ys` over `Spec 𝒪_{S, s}`
together with an isomorphism over `Spec 𝒪_{S, s} ×_S U`, there exist an affine open neighbourhood
`W` of `s` and a finite étale cover over `U ⊔ W` restricting to `YU` on `U` and to `Ys` on
`Spec 𝒪_{S, s}`. -/
@[stacks 0EY3 "finite étale case"]
theorem exists_spread_of_iso_fromSpecStalk {S : Scheme.{u}} (U : S.Opens) [QuasiCompact U.ι]
    (s : S) (YU : FiniteEtaleScheme U.toScheme)
    (Ys : FiniteEtaleScheme (Spec (S.presheaf.stalk s)))
    (e : (pullback (S.fromSpecStalk s ∣_ U)).obj YU ≅
      (pullback (S.fromSpecStalk s ⁻¹ᵁ U).ι).obj Ys) :
    ∃ (W : S.Opens) (_ : IsAffineOpen W) (hs : s ∈ W)
      (Y' : FiniteEtaleScheme (U ⊔ W).toScheme),
      Nonempty ((pullback (S.homOfLE le_sup_left)).obj Y' ≅ YU) ∧
      Nonempty ((pullback ((U ⊔ W).fromSpecStalkOfMem s (Opens.mem_sup.mpr (Or.inr hs)))).obj Y' ≅
        Ys) := by
  -- Spread `Ys` to an affine open neighbourhood `W₁` of `s`.
  obtain ⟨W₁, _, hs₁, YW₁, ⟨e₁⟩⟩ := exists_spread_fromSpecStalk s Ys
  let U₁ : W₁.toScheme.Opens := W₁.ι ⁻¹ᵁ U
  have hqcU₁ : QuasiCompact U₁.ι := quasiCompact_ι_preimage W₁.ι U
  let A₁ : Over U₁.toScheme := (Over.pullback (W₁.ι ∣_ U)).obj YU.obj
  let B₁ : Over U₁.toScheme := (Over.pullback U₁.ι).obj YW₁.obj
  let X₁ : Over W₁.toScheme := (Over.map U₁.ι).obj A₁
  let Z₁ : Over W₁.toScheme := (Over.map U₁.ι).obj B₁
  have : QuasiCompact X₁.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd YU.obj.hom (W₁.ι ∣_ U) ≫ U₁.ι))
  have : QuasiSeparated X₁.hom :=
    inferInstanceAs (QuasiSeparated (pullback.snd YU.obj.hom (W₁.ι ∣_ U) ≫ U₁.ι))
  have : LocallyOfFinitePresentation X₁.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd YU.obj.hom (W₁.ι ∣_ U) ≫ U₁.ι))
  have : QuasiCompact Z₁.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd YW₁.obj.hom U₁.ι ≫ U₁.ι))
  have : QuasiSeparated Z₁.hom :=
    inferInstanceAs (QuasiSeparated (pullback.snd YW₁.obj.hom U₁.ι ≫ U₁.ι))
  have : LocallyOfFinitePresentation Z₁.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd YW₁.obj.hom U₁.ι ≫ U₁.ι))
  -- Compare `X₁` and `Z₁` over `Spec 𝒪_{W₁, s}` using `e` and `e₁`.
  let s₁ : W₁.toScheme := ⟨s, hs₁⟩
  let p₁ : Spec (W₁.toScheme.presheaf.stalk s₁) ⟶ W₁.toScheme := W₁.toScheme.fromSpecStalk s₁
  let τ := stalkOpenRestriction U W₁ s hs₁
  have hτU : τ ≫ (S.fromSpecStalk s ∣_ U) = p₁ ∣_ U₁ ≫ W₁.ι ∣_ U :=
    stalkOpenRestriction_comp_morphismRestrict U W₁ s hs₁
  have hτW₁ : τ ≫ (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫ W₁.fromSpecStalkOfMem s hs₁ =
      p₁ ∣_ U₁ ≫ U₁.ι :=
    stalkOpenRestriction_comp_ι_fromSpecStalkOfMem U W₁ s hs₁
  let e_ov : (Over.pullback (p₁ ∣_ U₁)).obj A₁ ≅ (Over.pullback (p₁ ∣_ U₁)).obj B₁ :=
    (Over.pullbackCompIso hτU.symm).app YU.obj ≪≫
      ((Over.pullbackCompIso (rfl : τ ≫ (S.fromSpecStalk s ∣_ U) = _)).app YU.obj).symm ≪≫
      (Over.pullback τ).mapIso ((finiteEtaleSchemeProperty _).ι.mapIso e) ≪≫
      (Over.pullback τ).mapIso
        ((Over.pullback (S.fromSpecStalk s ⁻¹ᵁ U).ι).mapIso
          ((finiteEtaleSchemeProperty _).ι.mapIso e₁.symm)) ≪≫
      (Over.pullback τ).mapIso
        ((Over.pullbackCompIso (rfl : (S.fromSpecStalk s ⁻¹ᵁ U).ι ≫
          W₁.fromSpecStalkOfMem s hs₁ = _)).app YW₁.obj) ≪≫
      (Over.pullbackCompIso hτW₁).app YW₁.obj ≪≫
      ((Over.pullbackCompIso (rfl : p₁ ∣_ U₁ ≫ U₁.ι = _)).app YW₁.obj).symm
  let e_p₁ : (Over.pullback p₁).obj X₁ ≅ (Over.pullback p₁).obj Z₁ :=
    (pullbackMapOpenIso p₁ U₁).app A₁ ≪≫
      (Over.map (p₁ ⁻¹ᵁ U₁).ι).mapIso e_ov ≪≫
      ((pullbackMapOpenIso p₁ U₁).app B₁).symm
  -- Spread `e_p₁` from `Spec 𝒪_{W₁, s}` to an affine open neighbourhood `V ⊆ W₁` of `s`.
  obtain ⟨V, hV, hsV, eV, -⟩ := exists_pullback_iso_fromSpecStalk (S := W₁.toScheme) s₁ e_p₁
  let eV_ov : (Over.pullback (V.ι ∣_ U₁)).obj A₁ ≅ (Over.pullback (V.ι ∣_ U₁)).obj B₁ :=
    (Over.fullyFaithfulMap (V.ι ⁻¹ᵁ U₁).ι).preimageIso
      (((pullbackMapOpenIso V.ι U₁).app A₁).symm ≪≫ eV ≪≫ (pullbackMapOpenIso V.ι U₁).app B₁)
  -- Push `V` forward to an affine open `W ⊆ W₁` in `S`, and glue `YU` with `YW₁|_W` over `U ⊔ W`.
  let W : S.Opens := W₁.ι ''ᵁ V
  obtain ⟨hW, hWW₁, hsW, hstalk_sup, hstalk_W₁⟩ :=
    affineImage_fromSpecStalkOfMem U W₁ hs₁ hV hsV
  let YW : FiniteEtaleScheme W.toScheme := (pullback (S.homOfLE hWW₁)).obj YW₁
  let isoInf := infImageOpenIso U W₁ V
  have hisoInf_U : isoInf.hom ≫ (V.ι ∣_ U₁) ≫ (W₁.ι ∣_ U) = S.homOfLE inf_le_left :=
    infImageOpenIso_hom_comp_left U W₁ V
  have hisoInf_W : isoInf.hom ≫ (V.ι ∣_ U₁) ≫ U₁.ι =
      S.homOfLE inf_le_right ≫ S.homOfLE hWW₁ :=
    infImageOpenIso_hom_comp_right U W₁ V
  let e_glue : (Over.pullback (S.homOfLE (inf_le_left : U ⊓ W ≤ U))).obj YU.obj ≅
      (Over.pullback (S.homOfLE (inf_le_right : U ⊓ W ≤ W))).obj YW.obj :=
    ((Over.pullbackCompIso hisoInf_U).app YU.obj).symm ≪≫
      (Over.pullback isoInf.hom).mapIso
        (((Over.pullbackCompIso (rfl : V.ι ∣_ U₁ ≫ W₁.ι ∣_ U = _)).app YU.obj).symm ≪≫
          eV_ov ≪≫
          (Over.pullbackCompIso (rfl : V.ι ∣_ U₁ ≫ U₁.ι = _)).app YW₁.obj) ≪≫
      (Over.pullbackCompIso hisoInf_W).app YW₁.obj ≪≫
      ((Over.pullbackCompIso (rfl : S.homOfLE inf_le_right ≫ S.homOfLE hWW₁ = _)).app YW₁.obj).symm
  have hpb := isPullback_opens_inf_le (X := S) (le_sup_left : U ≤ U ⊔ W) (le_sup_right : W ≤ U ⊔ W)
  have hcov := S.opensRange_homOfLE_sup U W
  let Y_over : Over (U ⊔ W).toScheme := glueOver hpb YU.obj YW.obj e_glue
  have : IsZariskiLocalAtTarget @IsFinite.{u} := isZariskiLocalAtTarget_isFinite
  have : IsZariskiLocalAtTarget @Etale.{u} := isZariskiLocalAtTarget_etale
  have hfin : IsFinite Y_over.hom :=
    IsZariskiLocalAtTarget.of_glueOver (P := @IsFinite.{u}) hpb hcov YU.obj YW.obj e_glue
      inferInstance inferInstance
  have het : Etale Y_over.hom :=
    IsZariskiLocalAtTarget.of_glueOver (P := @Etale.{u}) hpb hcov YU.obj YW.obj e_glue
      inferInstance inferInstance
  let Y' : FiniteEtaleScheme (U ⊔ W).toScheme :=
    ⟨Y_over, (finiteEtaleSchemeProperty_iff Y_over).mpr ⟨hfin, het⟩⟩
  refine ⟨W, hW, hsW, Y',
    ⟨ObjectProperty.isoMk _ (glueOverPullbackLeftIso hpb YU.obj YW.obj e_glue)⟩, ⟨?_⟩⟩
  refine ObjectProperty.isoMk _
    (((Over.pullbackCompIso hstalk_sup).app Y'.obj).symm ≪≫
      (Over.pullback (W.fromSpecStalkOfMem s hsW)).mapIso
        (glueOverPullbackRightIso hpb YU.obj YW.obj e_glue) ≪≫
      (Over.pullbackCompIso hstalk_W₁).app YW₁.obj ≪≫
      (finiteEtaleSchemeProperty _).ι.mapIso e₁)

end TauCeti.FiniteEtaleScheme
