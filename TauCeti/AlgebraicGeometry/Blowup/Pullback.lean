/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Blowing up the inverse image of the centre

Let `I` be an ideal sheaf on a scheme `X` and let `g : X' ⟶ X` be a morphism of schemes. The
inverse image `I.comap g` cuts out the scheme-theoretic inverse image `g⁻¹(V(I))`. On the blowup
`Bl_{I.comap g} X'` the centre `V(I)` pulls back to the exceptional divisor, an effective Cartier
divisor, so the universal property of `Bl_I X` gives a morphism of blowups over `g`
(`AlgebraicGeometry.Scheme.IdealSheafData.blowupMap`), and with it a comparison morphism

`Bl_{I.comap g} X' ⟶ X' ×_X Bl_I X`

over `X'` (`AlgebraicGeometry.Scheme.IdealSheafData.blowupBaseChangeHom`).

* It is always a closed immersion. Over affine opens `U` of `X` and `U'` of `X'` with
  `g(U') ⊆ U`, it is the comparison `Proj S[(IS)t] ⟶ Spec S ×_{Spec R} Proj R[It]` of affine
  blowups for `R = Γ(X, U)`, `S = Γ(X', U')` and `I = I(U)`, which is a closed immersion
  (`TauCeti.AlgebraicGeometry.isClosedImmersion_affineBlowupBaseChangeHom`); these opens cover
  `X' ×_X Bl_I X`.
* For flat `g` it is an isomorphism: then the centre also pulls back to an effective Cartier
  divisor on `X' ×_X Bl_I X`, and the universal property of `Bl_{I.comap g} X'` gives the inverse.
  So blowing up commutes with flat base change, in particular with restriction to open
  subschemes.

When `g` is a closed immersion, for instance the inclusion of a closed subscheme `Z` of `X`, the
morphism `Bl_{I.comap g} Z ⟶ Bl_I X` is therefore a closed immersion. This closed subscheme of
`Bl_I X`, the blowup of `Z` along the inverse image of the centre, is the *strict transform* of
`Z` (Stacks Project, Definition 080D and Lemma 080E); its description as the scheme-theoretic
closure of the inverse image of `Z ∖ V(I)` is in
`TauCeti/AlgebraicGeometry/Blowup/StrictTransform.lean`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.blowupMap I g`: the morphism
  `Bl_{I.comap g} X' ⟶ Bl_I X` over `g`.
* `AlgebraicGeometry.Scheme.IdealSheafData.blowupBaseChangeHom I g`: the comparison morphism
  `Bl_{I.comap g} X' ⟶ X' ×_X Bl_I X`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_blowupBaseChangeHom`: the comparison
  is a closed immersion.
* `AlgebraicGeometry.Scheme.IdealSheafData.isIso_blowupBaseChangeHom`: for flat `g` it is an
  isomorphism, and `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_blowupMap_of_flat`: the
  square formed by the two blowups over `g` is cartesian.
* `AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_blowupMap`: for a closed immersion
  `g`, the morphism of blowups `Bl_{I.comap g} X' ⟶ Bl_I X` is a closed immersion;
  `AlgebraicGeometry.Scheme.IdealSheafData.isOpenImmersion_blowupMap`: for an open immersion `g`
  it is an open immersion, onto the preimage of the image of `g`
  (`AlgebraicGeometry.Scheme.IdealSheafData.opensRange_blowupMap`).

## References

* [The Stacks Project, Lemma 0805](https://stacks.math.columbia.edu/tag/0805): the blowup of the
  inverse image of the centre is a closed subscheme of the base change of the blowup, equal to it
  for flat base change.
* [The Stacks Project, Definition 080D](https://stacks.math.columbia.edu/tag/080D): the strict
  transform.
* [The Stacks Project, Lemma 080E](https://stacks.math.columbia.edu/tag/080E): the strict
  transform of a closed subscheme is the blowup of that closed subscheme along the inverse image
  of the centre.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry

variable {X X' : Scheme.{u}} (I : X.IdealSheafData) (g : X' ⟶ X)

/-! ### The morphism of blowups and the comparison morphism -/

/-- The centre `V(I)` pulls back to an effective Cartier divisor on `Bl_{I.comap g} X'`, along
the structure morphism followed by `g`: it is the exceptional divisor of that blowup. -/
theorem isEffectiveCartier_comap_blowupToBase_comp :
    (I.comap ((I.comap g).blowupToBase ≫ g)).IsEffectiveCartier := by
  rw [comap_comp]
  exact (I.comap g).isEffectiveCartier_comap_blowupToBase

/-- The **morphism of blowups over `g`**: the morphism `Bl_{I.comap g} X' ⟶ Bl_I X` lifting
`Bl_{I.comap g} X' ⟶ X' ⟶ X` (`blowupMap_blowupToBase`), the unique such lift
(`eq_blowupMap`). It is a closed immersion when `g` is (`isClosedImmersion_blowupMap`), and an
open immersion when `g` is (`isOpenImmersion_blowupMap`). -/
def blowupMap : (I.comap g).blowup ⟶ I.blowup :=
  I.blowupLift ((I.comap g).blowupToBase ≫ g) (I.isEffectiveCartier_comap_blowupToBase_comp g)

/-- The morphism of blowups lies over `g`. -/
@[reassoc (attr := simp)]
theorem blowupMap_blowupToBase :
    I.blowupMap g ≫ I.blowupToBase = (I.comap g).blowupToBase ≫ g :=
  I.blowupLift_blowupToBase _ _

/-- Every morphism `Bl_{I.comap g} X' ⟶ Bl_I X` over `g` is the morphism of blowups. -/
theorem eq_blowupMap {h : (I.comap g).blowup ⟶ I.blowup}
    (hh : h ≫ I.blowupToBase = (I.comap g).blowupToBase ≫ g) : h = I.blowupMap g :=
  I.eq_blowupLift _ hh

/-- Lifting through `Bl_{I.comap g} X'` and then mapping to `Bl_I X` is lifting the composite
through `Bl_I X`. -/
@[reassoc]
theorem blowupLift_blowupMap {T : Scheme.{u}} (f : T ⟶ X')
    (hf : ((I.comap g).comap f).IsEffectiveCartier) (hfg : (I.comap (f ≫ g)).IsEffectiveCartier) :
    (I.comap g).blowupLift f hf ≫ I.blowupMap g = I.blowupLift (f ≫ g) hfg :=
  I.eq_blowupLift hfg
    (by rw [Category.assoc, blowupMap_blowupToBase, blowupLift_blowupToBase_assoc])

/-- The exceptional divisor of `Bl_I X` pulls back along the morphism of blowups to the exceptional
divisor of `Bl_{I.comap g} X'`. -/
theorem comap_comap_blowupMap :
    (I.comap I.blowupToBase).comap (I.blowupMap g) =
      (I.comap g).comap (I.comap g).blowupToBase := by
  rw [← comap_comp, blowupMap_blowupToBase, comap_comp]

/-- The **comparison of blowups under base change**: the morphism
`Bl_{I.comap g} X' ⟶ X' ×_X Bl_I X` with components the structure morphism of the blowup of `X'`
and the morphism of blowups. It is a closed immersion (`isClosedImmersion_blowupBaseChangeHom`),
and an isomorphism for flat `g` (`isIso_blowupBaseChangeHom`). -/
def blowupBaseChangeHom : (I.comap g).blowup ⟶ pullback g I.blowupToBase :=
  pullback.lift (I.comap g).blowupToBase (I.blowupMap g) (I.blowupMap_blowupToBase g).symm

/-- The comparison is a morphism over `X'`. -/
@[reassoc (attr := simp)]
theorem blowupBaseChangeHom_fst :
    I.blowupBaseChangeHom g ≫ pullback.fst _ _ = (I.comap g).blowupToBase :=
  pullback.lift_fst _ _ _

/-- The projection of the comparison to `Bl_I X` is the morphism of blowups. -/
@[reassoc (attr := simp)]
theorem blowupBaseChangeHom_snd :
    I.blowupBaseChangeHom g ≫ pullback.snd _ _ = I.blowupMap g :=
  pullback.lift_snd _ _ _

/-- Two morphisms into `X' ×_X Bl_I X` agree if they agree after projecting to `X'` and the
centre `V(I)` pulls back to an effective Cartier divisor along their common composite to `X`. -/
theorem pullback_blowupToBase_hom_ext {T : Scheme.{u}} {u v : T ⟶ pullback g I.blowupToBase}
    (h : u ≫ pullback.fst _ _ = v ≫ pullback.fst _ _)
    (hf : (I.comap (u ≫ pullback.fst _ _ ≫ g)).IsEffectiveCartier) : u = v := by
  refine pullback.hom_ext h (I.blowup_hom_ext ?_ ?_)
  · simp only [Category.assoc, ← pullback.condition, reassoc_of% h]
  · rwa [Category.assoc, ← pullback.condition]

/-! ### Flat base change -/

section Flat

variable [Flat g]

/-- For flat `g`, the inverse image of the centre is an effective Cartier divisor on
`X' ×_X Bl_I X`: it is the pullback of the exceptional divisor along the flat projection to
`Bl_I X`. -/
private theorem isEffectiveCartier_comap_comap_pullback_fst :
    ((I.comap g).comap (pullback.fst g I.blowupToBase)).IsEffectiveCartier := by
  rw [← comap_comp, pullback.condition, comap_comp]
  exact I.isEffectiveCartier_comap_blowupToBase.comap _

/-- **Blowing up commutes with flat base change**: for flat `g`, the comparison
`Bl_{I.comap g} X' ⟶ X' ×_X Bl_I X` is an isomorphism. Its inverse is the lift of the projection
`X' ×_X Bl_I X ⟶ X'` given by the universal property of `Bl_{I.comap g} X'`. -/
instance isIso_blowupBaseChangeHom : IsIso (I.blowupBaseChangeHom g) := by
  set ψ := (I.comap g).blowupLift (pullback.fst g I.blowupToBase)
    (I.isEffectiveCartier_comap_comap_pullback_fst g)
  refine ⟨ψ, ?_, ?_⟩
  · refine (I.comap g).blowup_hom_ext (by simp [ψ]) ?_
    simpa [ψ] using (I.comap g).isEffectiveCartier_comap_blowupToBase
  · refine I.pullback_blowupToBase_hom_ext g (by simp [ψ]) ?_
    rw [Category.assoc, blowupBaseChangeHom_fst_assoc, (I.comap g).blowupLift_blowupToBase_assoc,
      comap_comp]
    exact I.isEffectiveCartier_comap_comap_pullback_fst g

/-- **The blowup of `X'` along the inverse image of the centre is the base change of the blowup
of `X` along `V(I)`**, for flat `g`: the square formed by the two blowups over `g` is
cartesian. -/
theorem isPullback_blowupMap_of_flat :
    IsPullback (I.comap g).blowupToBase (I.blowupMap g) g I.blowupToBase :=
  IsPullback.of_iso_pullback ⟨(I.blowupMap_blowupToBase g).symm⟩
    (asIso (I.blowupBaseChangeHom g)) (I.blowupBaseChangeHom_fst g)
    (I.blowupBaseChangeHom_snd g)

end Flat

/-- **Blowing up commutes with restriction to open subschemes**: for an open immersion `g`, the
morphism of blowups `Bl_{I.comap g} X' ⟶ Bl_I X` is an open immersion, with image the preimage of
the image of `g` (`opensRange_blowupMap`). -/
instance isOpenImmersion_blowupMap [IsOpenImmersion g] : IsOpenImmersion (I.blowupMap g) :=
  MorphismProperty.of_isPullback (I.isPullback_blowupMap_of_flat g) ‹_›

/-- For an open immersion `g`, the image of the morphism of blowups is the preimage in `Bl_I X` of
the image of `g`. -/
theorem opensRange_blowupMap [IsOpenImmersion g] :
    (I.blowupMap g).opensRange = I.blowupToBase ⁻¹ᵁ g.opensRange := by
  rw [← Scheme.Hom.opensRange_pullbackSnd,
    ← Scheme.Hom.opensRange_comp_of_isIso (I.blowupBaseChangeHom g)]
  congr 1
  exact (I.blowupBaseChangeHom_snd g).symm

/-! ### The comparison is a closed immersion -/

/-- The comparison of affine blowups `Proj S[J't] ⟶ Spec S ×_{Spec R} Proj R[Jt]`, for an
ideal `J'` of `S` equal to the extension of the ideal `J` of `R`: a closed immersion over
`Spec S`. -/
private theorem exists_isClosedImmersion_reesAlgebra {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (J : Ideal R) (J' : Ideal S) (hJ : J.map φ.hom = J') :
    ∃ c : Proj (reesAlgebra.grade J') ⟶
        pullback (Proj.toSpecCoeff (reesAlgebra.grade J)) (Spec.map φ),
      IsClosedImmersion c ∧ c ≫ pullback.snd _ _ = Proj.toSpecCoeff (reesAlgebra.grade J') := by
  subst hJ
  let := φ.hom.toAlgebra
  -- with this algebra structure `algebraMap R S` is `φ.hom` by definition
  -- (`RingHom.algebraMap_toAlgebra`), and `CommRingCat.ofHom φ.hom` is `φ` by definition
  -- (`CommRingCat.ofHom_hom`), so the affine comparison has exactly the required type
  exact ⟨affineBlowupBaseChangeHom J S, inferInstance, affineBlowupBaseChangeHom_snd J S⟩

/-- Over affine opens `U` of `X` and `U'` of `X'` with `g(U') ⊆ U`, the comparison of blowups is
the base change of a closed immersion along an open immersion whose image contains the preimage
of `U'`: the affine chart of `Bl_{I.comap g} X'` over `U'` is the pullback of the comparison along
the open immersion `Spec Γ(X', U') ×_{Spec Γ(X, U)} Proj Γ(X, U)[I(U)t] ⟶ X' ×_X Bl_I X`, and
over it the comparison is the closed immersion of affine blowups. -/
private theorem exists_isPullback_blowupBaseChangeHom {U : X.Opens} {U' : X'.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (e : U' ≤ g ⁻¹ᵁ U) :
    ∃ (B : Scheme.{u}) (b : B ⟶ pullback g I.blowupToBase)
      (c : Proj (reesAlgebra.grade ((I.comap g).ideal ⟨U', hU'⟩)) ⟶ B),
      IsOpenImmersion b ∧ IsClosedImmersion c ∧
        IsPullback ((I.comap g).blowupChart hU') c (I.blowupBaseChangeHom g) b ∧
        pullback.fst g I.blowupToBase ⁻¹' U' ⊆ Set.range b := by
  obtain ⟨c, hc, hcs⟩ := exists_isClosedImmersion_reesAlgebra (g.appLE U U' e)
    (I.ideal ⟨U, hU⟩) _ (I.ideal_comap_of_le g ⟨U, hU⟩ ⟨U', hU'⟩ e).symm
  have hsq : Spec.map (g.appLE U U' e) ≫ hU.fromSpec = hU'.fromSpec ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g hU hU' e
  -- `Spec Γ(X', U') ×_{Spec Γ(X, U)} Proj Γ(X, U)[I(U)t]` is the base change of `Bl_I X` along
  -- `Spec Γ(X', U') ⟶ X' ⟶ X`, by pasting with the affine chart of `Bl_I X` over `U`.
  have hout := (IsPullback.of_hasPullback (Proj.toSpecCoeff (reesAlgebra.grade (I.ideal ⟨U, hU⟩)))
    (Spec.map (g.appLE U U' e))).paste_horiz (I.isPullback_blowupChart_fromSpec hU).flip
  rw [hsq] at hout
  obtain ⟨b, hbfst, hbsnd⟩ : ∃ b : pullback _ (Spec.map (g.appLE U U' e)) ⟶
      pullback g I.blowupToBase, b ≫ pullback.fst _ _ = pullback.snd _ _ ≫ hU'.fromSpec ∧
        b ≫ pullback.snd _ _ = pullback.fst _ _ ≫ I.blowupChart hU :=
    ⟨pullback.lift _ _ (by simpa only [Category.assoc] using hout.w.symm),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- so it is also the base change of `X' ×_X Bl_I X` along `Spec Γ(X', U') ⟶ X'`.
  have hbot : IsPullback b (pullback.snd _ _) (pullback.fst g I.blowupToBase) hU'.fromSpec :=
    IsPullback.of_right (by rwa [hbsnd]) hbfst (IsPullback.of_hasPullback g I.blowupToBase).flip
  have h₁ : (I.comap g).blowupChart hU' ≫ (I.comap g).blowupToBase =
      c ≫ pullback.snd _ _ ≫ hU'.fromSpec := by
    rw [blowupChart_blowupToBase, reassoc_of% hcs]
  have hcomm : (I.comap g).blowupChart hU' ≫ I.blowupBaseChangeHom g = c ≫ b := by
    refine I.pullback_blowupToBase_hom_ext g (by rw [Category.assoc, Category.assoc,
      blowupBaseChangeHom_fst, hbfst, h₁]) ?_
    rw [Category.assoc, blowupBaseChangeHom_fst_assoc, comap_comp, comap_comp]
    exact (I.comap g).isEffectiveCartier_comap_blowupToBase.comap _
  refine ⟨_, b, c, MorphismProperty.of_isPullback hbot.flip inferInstance, hc,
    IsPullback.of_bot ?_ hcomm hbot, fun p hp ↦ ?_⟩
  · simpa [hcs] using ((I.comap g).isPullback_blowupChart_fromSpec hU').flip
  · rw [← hU'.range_fromSpec, ← Scheme.Pullback.range_fst] at hp
    obtain ⟨q, rfl⟩ := hp
    exact ⟨hbot.isoPullback.inv q, by rw [← Scheme.Hom.comp_apply, hbot.isoPullback_inv_fst]⟩

/-- **The blowup of the inverse image of the centre is a closed subscheme of the base change of
the blowup**: for every morphism `g : X' ⟶ X`, the comparison
`Bl_{I.comap g} X' ⟶ X' ×_X Bl_I X` is a closed immersion. -/
instance isClosedImmersion_blowupBaseChangeHom :
    IsClosedImmersion (I.blowupBaseChangeHom g) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun p ↦ ?_
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (g (pullback.fst g I.blowupToBase p)))
  obtain ⟨U', hU', hpU', hU'U⟩ :=
    exists_isAffineOpen_mem_and_subset ((Scheme.Hom.mem_preimage g).mpr hpU)
  obtain ⟨B, b, c, _, hc, hbc, hb⟩ := I.exists_isPullback_blowupBaseChangeHom g hU hU' hU'U
  refine ⟨b.opensRange,
    Scheme.Hom.mem_opensRange.mpr (Set.mem_range.mp (hb (Set.mem_preimage.mpr hpU'))), ?_⟩
  refine (MorphismProperty.arrow_mk_iso_iff _ (morphismRestrictOpensRange _ b)).mpr ?_
  refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk hbc.isoPullback (Iso.refl _) ?_)).mp hc
  rw [Iso.refl_hom, Category.comp_id]
  exact hbc.isoPullback_hom_snd

/-- **The blowup of a closed subscheme is a closed subscheme of the blowup**: for a closed
immersion `g : X' ⟶ X`, the morphism of blowups `Bl_{I.comap g} X' ⟶ Bl_I X` is a closed
immersion. Its image is the strict transform of `X'` (Stacks Project, Lemma 080E). -/
instance isClosedImmersion_blowupMap [IsClosedImmersion g] :
    IsClosedImmersion (I.blowupMap g) := by
  rw [← blowupBaseChangeHom_snd]
  infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
