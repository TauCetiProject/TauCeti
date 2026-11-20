/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Strict transforms of scheme-theoretic images

Suppose `W' = W ×_X Bl_I X`. A closed subscheme `Z` of `W` has a strict transform in
`W'`, namely the blowup of `Z` along the inverse image of `I`, embedded in `W'`.
If `v : V ⟶ W'` lies over the complement of the blowup centre and its composite to `W`
is quasi-compact, its scheme-theoretic image in `W'` is the strict transform of its
scheme-theoretic image in `W`. In particular, this identifies schematic graph closures
before and after an admissible blowup on one factor of a fibre product, as needed when
extending maps from open subschemes.

## References

* [The Stacks Project, Lemma 38.33.5](https://stacks.math.columbia.edu/tag/0F3Y).
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X V W W' Z : Scheme.{u}} (I : X.IdealSheafData)

/-- A lift to a blowup is scheme-theoretically dominant if its composite to the base is
quasi-compact and scheme-theoretically dominant. -/
theorem isSchemeTheoreticallyDominant_of_comp_blowupToBase (v : V ⟶ I.blowup)
    [QuasiCompact (v ≫ I.blowupToBase)] [IsSchemeTheoreticallyDominant (v ≫ I.blowupToBase)] :
    IsSchemeTheoreticallyDominant v := by
  let U := I.support.compl
  let b := I.blowupToBase
  have hU : IsSchemeTheoreticallyDominant ((v ≫ b) ∣_ U) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict _ _).flip
  have hiso : IsIso (b ∣_ U) := I.isIso_blowupToBase_restrict_compl_support
  -- Away from the centre the restriction of `v` differs from that of `v ≫ b` by an isomorphism.
  have hV : IsSchemeTheoreticallyDominant (v ∣_ b ⁻¹ᵁ U) := by
    have : IsSchemeTheoreticallyDominant ((v ∣_ b ⁻¹ᵁ U) ≫ (b ∣_ U)) := by
      rw [morphismRestrict_comp] at hU
      exact hU
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
      (inferInstance : IsSchemeTheoreticallyDominant
        (((v ∣_ b ⁻¹ᵁ U) ≫ (b ∣_ U)) ≫ inv (b ∣_ U)))
  -- This open is scheme-theoretically dense because the exceptional ideal is Cartier.
  have hD : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ U).ι := by
    rw [← compl_support_comap]
    exact I.isEffectiveCartier_comap_blowupToBase.isSchemeTheoreticallyDominant_support_compl_ι
  have hcomp : IsSchemeTheoreticallyDominant ((v ⁻¹ᵁ b ⁻¹ᵁ U).ι ≫ v) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact IsSchemeTheoreticallyDominant.of_comp (v ⁻¹ᵁ b ⁻¹ᵁ U).ι v

variable {p : W' ⟶ W} {b : W' ⟶ I.blowup} {f : W ⟶ X}

/-- The map from the blowup of `Z` along the centre pulled back through `g ≫ f` into
`W' = W ×_X Bl_I X`. For a closed immersion `g`, this embeds the strict transform in `W'`. -/
def blowupMapToPullback (h : IsPullback p b f I.blowupToBase) (g : Z ⟶ W) :
    (I.comap (g ≫ f)).blowup ⟶ W' :=
  h.lift ((I.comap (g ≫ f)).blowupToBase ≫ g) (I.blowupMap (g ≫ f)) (by simp)

/-- The first projection of the comparison is the blowup projection followed by `g`. -/
@[reassoc (attr := simp)]
theorem blowupMapToPullback_fst (h : IsPullback p b f I.blowupToBase) (g : Z ⟶ W) :
    I.blowupMapToPullback h g ≫ p = (I.comap (g ≫ f)).blowupToBase ≫ g :=
  h.lift_fst _ _ _

/-- The second projection of the comparison is the induced morphism of blowups. -/
@[reassoc (attr := simp)]
theorem blowupMapToPullback_snd (h : IsPullback p b f I.blowupToBase) (g : Z ⟶ W) :
    I.blowupMapToPullback h g ≫ b = I.blowupMap (g ≫ f) :=
  h.lift_snd _ _ _

/-- The strict transform of a closed subscheme of `W` is closed in `W ×_X Bl_I X`. -/
theorem isClosedImmersion_blowupMapToPullback (h : IsPullback p b f I.blowupToBase)
    (g : Z ⟶ W) [IsClosedImmersion g] : IsClosedImmersion (I.blowupMapToPullback h g) := by
  let k := (IsPullback.of_hasPullback g p).paste_vert h
  have hk : I.blowupMapToPullback h g = I.blowupBaseChangeHom (g ≫ f) ≫
      k.isoPullback.inv ≫ pullback.snd g p := by
    apply h.hom_ext
    · simp only [blowupMapToPullback_fst, Category.assoc, ← pullback.condition,
        k.isoPullback_inv_fst_assoc, blowupBaseChangeHom_fst_assoc]
    · rw [blowupMapToPullback_snd, ← I.blowupBaseChangeHom_snd]
      simp only [Category.assoc, k.isoPullback_inv_snd]
  rw [hk]
  infer_instance

/-- In a base change of a blowup, the schematic image of `v` is the strict transform of
its schematic image downstairs. It suffices that the centre pull back to an effective
Cartier divisor on the source of `v`; in particular this holds when `v` lies over the
complement of the centre. -/
theorem ker_blowupMapToPullback_imageι (h : IsPullback p b f I.blowupToBase) (v : V ⟶ W')
    [QuasiCompact (v ≫ p)] (hv : (I.comap ((v ≫ p) ≫ f)).IsEffectiveCartier) :
    (I.blowupMapToPullback h (v ≫ p).imageι).ker = v.ker := by
  let g := v ≫ p
  let J := I.comap (g.imageι ≫ f)
  have ht : (J.comap g.toImage).IsEffectiveCartier := by
    simpa only [J, ← comap_comp, Scheme.Hom.toImage_imageι_assoc] using hv
  -- The image factorization lifts to the blowup of the schematic image downstairs.
  let t := J.blowupLift g.toImage ht
  have ht' : t ≫ J.blowupToBase = g.toImage := J.blowupLift_blowupToBase _ _
  have hq : QuasiCompact (t ≫ J.blowupToBase) := ht' ▸ inferInstanceAs (QuasiCompact g.toImage)
  have hd : IsSchemeTheoreticallyDominant (t ≫ J.blowupToBase) :=
    ht' ▸ inferInstanceAs (IsSchemeTheoreticallyDominant g.toImage)
  have htD : IsSchemeTheoreticallyDominant t :=
    J.isSchemeTheoreticallyDominant_of_comp_blowupToBase t
  have he : t ≫ I.blowupMapToPullback h g.imageι = v := by
    apply h.hom_ext
    · rw [Category.assoc, blowupMapToPullback_fst, ← Category.assoc, ht',
        Scheme.Hom.toImage_imageι]
    · have hv' : (I.comap (g.toImage ≫ g.imageι ≫ f)).IsEffectiveCartier := by
        simpa only [Scheme.Hom.toImage_imageι_assoc] using hv
      rw [Category.assoc, blowupMapToPullback_snd, blowupLift_blowupMap _ _ _ _ hv']
      exact (I.eq_blowupLift hv' (by simp only [Scheme.Hom.toImage_imageι_assoc, g,
        Category.assoc, h.w])).symm
  exact (Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant t _).symm.trans
    (congrArg Scheme.Hom.ker he)

/-- The blowup of the schematic image downstairs identifies with the schematic image upstairs,
with the identification over `W'` given by `blowupSchematicImageIso_hom_imageι`. -/
def blowupSchematicImageIso (h : IsPullback p b f I.blowupToBase) (v : V ⟶ W')
    [QuasiCompact (v ≫ p)] (hv : (I.comap ((v ≫ p) ≫ f)).IsEffectiveCartier) :
    (I.comap ((v ≫ p).imageι ≫ f)).blowup ≅ v.image := by
  have := I.isClosedImmersion_blowupMapToPullback h (v ≫ p).imageι
  have e : v.imageι.ker = (I.blowupMapToPullback h (v ≫ p).imageι).ker :=
    (IdealSheafData.ker_subschemeι _).trans (I.ker_blowupMapToPullback_imageι h v hv).symm
  have := IsClosedImmersion.isIso_lift _ _ e
  exact asIso (IsClosedImmersion.lift _ _ e.le)

/-- The isomorphism to the schematic image upstairs respects its embedding. -/
@[reassoc (attr := simp)]
theorem blowupSchematicImageIso_hom_imageι (h : IsPullback p b f I.blowupToBase) (v : V ⟶ W')
    [QuasiCompact (v ≫ p)] (hv : (I.comap ((v ≫ p) ≫ f)).IsEffectiveCartier) :
    (I.blowupSchematicImageIso h v hv).hom ≫ v.imageι =
      I.blowupMapToPullback h (v ≫ p).imageι := by
  simp only [blowupSchematicImageIso, asIso_hom, IsClosedImmersion.lift_fac]

/-- The inverse isomorphism to the strict transform respects its embedding. -/
@[reassoc (attr := simp)]
theorem blowupSchematicImageIso_inv_blowupMapToPullback
    (h : IsPullback p b f I.blowupToBase) (v : V ⟶ W')
    [QuasiCompact (v ≫ p)] (hv : (I.comap ((v ≫ p) ≫ f)).IsEffectiveCartier) :
    (I.blowupSchematicImageIso h v hv).inv ≫ I.blowupMapToPullback h (v ≫ p).imageι = v.imageι := by
  rw [Iso.inv_comp_eq, blowupSchematicImageIso_hom_imageι]

end AlgebraicGeometry.Scheme.IdealSheafData
