/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Schematic images under admissible blowups

Let `v : V ⟶ W` be quasi-compact, let `p : W ⟶ X`, and let `I` be an ideal sheaf on `X`
whose pullback along `v ≫ p` is an effective Cartier divisor. Inside `W ×[X] Bl_I X`,
the schematic image of the lift of `v` is the strict transform of `v.image`. Equivalently, it is the
blowup of `v.image` along the inverse image of `I`. The comparison is an isomorphism respecting
the closed embeddings into the base-changed blowup and the maps to the original image.

This applies in particular to the closure of a subscheme of a product when one factor is
blown up away from that subscheme. It permits carrying schematic closures through the
blowups used to enlarge and glue compactifications, without reducedness or Noetherianity.

## References

* The Stacks Project, Lemma 38.33.5 (Tag 0F3Y).
* The Stacks Project, Lemma 31.34.2 (Tag 080E), identifying strict transforms with blowups.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {V W X : Scheme.{u}} (I : X.IdealSheafData) (p : W ⟶ X) (v : V ⟶ W)

/-- The strict transform of the schematic image of `v`, embedded in the base change
of the blowup along `p`. -/
def blowupImageι : (I.comap (v.imageι ≫ p)).blowup ⟶ pullback p I.blowupToBase :=
  I.blowupBaseChangeHom (v.imageι ≫ p) ≫
    pullback.map (v.imageι ≫ p) I.blowupToBase p I.blowupToBase
      v.imageι (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem blowupImageι_fst :
    I.blowupImageι p v ≫ pullback.fst p I.blowupToBase =
      (I.comap (v.imageι ≫ p)).blowupToBase ≫ v.imageι := by
  simp [blowupImageι]

@[reassoc (attr := simp)]
theorem blowupImageι_snd :
    I.blowupImageι p v ≫ pullback.snd p I.blowupToBase = I.blowupMap (v.imageι ≫ p) := by
  simp [blowupImageι]

/-- The strict transform of a schematic image is closed in the base-changed blowup. -/
instance isClosedImmersion_blowupImageι : IsClosedImmersion (I.blowupImageι p v) := by
  -- Instance search does not reach composition stability through IsMultiplicative here.
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : IsClosedImmersion (pullback.map (v.imageι ≫ p) I.blowupToBase p I.blowupToBase
      v.imageι (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance
      rfl (by simp)
  dsimp only [blowupImageι]
  infer_instance

/-- The canonical lift to the blowup of the schematic image factors any lift of `v`
through the strict-transform embedding. -/
@[reassoc]
theorem blowupLift_toImage_blowupImageι (hv : (I.comap (v ≫ p)).IsEffectiveCartier)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    (I.comap (v.imageι ≫ p)).blowupLift v.toImage (by simpa using hv) ≫
      I.blowupImageι p v = g := by
  refine I.pullback_blowupToBase_hom_ext p (by simp [hg]) ?_
  simpa using hv

variable [QuasiCompact v]

/-- When the pulled-back centre is effective Cartier, the schematic image of a lift is the strict
transform of the original schematic image. -/
theorem ker_eq_ker_blowupImageι (hv : (I.comap (v ≫ p)).IsEffectiveCartier)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    g.ker = (I.blowupImageι p v).ker := by
  -- Lift the schematically dense map to its image; it stays dense on the blowup.
  let l := (I.comap (v.imageι ≫ p)).blowupLift v.toImage (by simpa using hv)
  have : IsSchemeTheoreticallyDominant l :=
    (I.comap (v.imageι ≫ p)).isSchemeTheoreticallyDominant_blowupLift v.toImage _
  have hlg : l ≫ I.blowupImageι p v = g :=
    I.blowupLift_toImage_blowupImageι p v hv g hg
  rw [← hlg, Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant]

/-- The schematic image of a lift through the blowup is canonically
isomorphic to the blowup of the schematic image along the inverse image of the centre. -/
def imageBlowupIso (hv : (I.comap (v ≫ p)).IsEffectiveCartier)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    g.image ≅ (I.comap (v.imageι ≫ p)).blowup :=
  have hker : (I.blowupImageι p v).ker = g.imageι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, I.ker_eq_ker_blowupImageι p v hv g hg]
  haveI := IsClosedImmersion.isIso_lift _ _ hker
  asIso (IsClosedImmersion.lift (I.blowupImageι p v) g.imageι hker.le)

/-- The comparison respects the closed embeddings into the base-changed blowup. -/
@[reassoc (attr := simp)]
theorem imageBlowupIso_hom_blowupImageι (hv : (I.comap (v ≫ p)).IsEffectiveCartier)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    (I.imageBlowupIso p v hv g hg).hom ≫ I.blowupImageι p v = g.imageι := by
  simp only [imageBlowupIso, asIso_hom, IsClosedImmersion.lift_fac]

/-- The inverse comparison also respects the closed embeddings. -/
@[reassoc (attr := simp)]
theorem imageBlowupIso_inv_imageι (hv : (I.comap (v ≫ p)).IsEffectiveCartier)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    (I.imageBlowupIso p v hv g hg).inv ≫ g.imageι = I.blowupImageι p v := by
  rw [Iso.inv_comp_eq, imageBlowupIso_hom_blowupImageι]

/-- The comparison carries the map from `V` to its schematic image to the canonical
lift into the blowup of the original schematic image. -/
@[reassoc (attr := simp)]
theorem toImage_imageBlowupIso_hom (hv : (I.comap (v ≫ p)).IsEffectiveCartier)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    g.toImage ≫ (I.imageBlowupIso p v hv g hg).hom =
      (I.comap (v.imageι ≫ p)).blowupLift v.toImage (by simpa using hv) := by
  apply (cancel_mono (I.blowupImageι p v)).mp
  rw [Category.assoc, imageBlowupIso_hom_blowupImageι, Scheme.Hom.toImage_imageι,
    blowupLift_toImage_blowupImageι I p v hv g hg]

end AlgebraicGeometry.Scheme.IdealSheafData
