/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import TauCeti.AlgebraicGeometry.Blowup.Restriction
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
public import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Schematic images under admissible blowups

Let `v : V ⟶ W` be quasi-compact, let `p : W ⟶ X`, and let `I` be an ideal sheaf on `X`
whose support misses the image of `v ≫ p`. Inside `W ×[X] Bl_I X`, the schematic image of
the lift of `v` is the strict transform of `v.image`. Equivalently, it is the blowup of
`v.image` along the inverse image of `I`. The comparison is an isomorphism respecting
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

variable {V X : Scheme.{u}} (I : X.IdealSheafData) (f : V ⟶ X)

/-- A quasi-compact schematically dominant morphism avoiding the centre remains
schematically dominant after lifting to the blowup. -/
theorem isSchemeTheoreticallyDominant_blowupLift_of_comap_eq_top
    [QuasiCompact f] [IsSchemeTheoreticallyDominant f] (hf : I.comap f = ⊤) :
    IsSchemeTheoreticallyDominant
      (I.blowupLift f (hf ▸ isEffectiveCartier_top V)) := by
  let U : X.Opens := I.support.compl
  let B := I.blowupToBase ⁻¹ᵁ U
  have hrange : Set.range f ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    have h := (I.comap_eq_top_iff f).mp hf
    exact h.ge (Set.mem_univ v)
  let g := IsOpenImmersion.lift U.ι f hrange
  have hB : IsSchemeTheoreticallyDominant B.ι := by
    dsimp only [B, U]
    rw [← I.compl_support_comap I.blowupToBase]
    exact I.isEffectiveCartier_comap_blowupToBase
      |>.isSchemeTheoreticallyDominant_support_compl_ι
  have heq : g ≫ inv (I.blowupToBase ∣_ U) ≫ B.ι =
      I.blowupLift f (hf ▸ isEffectiveCartier_top V) := by
    apply I.eq_blowupLift
    simp only [Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      IsOpenImmersion.lift_fac]
  rw [← heq]
  infer_instance

variable {W : Scheme.{u}} (p : W ⟶ X) (v : V ⟶ W)

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

variable [QuasiCompact v]

/-- Schematic closure commutes with a blowup away from `v`: inside the base-changed
blowup, the schematic image of a lift is the strict transform of the schematic image. -/
theorem ker_eq_ker_blowupImageι (hv : I.comap (v ≫ p) = ⊤)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    g.ker = (I.blowupImageι p v).ker := by
  -- Lift the schematically dense map to its image; it stays dense on the blowup.
  have hvi : (I.comap (v.imageι ≫ p)).comap v.toImage = ⊤ := by
    rw [← comap_comp, ← Category.assoc, Scheme.Hom.toImage_imageι, hv]
  let l := (I.comap (v.imageι ≫ p)).blowupLift v.toImage (hvi ▸ isEffectiveCartier_top V)
  have : IsSchemeTheoreticallyDominant l :=
    (I.comap (v.imageι ≫ p)).isSchemeTheoreticallyDominant_blowupLift_of_comap_eq_top
      v.toImage hvi
  have hlg : l ≫ I.blowupImageι p v = g := by
    apply pullback.hom_ext
    · simp [l, hg]
    · have hl : (l ≫ I.blowupMap (v.imageι ≫ p)) ≫ I.blowupToBase = v ≫ p := by
        simp [l]
      have hg' : (g ≫ pullback.snd p I.blowupToBase) ≫ I.blowupToBase = v ≫ p := by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, hg]
      rw [Category.assoc, blowupImageι_snd]
      exact (I.eq_blowupLift (hv ▸ isEffectiveCartier_top V) hl).trans
        (I.eq_blowupLift (hv ▸ isEffectiveCartier_top V) hg').symm
  rw [← hlg, Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant]

/-- The schematic image of a lift through a blowup avoiding `v` is canonically
isomorphic to the blowup of the schematic image along the inverse image of the centre. -/
def imageBlowupIso (hv : I.comap (v ≫ p) = ⊤)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    g.image ≅ (I.comap (v.imageι ≫ p)).blowup := by
  let hker : (I.blowupImageι p v).ker = g.imageι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, I.ker_eq_ker_blowupImageι p v hv g hg]
  let l := IsClosedImmersion.lift (I.blowupImageι p v) g.imageι hker.le
  have : IsIso l := IsClosedImmersion.isIso_lift _ _ hker
  exact asIso l

/-- The comparison respects the closed embeddings into the base-changed blowup. -/
@[reassoc (attr := simp)]
theorem imageBlowupIso_hom_blowupImageι (hv : I.comap (v ≫ p) = ⊤)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    (I.imageBlowupIso p v hv g hg).hom ≫ I.blowupImageι p v = g.imageι := by
  dsimp only [imageBlowupIso, asIso]
  exact IsClosedImmersion.lift_fac _ _ _

/-- The inverse comparison also respects the closed embeddings. -/
@[reassoc (attr := simp)]
theorem imageBlowupIso_inv_imageι (hv : I.comap (v ≫ p) = ⊤)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    (I.imageBlowupIso p v hv g hg).inv ≫ g.imageι = I.blowupImageι p v := by
  rw [Iso.inv_comp_eq, imageBlowupIso_hom_blowupImageι]

/-- The comparison identifies the maps from `V` to the original schematic image. -/
@[reassoc (attr := simp)]
theorem toImage_imageBlowupIso_hom_blowupToBase (hv : I.comap (v ≫ p) = ⊤)
    (g : V ⟶ pullback p I.blowupToBase) (hg : g ≫ pullback.fst p I.blowupToBase = v) :
    g.toImage ≫ (I.imageBlowupIso p v hv g hg).hom ≫
      (I.comap (v.imageι ≫ p)).blowupToBase = v.toImage := by
  apply (cancel_mono v.imageι).mp
  simp only [Category.assoc, ← blowupImageι_fst,
    imageBlowupIso_hom_blowupImageι_assoc, Scheme.Hom.toImage_imageι_assoc,
    hg, Scheme.Hom.toImage_imageι]

end AlgebraicGeometry.Scheme.IdealSheafData
