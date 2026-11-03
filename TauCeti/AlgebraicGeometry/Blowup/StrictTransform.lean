/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
public import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The strict transform as a scheme-theoretic closure

Let `I` be an ideal sheaf on a scheme `X`, let `b : Bl_I X ⟶ X` be the blowup of `X` along
`V(I)`, and let `g : X' ⟶ X` be a morphism of schemes. The *strict transform* of `X'` is the
scheme-theoretic closure, in the base change `X' ×_X Bl_I X`, of the open part lying over the
complement `X ∖ V(I)` of the centre, that is, of the complement of the inverse image of the
exceptional divisor (Stacks Project, Definition 080D). When `g` is the inclusion of a closed
subscheme `Z`, the base change is the inverse image `b⁻¹(Z)`, and the strict transform is the
scheme-theoretic closure in `Bl_I X` of `b⁻¹(Z) ∖ b⁻¹(V(I))`.

This file proves that the strict transform is the blowup of `X'` along the inverse image of the
centre (Stacks Project, Lemma 080E): the closed immersion
`Bl_{I.comap g} X' ⟶ X' ×_X Bl_I X` of `TauCeti/AlgebraicGeometry/Blowup/Pullback.lean`
(`AlgebraicGeometry.Scheme.IdealSheafData.blowupBaseChangeHom`) has the same kernel as the
inclusion of the open part over `X ∖ V(I)`. Consequently the kernel of the morphism of blowups
`Bl_{I.comap g} X' ⟶ Bl_I X`, which is a closed immersion when `g` is, is the ideal sheaf of the
scheme-theoretic closure of `b⁻¹(Z) ∖ b⁻¹(V(I))` in `Bl_I X`.

The proof compares the two morphisms into `X' ×_X Bl_I X` through factorizations.

* The open part over `X ∖ V(I)` factors through `Bl_{I.comap g} X'`: the centre pulls back to the
  empty closed subscheme on it, which is an effective Cartier divisor, so the universal property
  of the blowup applies.
* Conversely, the restriction of `Bl_{I.comap g} X' ⟶ X' ×_X Bl_I X` to the complement of the
  exceptional divisor factors through the open part over `X ∖ V(I)`, and this complement is
  scheme-theoretically dense, because the exceptional divisor is an effective Cartier divisor
  (`IsEffectiveCartier.isSchemeTheoreticallyDominant_support_compl_ι`).

No finiteness, Noetherianity or flatness hypothesis is needed.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.ker_blowupBaseChangeHom`: the blowup of `X'` along the
  inverse image of the centre is the scheme-theoretic closure, in `X' ×_X Bl_I X`, of the open part
  lying over `X ∖ V(I)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.ker_blowupMap`: the image of `Bl_{I.comap g} X'` in
  `Bl_I X` is the scheme-theoretic closure of the image of that open part.

## References

* [The Stacks Project, Definition 080D](https://stacks.math.columbia.edu/tag/080D): the strict
  transform.
* [The Stacks Project, Lemma 080E](https://stacks.math.columbia.edu/tag/080E): the strict
  transform is the blowup along the inverse image of the centre.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X X' : Scheme.{u}} (I : X.IdealSheafData) (g : X' ⟶ X)

/-- **The strict transform is the blowup along the inverse image of the centre.** The closed
immersion `Bl_{I.comap g} X' ⟶ X' ×_X Bl_I X` has the same kernel as the inclusion of the open
part of `X' ×_X Bl_I X` lying over `X ∖ V(I)`: the blowup of `X'` along the inverse image of the
centre is the scheme-theoretic closure of that open part. -/
theorem ker_blowupBaseChangeHom :
    (I.blowupBaseChangeHom g).ker =
      (Scheme.Opens.ι ((pullback.fst g I.blowupToBase ≫ g) ⁻¹ᵁ I.support.compl)).ker := by
  set W := (pullback.fst g I.blowupToBase ≫ g) ⁻¹ᵁ I.support.compl
  set c := I.blowupBaseChangeHom g
  -- The centre pulls back to the unit ideal sheaf on the open part `W` over `X ∖ V(I)`.
  have hW : (I.comap (W.ι ≫ pullback.fst g I.blowupToBase ≫ g)).IsEffectiveCartier := by
    rw [(comap_eq_top_iff _ _).mpr (by rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self])]
    exact isEffectiveCartier_top _
  have hW' : ((I.comap g).comap (W.ι ≫ pullback.fst g I.blowupToBase)).IsEffectiveCartier := by
    rwa [← comap_comp, Category.assoc]
  refine le_antisymm ?_ ?_
  · -- `W` factors through `Bl_{I.comap g} X'` by the universal property of the blowup.
    let w := (I.comap g).blowupLift (W.ι ≫ pullback.fst g I.blowupToBase) hW'
    have hwfst : w ≫ c ≫ pullback.fst _ _ = W.ι ≫ pullback.fst _ _ := by simp [w, c]
    have hw : w ≫ c = W.ι := by
      refine I.pullback_blowupToBase_hom_ext g (by rwa [Category.assoc]) ?_
      rwa [Category.assoc, reassoc_of% hwfst]
    exact hw ▸ Scheme.Hom.le_ker_comp w c
  · -- The complement of the exceptional divisor of `Bl_{I.comap g} X'` is `c⁻¹(W)`, which is
    -- scheme-theoretically dense and maps into `W`.
    have hcW : c ⁻¹ᵁ W = ((I.comap g).comap (I.comap g).blowupToBase).support.compl := by
      rw [compl_support_comap, compl_support_comap, ← Scheme.Hom.comp_preimage,
        ← Scheme.Hom.comp_preimage]
      simp [c]
    have : IsSchemeTheoreticallyDominant (c ⁻¹ᵁ W).ι := by
      rw [hcW]
      exact (I.comap g).isEffectiveCartier_comap_blowupToBase
        |>.isSchemeTheoreticallyDominant_support_compl_ι
    rw [← Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant (c ⁻¹ᵁ W).ι c,
      ← morphismRestrict_ι]
    exact Scheme.Hom.le_ker_comp _ _

/-- **The strict transform as a scheme-theoretic closure in the blowup.** The morphism of blowups
`Bl_{I.comap g} X' ⟶ Bl_I X` has the same kernel as the open part of `X' ×_X Bl_I X` lying over
`X ∖ V(I)`, mapped to `Bl_I X`. For a closed immersion `g`, the morphism of blowups is a closed
immersion (`isClosedImmersion_blowupMap`), so its image, the blowup of `X'` along the inverse
image of the centre, is the scheme-theoretic closure in `Bl_I X` of `b⁻¹(X') ∖ b⁻¹(V(I))`, the
strict transform of `X'`. -/
theorem ker_blowupMap :
    (I.blowupMap g).ker =
      (Scheme.Opens.ι ((pullback.fst g I.blowupToBase ≫ g) ⁻¹ᵁ I.support.compl) ≫
        pullback.snd g I.blowupToBase).ker := by
  rw [← blowupBaseChangeHom_snd, Scheme.Hom.ker_comp, Scheme.Hom.ker_comp,
    ker_blowupBaseChangeHom]

end AlgebraicGeometry.Scheme.IdealSheafData
