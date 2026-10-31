/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
public import TauCeti.RingTheory.ReesAlgebra.BaseChange

/-!
# Blowing up affine schemes commutes with flat base change

Let `I` be an ideal of a commutative ring `R` and let `S` be an `R`-algebra, with extended ideal
`IS = I.map (algebraMap R S)`. The blowup of `Spec R` along `V(I)` is `Proj R[It]`, with structure
morphism `Proj.toSpecCoeff` to `Spec R`. The base change of the Rees algebra
(`reesAlgebra.baseChangeGradedAlgHom`) is a surjective graded homomorphism
`S ⊗[R] R[It] ⟶ S[(IS)t]`, and `Proj` commutes with arbitrary extension of the coefficient ring
(`AlgebraicGeometry.Proj.baseChangeIso`). Together they give a comparison morphism over `Spec S`

`Proj S[(IS)t] ⟶ Spec S ×_{Spec R} Proj R[It]`

from the blowup of `Spec S` along the inverse image `V(IS)` of the centre to the base change of
the blowup of `Spec R`. It is always a closed immersion, and it is an isomorphism when `S` is flat
over `R`: then the blowup of `Spec S` along `V(IS)` is the base change of the blowup of `Spec R`
along `V(I)`. In particular blowing up commutes with localizations `R ⟶ R_f` and with étale
`R`-algebras.

## Main definitions

* `TauCeti.AlgebraicGeometry.affineBlowupBaseChangeHom I S`: the comparison morphism from the
  blowup of `Spec S` along `V(IS)` to the base change of the blowup of `Spec R` along `V(I)`.

## Main results

* `TauCeti.AlgebraicGeometry.toSpecCoeff_reesAlgebra`: the coefficient structure morphism of the
  blowup is the structure morphism to the spectrum of the degree zero part `R`.
* `TauCeti.AlgebraicGeometry.affineBlowupBaseChangeHom_snd`: the comparison lies over `Spec S`.
* `TauCeti.AlgebraicGeometry.isClosedImmersion_affineBlowupBaseChangeHom`: the comparison is a
  closed immersion.
* `TauCeti.AlgebraicGeometry.isIso_affineBlowupBaseChangeHom`: for flat `S`, it is an isomorphism.
* `TauCeti.AlgebraicGeometry.isPullback_affineBlowup_of_flat`: for flat `S`, the square formed by
  the two blowups over `Spec S ⟶ Spec R` is cartesian.

## References

* [The Stacks Project, Section *Blowing up*](https://stacks.math.columbia.edu/tag/01OF), the
  lemma comparing the blowup of the inverse image of the centre with the base change of the
  blowup: it is a closed subscheme, equal to it after flat base change.
-/

public section

open CategoryTheory CategoryTheory.Limits reesAlgebra

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] (I : Ideal R) (S : Type u) [CommRing S] [Algebra R S]

/-- The coefficient structure morphism `Proj R[It] ⟶ Spec R` of the blowup is the structure
morphism to the spectrum of the degree zero part of `R[It]`, identified with `R` by
`reesAlgebra.gradeZeroEquiv`. -/
theorem toSpecCoeff_reesAlgebra :
    Proj.toSpecCoeff (grade I) =
      Proj.toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom := by
  have h : (gradeZeroEquiv I : R →+* grade I 0) = algebraMap R (grade I 0) :=
    RingHom.ext (gradeZeroEquiv_apply I)
  rw [Proj.toSpecCoeff_def, RingEquiv.toCommRingCatIso_hom, h]

/-- **The comparison of blowups under base change.** The morphism from the blowup `Proj S[(IS)t]`
of `Spec S` along `V(IS)` to the base change `Spec S ×_{Spec R} Proj R[It]` of the blowup of
`Spec R` along `V(I)`, induced by the base change `S ⊗[R] R[It] ⟶ S[(IS)t]` of Rees algebras.
It is a closed immersion (`isClosedImmersion_affineBlowupBaseChangeHom`), and an isomorphism for
flat `S` (`isIso_affineBlowupBaseChangeHom`). -/
noncomputable def affineBlowupBaseChangeHom :
    Proj (grade (I.map (algebraMap R S))) ⟶
      pullback (Proj.toSpecCoeff (grade I)) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  Proj.map (baseChangeGradedAlgHom I S).toGradedRingHom
      (HomogeneousIdeal.irrelevant_le_map_of_surjective _
        (baseChangeGradedAlgHom_surjective I S)) ≫
    (Proj.baseChangeIso (grade I) S).hom

/-- The projection of the comparison to the blowup of `Spec R` is the morphism of projective
spectra induced by the base change of Rees algebras, followed by the coefficient projection. -/
@[reassoc (attr := simp)]
theorem affineBlowupBaseChangeHom_fst :
    affineBlowupBaseChangeHom I S ≫ pullback.fst _ _ =
      Proj.map (baseChangeGradedAlgHom I S).toGradedRingHom
          (HomogeneousIdeal.irrelevant_le_map_of_surjective _
        (baseChangeGradedAlgHom_surjective I S)) ≫
        Proj.baseChangeProjection (grade I) S := by
  simp [affineBlowupBaseChangeHom]

/-- The comparison of blowups is a morphism over `Spec S`. -/
@[reassoc (attr := simp)]
theorem affineBlowupBaseChangeHom_snd :
    affineBlowupBaseChangeHom I S ≫ pullback.snd _ _ =
      Proj.toSpecCoeff (grade (I.map (algebraMap R S))) := by
  rw [affineBlowupBaseChangeHom, Category.assoc, Proj.baseChangeIso_hom_snd]
  refine Proj.map_toSpecCoeff _ _ _ fun s ↦ Subtype.ext ?_
  simpa using (baseChangeHom I S).commutes s

/-- **The blowup of the inverse image of the centre is a closed subscheme of the base change of
the blowup**: the comparison `Proj S[(IS)t] ⟶ Spec S ×_{Spec R} Proj R[It]` is a closed
immersion, for every `R`-algebra `S`. -/
instance isClosedImmersion_affineBlowupBaseChangeHom :
    IsClosedImmersion (affineBlowupBaseChangeHom I S) := by
  have := Proj.isClosedImmersion_map (baseChangeGradedAlgHom I S).toGradedRingHom
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _
        (baseChangeGradedAlgHom_surjective I S))
    (baseChangeGradedAlgHom_surjective I S)
  rw [affineBlowupBaseChangeHom]
  infer_instance

/-- **Blowing up commutes with flat base change**: for flat `S`, the comparison
`Proj S[(IS)t] ⟶ Spec S ×_{Spec R} Proj R[It]` is an isomorphism. -/
instance isIso_affineBlowupBaseChangeHom [Module.Flat R S] :
    IsIso (affineBlowupBaseChangeHom I S) := by
  have := (Proj.mapIso (baseChangeGradedAlgHom I S).toGradedRingHom
    (baseChangeGradedAlgHomSymm I S).toGradedRingHom
    (baseChangeGradedAlgHom_rightInverse I S) (baseChangeGradedAlgHom_leftInverse I S)).isIso_hom
  rw [Proj.mapIso_hom] at this
  rw [affineBlowupBaseChangeHom]
  infer_instance

/-- **The blowup of `Spec S` along `V(IS)` is the base change of the blowup of `Spec R` along
`V(I)`**, for flat `S`: the square formed by the projection of the comparison to `Proj R[It]`
and the structure morphisms of the two blowups over `Spec S ⟶ Spec R` is cartesian. -/
theorem isPullback_affineBlowup_of_flat [Module.Flat R S] :
    IsPullback (affineBlowupBaseChangeHom I S ≫ pullback.fst _ _)
      (Proj.toSpecCoeff (grade (I.map (algebraMap R S)))) (Proj.toSpecCoeff (grade I))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (affineBlowupBaseChangeHom I S)) rfl
    (affineBlowupBaseChangeHom_snd I S)
  rw [← affineBlowupBaseChangeHom_snd, Category.assoc, Category.assoc, pullback.condition]

end TauCeti.AlgebraicGeometry
