/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.FamilyLinearAction
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction

/-!
# Universal projective translation of a Hopf comodule

A comodule over a flat commutative Hopf `R`-algebra `H` gives a universal projective
translation on `Proj(Sym_R M) ×_{Spec R} Spec H`. It is an isomorphism fixing the
`Spec H` coordinate; projecting its output to projective space gives the family morphism.
The inverse comes from the inverse of the universal point `id : H →ₐ[R] H`, hence
from the antipode. This is a scheme construction, valid also for nonreduced groups.

The module `M` consists of homogeneous linear coordinates. For the projective space
of lines in a finite projective representation `V`, use the dual comodule `M = V∨`.
Inverse pullback then gives translation by the original representation on `V`.
No finite-type, smoothness, or characteristic assumption is imposed. Flatness of `H`
is automatic over a field and is used only in the projective base-change comparison.

The construction uses `Comodule.pointsAction` and
`Proj.symmetricAlgebraFamilyAut`. It supplies the universal family of translations;
compatibility with change of parameter algebra and the scheme action diagrams are
separate from the fixed-parameter group laws proved by the bundled homomorphism here.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f, projective actions and homogeneous spaces.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2, actions of algebra-valued points.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WithConv
open TauCeti.SymmetricAlgebra
open scoped TensorProduct

namespace TauCeti.Comodule

universe u

variable (R H M : Type u) [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]

section Parameter

variable (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S]

/-- Algebra-valued group points act by projective automorphisms of the scheme fiber product,
with the parameter algebra fixed. -/
noncomputable def projectivePointsAction :
    WithConv (H →ₐ[R] S) →*
      Aut (pullback (Proj.toSpecCoeff (homogeneousSubmodule R M))
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :=
  (Proj.symmetricAlgebraFamilyAut R S M).comp (pointsAction M)

/-- The projective point action is transport of inverse pullback by the scalar-extended
linear point action. -/
theorem projectivePointsAction_apply (g : WithConv (H →ₐ[R] S)) :
    projectivePointsAction R H M S g =
      (Proj.symmetricAlgebraBaseChangeIso R S M).symm ≪≫
        Proj.symmetricAlgebraMapIso S (pointsAction M g).symm ≪≫
          Proj.symmetricAlgebraBaseChangeIso R S M := by
  rw [projectivePointsAction, MonoidHom.comp_apply, Proj.symmetricAlgebraFamilyAut_apply]

/-- Projective translation fixes the parameter projection, including on the structure sheaf. -/
@[reassoc (attr := simp)]
theorem projectivePointsAction_hom_snd (g : WithConv (H →ₐ[R] S)) :
    (projectivePointsAction R H M S g).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  exact Proj.symmetricAlgebraFamilyAut_hom_snd R S M (pointsAction M g)

end Parameter

variable [Module.Flat R H]

/-- The universal translation `(x, g) ↦ (g · x, g)` on the projective-space/group fiber
product, obtained from the universal `H`-valued point. -/
noncomputable def projectiveUniversalTranslation :
    pullback (Proj.toSpecCoeff (homogeneousSubmodule R M))
        (Spec.map (CommRingCat.ofHom (algebraMap R H))) ≅
      pullback (Proj.toSpecCoeff (homogeneousSubmodule R M))
        (Spec.map (CommRingCat.ofHom (algebraMap R H))) :=
  projectivePointsAction R H M H (toConv (AlgHom.id R H))

/-- Universal translation is the projective action of the identity algebra homomorphism. -/
theorem projectiveUniversalTranslation_def :
    projectiveUniversalTranslation R H M =
      projectivePointsAction R H M H (toConv (AlgHom.id R H)) := (rfl)

/-- The inverse universal translation is translation by the convolution inverse of the
universal point, whose coordinate map is the antipode. -/
@[simp]
theorem projectiveUniversalTranslation_symm :
    (projectiveUniversalTranslation R H M).symm =
      projectivePointsAction R H M H ((toConv (AlgHom.id R H))⁻¹) := by
  exact (map_inv (projectivePointsAction R H M H) (toConv (AlgHom.id R H))).symm

/-- Universal translation preserves the group coordinate as a scheme morphism. -/
@[reassoc (attr := simp)]
theorem projectiveUniversalTranslation_hom_snd :
    (projectiveUniversalTranslation R H M).hom ≫ pullback.snd _ _ = pullback.snd _ _ :=
  projectivePointsAction_hom_snd R H M H _

/-- Universal inverse translation also preserves the group coordinate. -/
@[reassoc (attr := simp)]
theorem projectiveUniversalTranslation_inv_snd :
    (projectiveUniversalTranslation R H M).inv ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [← Iso.symm_hom, projectiveUniversalTranslation_symm]
  exact projectivePointsAction_hom_snd R H M H _

/-- The morphism from the projective-space/group fiber product to projective space obtained
by universal translation and projection. -/
noncomputable def projectiveTranslationMap :
    pullback (Proj.toSpecCoeff (homogeneousSubmodule R M))
        (Spec.map (CommRingCat.ofHom (algebraMap R H))) ⟶
      Proj (homogeneousSubmodule R M) :=
  (projectiveUniversalTranslation R H M).hom ≫ pullback.fst _ _

/-- The translation morphism is the first projection after universal translation. -/
theorem projectiveTranslationMap_def :
    projectiveTranslationMap R H M =
      (projectiveUniversalTranslation R H M).hom ≫ pullback.fst _ _ := (rfl)

/-- The universal translation morphism lies over the original base ring. -/
@[reassoc (attr := simp)]
theorem projectiveTranslationMap_toSpecCoeff :
    projectiveTranslationMap R H M ≫ Proj.toSpecCoeff (homogeneousSubmodule R M) =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R H)) := by
  rw [projectiveTranslationMap_def, Category.assoc, pullback.condition,
    projectiveUniversalTranslation_hom_snd_assoc]

end TauCeti.Comodule
