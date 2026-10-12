/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Basic
public import TauCeti.AlgebraicGeometry.Curves.SingularLocus
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import TauCeti.RingTheory.Node.Jacobian.Locus

/-!
# The singular subscheme of a node chart

For every commutative ring `R` and smoothing parameter `a : R`, the relative singular
subscheme of `Spec R[x,y]/(xy-a)` is canonically `Spec R/(a)` over `Spec R`.
In particular its structure morphism is a closed immersion and is unramified. This
supplies the singular-locus condition in the scheme-theoretic criterion for nodal curves.
The identification retains the scheme structure even when `a` is nilpotent or a zero divisor.

The relative singular locus is cut out by the two coordinates `x` and `y`
(`NodeAlgebra.singularLocus_ideal_top`). The construction uses the first Fitting ideal
of the relative differentials and the algebraic identification `NodeAlgebra.jacobianQuotientEquiv`.

## References

* [Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58).
* [Stacks Project, Example 55.14.1, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti.NodeAlgebra

universe u

variable {R : Type u} [CommRing R] (a : R)

/-- The direct structure morphism on the node chart, used to avoid the `Spec`-over-`Spec`
instance diamond when applying the singular-locus API. -/
local instance (priority := high) nodeSpecOverSpec :
    (Spec (.of (NodeAlgebra R a))).Over (Spec (.of R)) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))

local instance : Flat (Spec (.of (NodeAlgebra R a)) ↘ Spec (.of R)) :=
  flat_spec a

local instance :
    LocallyOfFinitePresentation (Spec (.of (NodeAlgebra R a)) ↘ Spec (.of R)) :=
  locallyOfFinitePresentation_spec a

local instance :
    PureRelativeDimension 1 (Spec (.of (NodeAlgebra R a)) ↘ Spec (.of R)) :=
  pureRelativeDimension_spec a

/-- The relative singular locus of the local model of a node `Spec R[x, y] ⧸ (xy - a)` over `R`
is cut out by the ideal `(x, y)` of the two coordinates. -/
theorem singularLocus_ideal_top :
    ((Spec (.of (NodeAlgebra R a))).singularLocus R).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {coord a 0, coord a 1}).map
        (Scheme.ΓSpecIso (.of (NodeAlgebra R a))).inv.hom := by
  rw [Scheme.singularLocus_ideal_top_Spec, fittingIdeal_differential_one]

private abbrev singularIdeal := (Spec (.of (NodeAlgebra R a))).singularLocus R

private abbrev topAffine : (Spec (.of (NodeAlgebra R a))).affineOpens :=
  ⟨⊤, isAffineOpen_top _⟩

private instance : IsAffine (singularIdeal a).subscheme :=
  isAffine_of_isAffineHom (singularIdeal a).subschemeι

private def singularSectionsIso :
    Γ((singularIdeal a).subscheme, ⊤) ≅
      CommRingCat.of (Γ(Spec (.of (NodeAlgebra R a)), ⊤) ⧸
        (singularIdeal a).ideal (topAffine a)) := by
  simpa only [topAffine, TopologicalSpace.Opens.map_top] using
    (singularIdeal a).subschemeObjIso (topAffine a)

private lemma singularSectionsIso_hom_comp :
    (singularIdeal a).subschemeι.appTop ≫ (singularSectionsIso a).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk ((singularIdeal a).ideal (topAffine a))) := by
  -- `appTop` and `subschemeObjIso` use the canonically equal opens `⊤` and `ι ⁻¹ᵁ ⊤`.
  -- `erw` unfolds the presheaf object at this equality of opens.
  dsimp only [singularSectionsIso, Scheme.Hom.appTop]
  erw [(singularIdeal a).subschemeι_app (topAffine a)]
  dsimp only [id]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def singularQuotientEquiv :
    (Γ(Spec (.of (NodeAlgebra R a)), ⊤) ⧸ (singularIdeal a).ideal (topAffine a)) ≃+*
      R ⧸ Ideal.span {a} :=
  (Ideal.quotientEquiv (fittingIdeal (NodeAlgebra R a) Ω[NodeAlgebra R a⁄R] 1)
    ((singularIdeal a).ideal (topAffine a))
    (Scheme.ΓSpecIso (.of (NodeAlgebra R a))).symm.commRingCatIsoToRingEquiv
    (by simpa only [RingEquiv.toRingHom_eq_coe,
      Iso.commRingCatIsoToRingEquiv_toRingHom, Iso.symm_hom] using
      (by rw [fittingIdeal_differential_one]; exact singularLocus_ideal_top a))).symm.trans
    (differentialFittingQuotientEquiv a).toRingEquiv

/-- The relative singular subscheme of the node chart `xy = a` is `Spec R/(a)`. -/
def singularLocusIso :
    ((Spec (.of (NodeAlgebra R a))).singularLocus R).subscheme ≅
      Spec (.of (R ⧸ Ideal.span {a})) :=
  (singularIdeal a).subscheme.isoSpec ≪≫
    Scheme.Spec.mapIso ((singularSectionsIso a) ≪≫
      (singularQuotientEquiv a).toCommRingCatIso).symm.op

/-- The singular-locus identification is an isomorphism over `Spec R`. -/
@[reassoc (attr := simp)]
theorem singularLocusIso_inv_comp :
    (singularLocusIso a).inv ≫
      ((Spec (.of (NodeAlgebra R a))).singularLocus R).subschemeι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) := by
  simp only [singularLocusIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
    Iso.symm_inv, Iso.trans_hom, Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
  simp only [singularIdeal]
  rw [← Scheme.isoSpec_inv_naturality_assoc
    ((Spec (.of (NodeAlgebra R a))).singularLocus R).subschemeι]
  simp only [Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Category.assoc]
  congr 1
  rw [Category.assoc _ ((singularIdeal a).subschemeι.appTop),
    singularSectionsIso_hom_comp]
  ext r
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, RingEquiv.toCommRingCatIso_hom,
    CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom, singularQuotientEquiv,
    RingEquiv.trans_apply, Ideal.quotientEquiv_symm_mk]
  rw [← Iso.symm_hom (Scheme.ΓSpecIso (.of (NodeAlgebra R a))),
    ← Iso.commRingCatIsoToRingEquiv_toRingHom]
  simp only [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  exact (congrArg (differentialFittingQuotientEquiv a)
    (differentialFittingQuotientEquiv_symm_mk a r).symm).trans
      ((differentialFittingQuotientEquiv a).apply_symm_apply _)

/-- The forward singular-locus identification commutes with the maps to `Spec R`. -/
@[reassoc (attr := simp)]
theorem singularLocusIso_hom_comp :
    (singularLocusIso a).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) =
      ((Spec (.of (NodeAlgebra R a))).singularLocus R).subschemeι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a))) := by
  rw [← singularLocusIso_inv_comp a, Iso.hom_inv_id_assoc]

/-- The singular subscheme of `xy = a` maps to `Spec R` by a closed immersion.
Consequently it is unramified over `R`, as required by the nodal-curve criterion. -/
instance isClosedImmersion_singularLocus :
    IsClosedImmersion
      (((Spec (.of (NodeAlgebra R a))).singularLocus R).subschemeι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (singularLocusIso a).inv, singularLocusIso_inv_comp]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

end TauCeti.NodeAlgebra
