/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Unit
public import TauCeti.AlgebraicGeometry.RelativeSpec.Counit

/-!
# The relative-Spec anti-equivalence

Quasi-coherent commutative algebras on a scheme correspond contravariantly to schemes affine
over it. The functors are `relativeSpec` and `affineFunctions`, the latter taking the actual
pushforward of the structure sheaf. The unit identifies an algebra with functions on its
relative spectrum; the counit recovers an affine morphism from its function algebra.

The triangle identities make these recovery isomorphisms compatible with both functors.
The anti-equivalence allows questions about affine schemes over the base to be translated into
questions about quasi-coherent commutative algebras, with the direction of morphisms reversed.

## References

* The Stacks Project, Tag 01LQ (relative spectrum as a functor).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.3.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

noncomputable section

namespace CategoryTheory.CommMon

variable {X : Scheme.{u}} (A : CommMon X.Modules) [A.X.IsQuasicoherent]

/-- On an affine open, the unit on section rings, preceded by the inverse identification of
pushforward sections, is the usual map of functions along the relative-spectrum chart. -/
private lemma sections_relativeSpecPushforwardIso (U : X.AffineZariskiSite) :
    A.relativeSpecToBase.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1) ≫
        CommRingCat.ofHom (sectionsAlgHom A.relativeSpecPushforwardIso.hom U.1).toRingHom =
      (A.relativeSpecCover.f U).appLE _ ⊤ (A.top_le_preimage_relativeSpecToBase U) ≫
        (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, U.1))).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  rw [Scheme.Hom.pushforwardStructureAlgebraPresheafIso_inv_app]
  -- Section-ring objects and presheaf components have different bundled presentations.
  -- Evaluation identifies their coercions before using the public chart formula.
  change sectionsAlgHom A.relativeSpecPushforwardIso.hom U.1
      ((A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv U.1).symm x) = _
  rw [sectionsAlgHom_relativeSpecPushforwardIso_hom_apply,
    relativeSpecCoverFunctionAlgebraSectionsRingEquiv_apply, RingEquiv.apply_symm_apply]
  rfl

/-- Applying relative Spec to the algebra-side unit and then recovering the scheme gives the
identity on the relative spectrum. -/
@[reassoc (attr := simp)]
lemma relativeSpecMap_relativeSpecPushforwardIso_hom_comp :
    relativeSpecMap A.relativeSpecPushforwardIso.hom ≫
        A.relativeSpecToBase.relativeSpecFunctionsToScheme = 𝟙 A.relativeSpec := by
  apply A.relativeSpec_hom_ext
  intro U
  let ι : Spec (CommRingCat.of Γ(A.X, U.1)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let hU := U.2.preimage A.relativeSpecToBase
  have hchart := IsAffineOpen.SpecMap_appLE_fromSpec ι hU (isAffineOpen_top _)
    (A.top_le_preimage_relativeSpecToBase U)
  have hring := sections_relativeSpecPushforwardIso A U
  let fU := CommRingCat.ofHom (sectionsAlgHom A.relativeSpecPushforwardIso.hom U.1).toRingHom
  let k : CommRingCat.of Γ(A.relativeSpec, A.relativeSpecToBase ⁻¹ᵁ U.1) ⟶
      CommRingCat.of Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, U.1) :=
    A.relativeSpecToBase.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1)
  have hc : Spec.map fU ≫ (Spec.map k ≫ hU.fromSpec) = ι := by
    -- The affine-site wrapper and section-ring carriers require full transparency here.
    -- The first calculation is functoriality of Spec; the last is the affine unit/counit law.
    erw [← Spec.map_comp_assoc, hring, Spec.map_comp_assoc, hchart,
      IsAffineOpen.fromSpec_top]
    erw [← Scheme.isoSpec_Spec_hom, Iso.hom_inv_id_assoc]
  -- Work at explicit spectrum sources: the open-cover object accessor is opaque to `rw`.
  exact (relativeSpecCover_f_relativeSpecMap_assoc A.relativeSpecPushforwardIso.hom U _).trans
    ((congrArg (Spec.map fU ≫ ·)
      (A.relativeSpecToBase.relativeSpecCover_f_relativeSpecFunctionsToScheme U)).trans
        (hc.trans (Category.comp_id _).symm))

end CategoryTheory.CommMon

namespace TauCeti.AlgebraicGeometry

variable (X : Scheme.{u})

/-- The geometric triangle identity for the canonical relative-Spec unit and counit. -/
@[reassoc (attr := simp)]
lemma relativeSpec_unit_counit (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    (relativeSpec X).map ((relativeSpecUnit X).hom.app A) ≫
        (relativeSpecCounit X).hom.app ((relativeSpec X).obj A) =
      𝟙 ((relativeSpec X).obj A) := by
  apply MorphismProperty.Over.Hom.ext
  -- Full transparency identifies the morphism-property over-category with its comma category.
  erw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.id_left,
    relativeSpec_map_left, relativeSpecCounit_hom_app_left,
    relativeSpecUnit_hom_app_unop_hom]
  -- After the characteristic equations, the exposed relative-Spec object identifies its
  -- structure morphism. Rewriting that morphism would change a dependent affineness instance.
  change CommMon.relativeSpecMap A.unop.obj.relativeSpecPushforwardIso.hom ≫
      A.unop.obj.relativeSpecToBase.relativeSpecFunctionsToScheme = 𝟙 _
  exact A.unop.obj.relativeSpecMap_relativeSpecPushforwardIso_hom_comp

/-- Relative Spec and the algebra of regular functions give an anti-equivalence between
quasi-coherent commutative algebras and affine schemes over an arbitrary base scheme. Its unit
and counit are the canonical section and affine-chart comparisons. -/
def relativeSpecEquiv : (QuasicoherentAlgebra X)ᵒᵖ ≌ AffineSchemeOver X where
  functor := relativeSpec X
  inverse := affineFunctions X
  unitIso := relativeSpecUnit X
  counitIso := relativeSpecCounit X
  functor_unitIso_comp := relativeSpec_unit_counit X

/-- The forward functor is the previously constructed relative spectrum. -/
@[simp]
lemma relativeSpecEquiv_functor : (relativeSpecEquiv X).functor = relativeSpec X := (rfl)

/-- The inverse functor takes the actual algebra of regular functions. -/
@[simp]
lemma relativeSpecEquiv_inverse : (relativeSpecEquiv X).inverse = affineFunctions X := (rfl)

/-- The equivalence uses the canonical algebra-side comparison. -/
@[simp]
lemma relativeSpecEquiv_unitIso :
    (relativeSpecEquiv X).unitIso ≪≫ eqToIso (by
      rw [relativeSpecEquiv_functor, relativeSpecEquiv_inverse]) = relativeSpecUnit X :=
  (rfl)

/-- The equivalence uses the canonical geometric recovery comparison. -/
@[simp]
lemma relativeSpecEquiv_counitIso :
    eqToIso (by rw [relativeSpecEquiv_functor, relativeSpecEquiv_inverse]) ≪≫
      (relativeSpecEquiv X).counitIso = relativeSpecCounit X := (rfl)

/-- Relative Spec is an equivalence, in particular fully faithful and essentially surjective. -/
instance relativeSpec_isEquivalence : (relativeSpec X).IsEquivalence := by
  rw [← relativeSpecEquiv_functor]
  exact (relativeSpecEquiv X).isEquivalence_functor

/-- Taking functions is an equivalence, in particular fully faithful and essentially
surjective. -/
instance affineFunctions_isEquivalence : (affineFunctions X).IsEquivalence := by
  rw [← relativeSpecEquiv_inverse]
  exact (relativeSpecEquiv X).isEquivalence_inverse

/-- The algebraic triangle identity for the canonical relative-Spec comparisons. -/
@[reassoc]
lemma affineFunctions_unit_counit (V : AffineSchemeOver X) :
    (relativeSpecUnit X).hom.app ((affineFunctions X).obj V) ≫
        (affineFunctions X).map ((relativeSpecCounit X).hom.app V) =
      𝟙 ((affineFunctions X).obj V) :=
  (relativeSpecEquiv X).unit_inverse_comp V

/-- The algebraic triangle identity, inverted: on function algebras, the relative-Spec counit
is the inverse of the relative-Spec unit. -/
@[simp]
lemma affineFunctions_map_relativeSpecCounit_hom_app (V : AffineSchemeOver X) :
    (affineFunctions X).map ((relativeSpecCounit X).hom.app V) =
      (relativeSpecUnit X).inv.app ((affineFunctions X).obj V) :=
  ((relativeSpecEquiv X).unitInv_app_inverse V).symm

end TauCeti.AlgebraicGeometry
