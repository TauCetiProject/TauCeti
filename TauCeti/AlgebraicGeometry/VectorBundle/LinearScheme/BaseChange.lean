/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.LinearScheme
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Basic

/-!
# Base change of linear schemes

A linear scheme is recovered from its degree-one sheaf by the graded symmetric algebra.
Consequently its base change along `f : Y ⟶ X` can be constructed by pulling back that sheaf
and taking its linear spectrum. This retains the grading, not just the underlying scheme.

`QuasicoherentLinearScheme.pullback` implements this construction. The natural isomorphisms
`linearSpecPullbackIso` and `pullbackDegreeOneIso` identify its action under the equivalence
between quasicoherent sheaves (opposite) and linear schemes. Most importantly,
`pullbackForgetIso` identifies its underlying affine scheme with the actual fibre product
`Y ×_X V`: it uses base change of the relative spectrum of a symmetric algebra, followed by
the reconstruction isomorphism `Spec_X (Sym A₁) ≅ V`.

The identity and composition comparisons are induced by those of quasicoherent pullback and
by the unit and counit of `linearSpecEquiv`. No flatness, finite rank, or affineness assumption
is needed.

## References

* The Stacks Project, Section 27.6, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.7.
-/

public section

open CategoryTheory Opposite
open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.QuasicoherentLinearScheme

universe u

noncomputable section

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X)

/-- Base change of linear schemes: pull back the degree-one sheaf and reconstruct its graded
linear spectrum. Its underlying affine scheme is the fibre product (`pullbackForgetIso`). -/
-- Exposed so that the comparison components below can be typed at the reconstructed objects.
@[expose]
def pullback : QuasicoherentLinearScheme X ⥤ QuasicoherentLinearScheme Y :=
  degreeOne X ⋙ (QuasicoherentSheaf.pullback f).op ⋙ linearSpec Y

/-- Base change sends `V` to the linear spectrum of the pullback of its degree-one sheaf. -/
@[simp]
theorem pullback_obj (V : QuasicoherentLinearScheme X) :
    (pullback f).obj V =
      (linearSpec Y).obj ((QuasicoherentSheaf.pullback f).op.obj ((degreeOne X).obj V)) :=
  (rfl)

/-- Base change acts on morphisms by pulling back their degree-one maps and taking linear
spectra. -/
@[simp]
theorem pullback_map {V W : QuasicoherentLinearScheme X} (a : V ⟶ W) :
    (pullback f).map a =
      (linearSpec Y).map ((QuasicoherentSheaf.pullback f).op.map ((degreeOne X).map a)) :=
  (rfl)

/-- The degree-one sheaf of a base-changed linear scheme is the pullback of its original
degree-one sheaf, naturally in the linear scheme. -/
def pullbackDegreeOneIso :
    pullback f ⋙ degreeOne Y ≅ degreeOne X ⋙ (QuasicoherentSheaf.pullback f).op :=
  Functor.isoWhiskerLeft (degreeOne X ⋙ (QuasicoherentSheaf.pullback f).op)
    (linearSpecEquiv Y).unitIso.symm

/-- The degree-one comparison is the identification `Sym¹(f^* A₁) ≅ f^* A₁`. -/
@[simp]
theorem pullbackDegreeOneIso_hom_app (V : QuasicoherentLinearScheme X) :
    (pullbackDegreeOneIso f).hom.app V =
      (degreeOneLinearSpecIso
        ((QuasicoherentSheaf.pullback f).op.obj ((degreeOne X).obj V))).hom := by
  -- Left whiskering evaluates the inverse unit at the pulled-back degree-one sheaf.
  change (linearSpecEquiv Y).unitInv.app _ = _
  exact linearSpecEquiv_unitInv_app _

/-- The inverse degree-one comparison is the inverse of `Sym¹(f^* A₁) ≅ f^* A₁`. -/
@[simp]
theorem pullbackDegreeOneIso_inv_app (V : QuasicoherentLinearScheme X) :
    (pullbackDegreeOneIso f).inv.app V =
      (degreeOneLinearSpecIso
        ((QuasicoherentSheaf.pullback f).op.obj ((degreeOne X).obj V))).inv := by
  -- Left whiskering evaluates the unit at the pulled-back degree-one sheaf.
  change (linearSpecEquiv Y).unit.app _ = _
  exact linearSpecEquiv_unit_app _

/-- Linear spectrum commutes with arbitrary base change, as a functor to structured linear
schemes, not merely to schemes over the base. -/
def linearSpecPullbackIso :
    linearSpec X ⋙ pullback f ≅ (QuasicoherentSheaf.pullback f).op ⋙ linearSpec Y :=
  (linearSpecEquiv X).funInvIdAssoc ((QuasicoherentSheaf.pullback f).op ⋙ linearSpec Y)

/-- The base-change comparison for linear spectrum is induced by `Sym¹ F ≅ F`. -/
@[simp]
theorem linearSpecPullbackIso_hom_app (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (linearSpecPullbackIso f).hom.app F =
      (linearSpec Y).map ((QuasicoherentSheaf.pullback f).op.map
        (degreeOneLinearSpecIso F).hom) := by
  rw [linearSpecPullbackIso, Equivalence.funInvIdAssoc_hom_app, linearSpecEquiv_unitInv_app]
  -- Mapping by a composite functor is definitionally successive mapping.
  rfl

/-- The inverse base-change comparison for linear spectrum is induced by `F ≅ Sym¹ F`. -/
@[simp]
theorem linearSpecPullbackIso_inv_app (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (linearSpecPullbackIso f).inv.app F =
      (linearSpec Y).map ((QuasicoherentSheaf.pullback f).op.map
        (degreeOneLinearSpecIso F).inv) := by
  rw [linearSpecPullbackIso, Equivalence.funInvIdAssoc_inv_app, linearSpecEquiv_unit_app]
  rfl

/-- **Base change of the underlying scheme.** Forgetting the grading after base change of a
linear scheme gives the base change of its underlying affine scheme. The comparison first uses
base change of `Spec (Sym A₁)` and then `Spec (Sym A₁) ≅ V`. -/
def pullbackForgetIso :
    pullback f ⋙ forget Y ≅ forget X ⋙ baseChangeAffineSchemeOver f :=
  Functor.isoWhiskerLeft (degreeOne X)
    (Functor.isoWhiskerLeft (QuasicoherentSheaf.pullback f).op (linearSpecForgetIso Y) ≪≫
      relativeSpecSymmetricAlgebraBaseChangeIso f) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (degreeOne X) (linearSpecForgetIso X).symm ≪≫
        (linearSpecEquiv X).invFunIdAssoc (forget X))
      (baseChangeAffineSchemeOver f)

/-- On objects the underlying-scheme comparison is base change of the symmetric spectrum,
followed by the base change of the reconstruction isomorphism. -/
theorem pullbackForgetIso_hom_app (V : QuasicoherentLinearScheme X) :
    (pullbackForgetIso f).hom.app V =
      ((linearSpecForgetIso Y).hom.app
          ((QuasicoherentSheaf.pullback f).op.obj ((degreeOne X).obj V)) ≫
        (relativeSpecSymmetricAlgebraBaseChangeIso f).hom.app ((degreeOne X).obj V)) ≫
      (baseChangeAffineSchemeOver f).map
        ((linearSpecForgetIso X).inv.app ((degreeOne X).obj V) ≫
          (forget X).map ((linearSpecEquiv X).counit.app V)) := by
  -- Unfolding whiskering and iso composition exposes the cancellation component. Rewriting
  -- these operations fails to match the slice's mixed `IsAffineHom` category instances.
  change _ ≫ (baseChangeAffineSchemeOver f).map
    ((linearSpecForgetIso X).inv.app ((degreeOne X).obj V) ≫
      ((linearSpecEquiv X).invFunIdAssoc (forget X)).hom.app V) = _
  exact congrArg (fun a ↦ _ ≫ (baseChangeAffineSchemeOver f).map
    ((linearSpecForgetIso X).inv.app ((degreeOne X).obj V) ≫ a))
    (Equivalence.invFunIdAssoc_hom_app _ _ V)

/-- The inverse underlying-scheme comparison reverses reconstruction and symmetric-spectrum
base change. -/
theorem pullbackForgetIso_inv_app (V : QuasicoherentLinearScheme X) :
    (pullbackForgetIso f).inv.app V =
      (baseChangeAffineSchemeOver f).map
        ((forget X).map ((linearSpecEquiv X).counitInv.app V) ≫
          (linearSpecForgetIso X).hom.app ((degreeOne X).obj V)) ≫
      ((relativeSpecSymmetricAlgebraBaseChangeIso f).inv.app ((degreeOne X).obj V) ≫
        (linearSpecForgetIso Y).inv.app
          ((QuasicoherentSheaf.pullback f).op.obj ((degreeOne X).obj V))) := by
  -- As for the hom component, unfold whiskering/composition only to expose cancellation.
  change (baseChangeAffineSchemeOver f).map
    (((linearSpecEquiv X).invFunIdAssoc (forget X)).inv.app V ≫
      (linearSpecForgetIso X).hom.app ((degreeOne X).obj V)) ≫ _ = _
  exact congrArg (fun a ↦ (baseChangeAffineSchemeOver f).map
    (a ≫ (linearSpecForgetIso X).hom.app ((degreeOne X).obj V)) ≫ _)
    (Equivalence.invFunIdAssoc_inv_app _ _ V)

/-- The base-change comparison after forgetting the affine slice structure. -/
def pullbackForgetIsoLeft (V : QuasicoherentLinearScheme X) :
    ((pullback f).obj V).obj.fst.left ≅ Limits.pullback V.obj.fst.hom f :=
  ((MorphismProperty.Over.forget _ _ Y) ⋙ Over.forget Y).mapIso
    ((pullbackForgetIso f).app V)

/-- The forward scheme comparison is the underlying map of the affine-slice comparison. -/
@[simp]
theorem pullbackForgetIsoLeft_hom (V : QuasicoherentLinearScheme X) :
    (pullbackForgetIsoLeft f V).hom = ((pullbackForgetIso f).hom.app V).left :=
  (rfl)

/-- The inverse scheme comparison is the underlying inverse affine-slice map. -/
@[simp]
theorem pullbackForgetIsoLeft_inv (V : QuasicoherentLinearScheme X) :
    (pullbackForgetIsoLeft f V).inv = ((pullbackForgetIso f).inv.app V).left :=
  (rfl)

/-- The projection from a base-changed linear scheme to the original total space. -/
def pullbackFst (V : QuasicoherentLinearScheme X) :
    ((pullback f).obj V).obj.fst.left ⟶ V.obj.fst.left :=
  ((pullbackForgetIso f).hom.app V).left ≫ Limits.pullback.fst V.obj.fst.hom f

/-- The underlying-scheme comparison carries the first fibre-product projection to
`pullbackFst`. -/
@[simp, reassoc]
theorem pullbackForgetIso_hom_left_fst (V : QuasicoherentLinearScheme X) :
    ((pullbackForgetIso f).hom.app V).left ≫ Limits.pullback.fst V.obj.fst.hom f =
      pullbackFst f V :=
  (rfl)

/-- The underlying-scheme comparison carries the second fibre-product projection to the
structure morphism of the base-changed linear scheme. -/
@[simp, reassoc]
theorem pullbackForgetIso_hom_left_snd (V : QuasicoherentLinearScheme X) :
    ((pullbackForgetIso f).hom.app V).left ≫ Limits.pullback.snd V.obj.fst.hom f =
      ((pullback f).obj V).obj.fst.hom :=
  -- The target affine slice object has structure morphism `pullback.snd` by definition.
  -- Unfolding is needed to recognize `IsAffineHom` as a morphism property in `Over.w`.
  MorphismProperty.Over.w ((pullbackForgetIso f).hom.app V)

/-- The inverse underlying-scheme comparison recovers the first fibre-product projection. -/
@[simp, reassoc]
theorem pullbackForgetIso_inv_left_fst (V : QuasicoherentLinearScheme X) :
    ((pullbackForgetIso f).inv.app V).left ≫ pullbackFst f V =
      Limits.pullback.fst V.obj.fst.hom f := by
  rw [← pullbackForgetIso_hom_left_fst]
  exact (pullbackForgetIsoLeft f V).inv_hom_id_assoc _

/-- The inverse underlying-scheme comparison recovers the second fibre-product projection. -/
@[simp, reassoc]
theorem pullbackForgetIso_inv_left_snd (V : QuasicoherentLinearScheme X) :
    ((pullbackForgetIso f).inv.app V).left ≫ ((pullback f).obj V).obj.fst.hom =
      Limits.pullback.snd V.obj.fst.hom f := by
  rw [← pullbackForgetIso_hom_left_snd]
  exact (pullbackForgetIsoLeft f V).inv_hom_id_assoc _

/-- The base-change projection is natural in the original linear scheme. -/
@[reassoc]
theorem pullbackFst_naturality {V W : QuasicoherentLinearScheme X} (a : V ⟶ W) :
    ((pullback f).map a).hom.fst.left ≫ pullbackFst f W =
      pullbackFst f V ≫ a.hom.fst.left := by
  have h := congrArg (fun b ↦ b.left) ((pullbackForgetIso f).hom.naturality a)
  -- `erw` unfolds the mixed `IsAffineHom` instances; ordinary `rw` cannot type-check
  -- these expressions at implicit transparency, even for associativity in schemes.
  erw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left] at h
  rw [← pullbackForgetIso_hom_left_fst, ← pullbackForgetIso_hom_left_fst]
  erw [← Category.assoc, h, Category.assoc,
    baseChangeAffineSchemeOver_map_left_fst, Category.assoc]

/-- The base-change projection commutes with the structure morphisms. -/
@[reassoc (attr := simp)]
theorem pullbackFst_hom (V : QuasicoherentLinearScheme X) :
    pullbackFst f V ≫ V.obj.fst.hom = ((pullback f).obj V).obj.fst.hom ≫ f := by
  -- As in naturality, `erw` is needed for the mixed affine-slice instances.
  erw [← pullbackForgetIso_hom_left_fst, Category.assoc,
    Limits.pullback.condition (f := V.obj.fst.hom) (g := f), ← Category.assoc]
  exact congrArg (· ≫ f) (pullbackForgetIso_hom_left_snd f V)

/-- The square consisting of the base-change projection and the structure morphisms is
cartesian in schemes. -/
theorem isPullback_pullbackFst (V : QuasicoherentLinearScheme X) :
    IsPullback (pullbackFst f V) ((pullback f).obj V).obj.fst.hom V.obj.fst.hom f := by
  exact IsPullback.of_iso_pullback ⟨pullbackFst_hom f V⟩ (pullbackForgetIsoLeft f V)
    (pullbackForgetIso_hom_left_fst f V) (pullbackForgetIso_hom_left_snd f V)

/-- Base change along the identity is naturally the identity on linear schemes. -/
def pullbackId (X : Scheme.{u}) : pullback (𝟙 X) ≅ 𝟭 (QuasicoherentLinearScheme X) :=
  Functor.isoWhiskerLeft (degreeOne X)
    (Functor.isoWhiskerRight (NatIso.op (QuasicoherentSheaf.pullbackId X)).symm
      (linearSpec X)) ≪≫
    (linearSpecEquiv X).counitIso

/-- The identity comparison pulls the identity comparison of quasicoherent sheaves through
linear spectrum and then reconstructs the original linear scheme. -/
@[simp]
theorem pullbackId_hom_app (V : QuasicoherentLinearScheme X) :
    (pullbackId X).hom.app V =
      (linearSpec X).map (((QuasicoherentSheaf.pullbackId X).inv.app
        ((degreeOne X).obj V).unop).op) ≫ (linearSpecDegreeOneIso V).hom := by
  unfold pullbackId
  -- `erw` recognizes composition through the mixed sheaf category instances.
  erw [Iso.trans_hom, NatTrans.comp_app]
  rw [linearSpecEquiv_counit_app]
  -- Whiskering and `NatIso.op` evaluate to the displayed mapped component.
  rfl

/-- The inverse identity comparison reverses reconstruction, then the identity comparison
of quasicoherent pullback. -/
@[simp]
theorem pullbackId_inv_app (V : QuasicoherentLinearScheme X) :
    (pullbackId X).inv.app V =
      (linearSpecDegreeOneIso V).inv ≫
        (linearSpec X).map (((QuasicoherentSheaf.pullbackId X).hom.app
          ((degreeOne X).obj V).unop).op) := by
  have h : (linearSpecEquiv X).counitIso.app V = linearSpecDegreeOneIso V :=
    Iso.ext (linearSpecEquiv_counit_app V)
  -- Iso composition, whiskering and `NatIso.op` give the displayed inverse component.
  exact congrArg (· ≫ (linearSpec X).map
    (((QuasicoherentSheaf.pullbackId X).hom.app ((degreeOne X).obj V).unop).op))
    (congrArg Iso.inv h)

/-- Successive base changes of linear schemes agree naturally with base change along the
composite morphism. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  Functor.isoWhiskerRight (pullbackDegreeOneIso g)
    ((QuasicoherentSheaf.pullback f).op ⋙ linearSpec X) ≪≫
  Functor.isoWhiskerLeft (degreeOne Z)
    (Functor.isoWhiskerRight (NatIso.op (QuasicoherentSheaf.pullbackComp f g)).symm
      (linearSpec X))

/-- The composition comparison uses `Sym¹(g^* A₁) ≅ g^* A₁` and the composition comparison for
quasicoherent pullback. -/
@[simp]
theorem pullbackComp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (V : QuasicoherentLinearScheme Z) :
    (pullbackComp f g).hom.app V =
      (linearSpec X).map ((QuasicoherentSheaf.pullback f).op.map
        ((pullbackDegreeOneIso g).hom.app V)) ≫
      (linearSpec X).map (((QuasicoherentSheaf.pullbackComp f g).inv.app
        ((degreeOne Z).obj V).unop).op) := by
  rfl

/-- The inverse composition comparison first separates quasicoherent pullbacks, then
reverses the degree-one comparison. -/
@[simp]
theorem pullbackComp_inv_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (V : QuasicoherentLinearScheme Z) :
    (pullbackComp f g).inv.app V =
      (linearSpec X).map (((QuasicoherentSheaf.pullbackComp f g).hom.app
        ((degreeOne Z).obj V).unop).op) ≫
      (linearSpec X).map ((QuasicoherentSheaf.pullback f).op.map
        ((pullbackDegreeOneIso g).inv.app V)) :=
  (rfl)

end

end TauCeti.AlgebraicGeometry.QuasicoherentLinearScheme
