/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Nilpotent.Points
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Scheme.Adjoint

import Mathlib.Algebra.Group.Action.TransferInstance
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints

/-!
# The adjoint action on the nilpotent cone

The full scheme-theoretic nilpotent cone is stable under the adjoint action. Its action is
obtained by descending the polynomial comodule algebra through the existing defining ideal.
On points over a commutative test algebra, this gives a group action compatible with the
adjoint action on scalar-extended Lie vectors.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace TauCeti

universe u

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)
local notation "P" => SymmetricAlgebra k (Module.Dual k 𝔤)
local notation "I" => nilpotentConeIdeal k H

/-- Mathlib's braided relative spectrum, specialized to the bundled ground field. -/
local instance algSpecBraided : (algSpec (CommRingCat.of k)).Braided :=
  AlgebraicGeometry.braidedAlgSpec

attribute [local instance] adjointPolynomialComoduleAlgebra nilpotentConeComoduleAlgebra

/-- The full nilpotent cone over its ground field. -/
abbrev nilpotentConeOver : Over (Spec (.of k)) :=
  (algSpec (.of k)).obj (op (CommAlgCat.of k (P ⧸ I)))

/-- The represented cone has the existing structural morphism over its ground field. -/
theorem nilpotentConeOver_hom : (nilpotentConeOver k H).hom = nilpotentConeToSpec k H := by
  rw [nilpotentConeToSpec_eq]
  exact algSpec_obj_hom _

/-- The closed inclusion of the nilpotent cone, as a morphism over the ground field. -/
def nilpotentConeιOver : nilpotentConeOver k H ⟶ lieAlgebraOver k H :=
  Over.homMk (nilpotentConeι k H) (by
    rw [nilpotentConeOver_hom]
    exact nilpotentConeι_comp_toSpec k H)

/-- Forgetting the base recovers the existing closed inclusion. -/
@[simp]
theorem nilpotentConeιOver_left : (nilpotentConeιOver k H).left = nilpotentConeι k H := by
  exact Over.homMk_left _ _

local notation "G" => Grp.X (Functor.obj (hopfSpec (CommRingCat.of k))
  (op (CommHopfAlgCat.of k H)))

/-- The adjoint action on the full scheme-theoretic nilpotent cone. -/
@[implicit_reducible]
def nilpotentConeAdjointAction : ModObj G (nilpotentConeOver k H) :=
  ComoduleAlgebra.specModObj k H (P ⧸ I)

attribute [local instance] lieAlgebraAdjointAction nilpotentConeAdjointAction

/-- The nilpotent-cone inclusion in its quotient and polynomial coordinate presentations. -/
theorem nilpotentConeιOver_eq : nilpotentConeιOver k H =
    (algSpec (.of k)).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)).op ≫
        (lieAlgebraOverIso k H).hom := by
  apply Over.OverMorphism.ext
  simp only [nilpotentConeιOver_left, Over.comp_left, lieAlgebraOverIso_hom_left,
    TauCeti.algSpec_map_left_ofAlgHom, nilpotentConeι_eq]
  exact congrArg (fun f : P →+* P ⧸ I ↦
    Spec.map (CommRingCat.ofHom f) ≫ (lieAlgebraSchemeIso k H).inv)
    (Ideal.Quotient.mkₐ_toRingHom k I).symm

/-- The existing closed inclusion of the cone is equivariant for the adjoint actions. -/
instance nilpotentConeιOver_isModHom : IsModHom G (nilpotentConeιOver k H) := by
  let : ModObj G ((algSpec (.of k)).obj (op (CommAlgCat.of k P))) :=
    ComoduleAlgebra.specModObj k H P
  let : IsModHom G
      ((algSpec (.of k)).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)).op) :=
    ComoduleAlgebra.specModObj_isModHom (Ideal.Quotient.mkₐ k I)
      (nilpotentConeComoduleAlgebra_coactAlgHom_comp_mk k H)
  refine { smul_hom := ?_ }
  rw [lieAlgebraAdjointAction_smul]
  rw [nilpotentConeιOver_eq]
  simpa using IsModHom.smul_hom (A := G)
    (f := (algSpec (.of k)).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)).op)

section Points

variable {A : Type u} [CommRing A] [Algebra k A]

private def nilpotentConePointOverEquiv :
    {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))} ≃
      ((algSpec (.of k)).obj (op (CommAlgCat.of k A)) ⟶ nilpotentConeOver k H) :=
  TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom.trans
    (TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom (R := CommRingCat.of k)
      (CommAlgCat.of k (P ⧸ I)) (CommAlgCat.of k A)).symm

@[simp]
private theorem nilpotentConePointOverEquiv_apply
    (f : {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))}) :
    nilpotentConePointOverEquiv k H f =
      (algSpec (.of k)).map (CommAlgCat.ofHom
        (TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom f)).op := by
  rw [nilpotentConePointOverEquiv, Equiv.trans_apply]
  exact TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom_symm_apply
    (R := CommRingCat.of k) _

/-- The adjoint action of algebra-valued group points on morphisms to the cone over the field. -/
@[no_expose]
local instance nilpotentConeOverPointAction : MulAction (WithConv (H →ₐ[k] A))
    ((algSpec (.of k)).obj (op (CommAlgCat.of k A)) ⟶ nilpotentConeOver k H) := by
  refine MulAction.compHom _ (?_ : WithConv (H →ₐ[k] A) →*
    ((algSpec (.of k)).obj (op (CommAlgCat.of k A)) ⟶ G))
  exact Spec.mapMulEquiv.toMonoidHom

/-- The group action on algebra-valued cone points, transported from the native action
on scheme morphisms through their algebra homomorphisms. -/
@[no_expose]
instance nilpotentConePointAction : MulAction (WithConv (H →ₐ[k] A))
    {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))} := by
  exact (nilpotentConePointOverEquiv k H).mulAction _

/-- The action on the existing point presentation is the native action on scheme morphisms. -/
theorem nilpotentConePointAction_eq (g : WithConv (H →ₐ[k] A))
    (f : {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))}) :
    letI : ModObj ((algSpec (.of k)).obj (op (CommAlgCat.of k H))) (nilpotentConeOver k H) :=
      nilpotentConeAdjointAction k H
    (algSpec (.of k)).map (CommAlgCat.ofHom
      (TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom
        (g • f))).op =
      (algSpec (.of k)).map (CommAlgCat.ofHom g.ofConv).op •
        (algSpec (.of k)).map (CommAlgCat.ofHom
          (TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom f)).op := by
  rw [← nilpotentConePointOverEquiv_apply, ← nilpotentConePointOverEquiv_apply,
    Equiv.smul_def (nilpotentConePointOverEquiv k H), Equiv.apply_symm_apply]
  -- Rewrite the group coordinate in the Hopf spectrum presentation used by the pulled-back
  -- action. The relative spectrum presentation in the statement gives the same action.
  exact congrArg
    (fun p : (algSpec (.of k)).obj (op (CommAlgCat.of k A)) ⟶ G ↦
      p • nilpotentConePointOverEquiv k H f)
    (TauCeti.CommHopfAlgCat.mapMulEquiv_eq_algSpec_map H A g)

/-- The action evaluates the descended coaction against the cone point and the inverse
group point, with inversion expressed by the Hopf antipode. -/
@[simp]
theorem specOverHomEquivAlgHom_nilpotentConePointAction (g : WithConv (H →ₐ[k] A))
    (f : {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))}) :
    TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom (g • f) =
      (Algebra.TensorProduct.lift
        (TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom f)
        (g.ofConv.comp (HopfAlgebra.antipodeAlgHom k H)) (fun _ _ ↦ Commute.all _ _)).comp
        (ComoduleAlgebra.coactAlgHom k H (P ⧸ I)) := by
  let : ModObj ((algSpec (.of k)).obj (op (CommAlgCat.of k H))) (nilpotentConeOver k H) :=
    nilpotentConeAdjointAction k H
  apply (TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom (R := CommRingCat.of k)
    (CommAlgCat.of k (P ⧸ I)) (CommAlgCat.of k A)).symm.injective
  rw [TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom_symm_apply,
    TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom_symm_apply,
    nilpotentConePointAction_eq, ComoduleAlgebra.specModObj_smul_map]

/-- The action on cone points is the ordinary adjoint action on scalar-extended Lie vectors.
The coordinate hypothesis uses the existing point equivalence and canonical evaluation pairing. -/
theorem nilpotentConePointAction_coordinates (g : WithConv (H →ₐ[k] A))
    (f : {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))})
    (z : A ⊗[k] 𝔤)
    (hz : ∀ φ, (nilpotentConePointEquiv k H f).val φ =
      Module.Dual.baseChangeEvaluation (1 ⊗ₜ[k] φ) z) (φ : Module.Dual k 𝔤) :
    (nilpotentConePointEquiv k H (g • f)).val φ =
      Module.Dual.baseChangeEvaluation (1 ⊗ₜ[k] φ)
        ((Derivation.adjointAction (CommAlgCat.of k A) g).val z) := by
  rw [← polynomialCoact_eval_ι k H g _ z hz φ]
  rw [← SymmetricAlgebra.lift_ι_apply
    (nilpotentConePointEquiv k H (g • f)).val φ]
  rw [lift_nilpotentConePointEquiv, specOverHomEquivAlgHom_nilpotentConePointAction]
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ComoduleAlgebra.coactAlgHom_apply]
  have hg : g.ofConv.comp (HopfAlgebra.antipodeAlgHom k H) = (g⁻¹).ofConv := by
    ext h
    exact (WithConv.algHom_inv_apply g h).symm
  rw [hg]
  -- Expose evaluation of the quotient coaction on a linear polynomial generator.
  change Algebra.TensorProduct.lift
    (TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom f) (g⁻¹).ofConv
    (fun _ _ ↦ Commute.all _ _)
    (Comodule.coact (R := k) (C := H) (Ideal.Quotient.mk I
      (SymmetricAlgebra.ι k (Module.Dual k 𝔤) φ))) = _
  rw [nilpotentConeComoduleAlgebra_coact_mk,
    lift_nilpotentConePointEquiv]
  generalize Comodule.coact (R := k) (C := H)
    (SymmetricAlgebra.ι k (Module.Dual k 𝔤) φ) = q
  induction q using TensorProduct.inductionOn <;> simp_all

end Points

end TauCeti
