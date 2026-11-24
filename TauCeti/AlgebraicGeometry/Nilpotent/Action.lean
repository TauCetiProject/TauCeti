/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Nilpotent.Points
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.Quotient
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.ComoduleAction
public import TauCeti.LinearAlgebra.Dual.BaseChange
import TauCeti.Algebra.Coalgebra.Comodule.Evaluation

/-!
# The adjoint action on the nilpotent cone

The full scheme-theoretic nilpotent cone is stable under the adjoint action. Its action is
obtained by descending the polynomial comodule algebra through the existing defining ideal.
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

attribute [local instance] adjointPolynomialComoduleAlgebra

/-- The polynomial coaction descends to the full coordinate ring of the nilpotent cone. -/
@[implicit_reducible]
def nilpotentConeComoduleAlgebra : ComoduleAlgebra k H (P ⧸ I) :=
  ComoduleAlgebra.quotient I fun _ hp ↦ coact_mem_map_includeLeft_nilpotentConeIdeal hp

attribute [local instance] nilpotentConeComoduleAlgebra

/-- The descended coaction is computed by applying the quotient map to polynomial functions. -/
theorem nilpotentConeComoduleAlgebra_coact_mk (p : P) :
    Comodule.coact (R := k) (C := H) (Ideal.Quotient.mk I p) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (AlgHom.id k H)
        (Comodule.coact (R := k) (C := H) p) :=
  ComoduleAlgebra.quotient_coact_mk I _ p

/-- The tangent scheme over the ground field, using its polynomial presentation. -/
abbrev lieAlgebraOver : Over (Spec (.of k)) :=
  Over.mk ((lieAlgebraSchemeIso k H).hom ≫ Spec.algebraMap k P)

/-- The full nilpotent cone over its ground field. -/
abbrev nilpotentConeOver : Over (Spec (.of k)) :=
  (algSpec (.of k)).obj (op (CommAlgCat.of k (P ⧸ I)))

/-- The represented cone has the existing structural morphism over its ground field. -/
theorem nilpotentConeOver_hom : (nilpotentConeOver k H).hom = nilpotentConeToSpec k H := by
  rw [nilpotentConeToSpec_eq]
  exact algSpec_obj_hom _

/-- The polynomial-coordinate presentation of the tangent scheme over the ground field. -/
def lieAlgebraOverIso : (algSpec (.of k)).obj (op (CommAlgCat.of k P)) ≅
    lieAlgebraOver k H :=
  TauCeti.AlgebraicGeometry.algSpecObjIsoOverMk _ ≪≫
    Over.isoMk (lieAlgebraSchemeIso k H).symm (by
      -- Expose the over-category equation while retaining the named scheme isomorphism.
      change (lieAlgebraSchemeIso k H).inv ≫ ((lieAlgebraSchemeIso k H).hom ≫ _) = _
      simp only [Iso.inv_hom_id_assoc, Over.mk_hom])

/-- The polynomial presentation sends a point back through the existing tangent comparison. -/
@[simp]
theorem lieAlgebraOverIso_hom_left : (lieAlgebraOverIso k H).hom.left =
    (lieAlgebraSchemeIso k H).inv := by
  simp only [lieAlgebraOverIso, Iso.trans_hom, Over.comp_left,
    TauCeti.AlgebraicGeometry.algSpecObjIsoOverMk_hom_left]
  rfl

/-- The closed inclusion of the nilpotent cone, as a morphism over the ground field. -/
def nilpotentConeιOver : nilpotentConeOver k H ⟶ lieAlgebraOver k H :=
  Over.homMk (nilpotentConeι k H) (by
    rw [nilpotentConeOver_hom]
    exact nilpotentConeι_comp_toSpec k H)

/-- Forgetting the base recovers the existing closed inclusion. -/
@[simp]
theorem nilpotentConeιOver_left : (nilpotentConeιOver k H).left = nilpotentConeι k H := by
  unfold nilpotentConeιOver
  rfl

local notation "G" => Grp.X (Functor.obj (hopfSpec (CommRingCat.of k))
  (op (CommHopfAlgCat.of k H)))

/-- The adjoint action on the existing tangent scheme over its ground field. -/
@[implicit_reducible]
def lieAlgebraAdjointAction : ModObj G (lieAlgebraOver k H) := by
  letI : ModObj G ((algSpec (.of k)).obj (op (CommAlgCat.of k P))) :=
    ComoduleAlgebra.specModObj k H P
  letI : IsMonHom (Iso.refl G).hom := by
    change IsMonHom (𝟙 G)
    infer_instance
  exact ModObj.ofIso (M := G) (Iso.refl G) (lieAlgebraOverIso k H)

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
  rfl

/-- The existing closed inclusion of the cone is equivariant for the adjoint actions. -/
instance nilpotentConeιOver_isModHom : IsModHom G (nilpotentConeιOver k H) := by
  let : ModObj G ((algSpec (.of k)).obj (op (CommAlgCat.of k P))) :=
    ComoduleAlgebra.specModObj k H P
  let : IsModHom G
      ((algSpec (.of k)).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)).op) :=
    ComoduleAlgebra.specModObj_isModHom (Ideal.Quotient.mkₐ k I)
      (ComoduleAlgebra.quotient_coactAlgHom_comp_mk I _)
  refine { smul_hom := ?_ }
  simp only [ModObj.ofIso_smul]
  rw [nilpotentConeιOver_eq]
  simpa using IsModHom.smul_hom (A := G)
    (f := (algSpec (.of k)).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)).op)

section Points

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The action on algebra-valued cone points, retaining their full scheme structure. -/
def nilpotentConePointAction (g : WithConv (H →ₐ[k] A))
    (f : {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))}) :
    {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))} :=
  letI : ModObj ((algSpec (.of k)).obj (op (CommAlgCat.of k H))) (nilpotentConeOver k H) :=
    nilpotentConeAdjointAction k H
  TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom.symm <|
    TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom (R := CommRingCat.of k)
      (CommAlgCat.of k (P ⧸ I)) (CommAlgCat.of k A)
      (CartesianMonoidalCategory.lift
        ((algSpec (.of k)).map (CommAlgCat.ofHom g.ofConv).op)
        ((algSpec (.of k)).map (CommAlgCat.ofHom
          (TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom f)).op) ≫
        ModObj.smul (M := (algSpec (.of k)).obj (op (CommAlgCat.of k H)))
          (X := nilpotentConeOver k H))

/-- The action on the existing point presentation is the native action on scheme morphisms. -/
theorem nilpotentConePointAction_eq (g : WithConv (H →ₐ[k] A))
    (f : {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))}) :
    letI : ModObj ((algSpec (.of k)).obj (op (CommAlgCat.of k H))) (nilpotentConeOver k H) :=
      nilpotentConeAdjointAction k H
    (algSpec (.of k)).map (CommAlgCat.ofHom
      (TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom
        (nilpotentConePointAction k H g f))).op =
      (algSpec (.of k)).map (CommAlgCat.ofHom g.ofConv).op •
        (algSpec (.of k)).map (CommAlgCat.ofHom
          (TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom f)).op := by
  dsimp only
  rw [nilpotentConePointAction, Equiv.apply_symm_apply]
  exact TauCeti.AlgebraicGeometry.algSpec_map_algSpecHomEquivAlgHom _

private theorem pointAction_algHom (g : WithConv (H →ₐ[k] A))
    (f : {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))}) :
    TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom (nilpotentConePointAction k H g f) =
      (Algebra.TensorProduct.lift
        (TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom f)
        (g.ofConv.comp (HopfAlgebra.antipodeAlgHom k H)) (fun _ _ ↦ Commute.all _ _)).comp
        (ComoduleAlgebra.coactAlgHom k H (P ⧸ I)) := by
  let : ModObj ((algSpec (.of k)).obj (op (CommAlgCat.of k H))) (nilpotentConeOver k H) :=
    nilpotentConeAdjointAction k H
  rw [nilpotentConePointAction, Equiv.apply_symm_apply]
  erw [← Hom.smul_def, ComoduleAlgebra.specModObj_smul_map]
  apply (TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom (R := CommRingCat.of k)
    (CommAlgCat.of k (P ⧸ I)) (CommAlgCat.of k A)).eq_symm_apply.mp
  exact (TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom_symm_apply
    (R := CommRingCat.of k) (A := CommAlgCat.of k (P ⧸ I)) (B := CommAlgCat.of k A) _).symm

private theorem point_lift_eq
    (f : {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))}) :
    SymmetricAlgebra.lift (nilpotentConePointEquiv k H f).val =
      (TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom f).comp (Ideal.Quotient.mkₐ k I) := by
  have h := nilpotentConePointEquiv_comp_ι k H f
  rw [nilpotentConeι_eq] at h
  have hf := TauCeti.AlgebraicGeometry.spec_map_specOverHomEquivAlgHom f
  rw [← hf, ← Category.assoc, ← Spec.map_comp] at h
  apply AlgHom.toRingHom_injective
  have h' := Spec.map_injective ((cancel_mono (lieAlgebraSchemeIso k H).inv).mp h)
  exact (congrArg CommRingCat.Hom.hom h').symm

attribute [local instance] Derivation.adjointComodule Comodule.dual

private theorem polynomialCoact_eval_ι
    (g : WithConv (H →ₐ[k] A)) (x : Module.Dual k 𝔤 →ₗ[k] A) (z : A ⊗[k] 𝔤)
    (hx : ∀ φ, x φ = Module.Dual.baseChangeEvaluation (1 ⊗ₜ[k] φ) z)
    (φ : Module.Dual k 𝔤) :
    Algebra.TensorProduct.lift (SymmetricAlgebra.lift x) (g⁻¹).ofConv
        (fun _ _ ↦ Commute.all _ _)
        (Comodule.coact (R := k) (C := H) (SymmetricAlgebra.ι k (Module.Dual k 𝔤) φ)) =
      Module.Dual.baseChangeEvaluation (1 ⊗ₜ[k] φ)
        ((Derivation.adjointAction (CommAlgCat.of k A) g).val z) := by
  rw [adjointPolynomialComoduleAlgebra_coact_ι]
  rw [← Derivation.adjointComodule_endOfPoint_eq_adjointAction]
  rw [← inv_inv g]
  rw [← Comodule.baseChangeEvaluation_dual_endOfPoint]
  rw [inv_inv, Comodule.endOfPoint_tmul, one_smul, Comodule.dual_coact]
  generalize Comodule.dualCoact (R := k) (H := H) (M := 𝔤) φ = q
  induction q using TensorProduct.inductionOn with
  | add q r hq hr => simp only [map_add, LinearMap.add_apply, hq, hr]
  | tmul ψ h =>
      simp only [LinearMap.rTensor_tmul, Algebra.TensorProduct.lift_tmul,
        SymmetricAlgebra.lift_ι_apply, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
        TensorProduct.comm_tmul, hx]
      have ht (a : A) : a ⊗ₜ[k] ψ = a • ((1 : A) ⊗ₜ[k] ψ) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm] using
        (congrArg (fun ξ ↦ Module.Dual.baseChangeEvaluation ξ z) (ht ((g⁻¹).ofConv h))).symm


/-- The action on cone points is the ordinary adjoint action on scalar-extended Lie vectors.
The coordinate hypothesis uses the existing point equivalence and canonical evaluation pairing. -/
theorem nilpotentConePointAction_coordinates (g : WithConv (H →ₐ[k] A))
    (f : {f : Spec (.of A) ⟶ nilpotentCone k H // f.IsOver (Spec (.of k))})
    (z : A ⊗[k] 𝔤)
    (hz : ∀ φ, (nilpotentConePointEquiv k H f).val φ =
      Module.Dual.baseChangeEvaluation (1 ⊗ₜ[k] φ) z) (φ : Module.Dual k 𝔤) :
    (nilpotentConePointEquiv k H (nilpotentConePointAction k H g f)).val φ =
      Module.Dual.baseChangeEvaluation (1 ⊗ₜ[k] φ)
        ((Derivation.adjointAction (CommAlgCat.of k A) g).val z) := by
  rw [← polynomialCoact_eval_ι k H g _ z hz φ]
  rw [← SymmetricAlgebra.lift_ι_apply
    (nilpotentConePointEquiv k H (nilpotentConePointAction k H g f)).val φ]
  rw [point_lift_eq, pointAction_algHom]
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
  rw [nilpotentConeComoduleAlgebra_coact_mk, point_lift_eq]
  generalize Comodule.coact (R := k) (C := H)
    (SymmetricAlgebra.ι k (Module.Dual k 𝔤) φ) = q
  induction q using TensorProduct.inductionOn <;> simp_all

end Points

end TauCeti
