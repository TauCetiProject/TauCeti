/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Framed
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Subfield

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import TauCeti.LinearAlgebra.Matrix.BaseChange

/-!
# Matrix bridges for framed continuous representations

This file provides congruence, subfield-lifting, and scalar-extension bridges for framed continuous
representations `TauCeti.ContinuousRep.ofFramed`, `TauCeti.ContinuousRep.frame`, and
`TauCeti.ContinuousRep.framedMap` from
`TauCeti.RepresentationTheory.Continuous.ContinuousRep.Framed`.

* **Congruence** (`TauCeti.ContinuousRep.ofFramedCongr`): equal continuous matrix homomorphisms
  yield canonically isomorphic framed representations on `ι → A`.
* **Subfield lifting** (`TauCeti.ContinuousRep.map_subtype_liftGLOfMem_frame`,
  `TauCeti.ContinuousRep.framedMap_subtype_liftGLOfMem`): pushing the subfield lift of
  `frame b ρ` forward along `SubringClass.subtype E` recovers `LinearMap.toMatrix b b (ρ g)`, and
  `framedMap (SubringClass.subtype E)` cancels `ContinuousMonoidHom.liftGLOfMem`.
* **Scalar extension** (`TauCeti.ContinuousRep.baseChangeOfGLIso`): when `B ⊗[A] (ι → A)` carries
  the `B`-module topology, extending scalars of `ofFramed φ` from `A` to `B` corresponds via
  `TensorProduct.piScalarRight` to `framedMap (algebraMap A B)`.

## Main definitions

* `TauCeti.ContinuousRep.ofFramedCongr`: canonical isomorphism between `ofFramed φ₁` and
  `ofFramed φ₂` for equal homomorphisms `φ₁ = φ₂`.
* `TauCeti.ContinuousRep.baseChangeOfGLIso`: canonical isomorphism identifying
  `(ofFramed φ).baseChange B` with `ofFramed (framedMap (algebraMap A B) _ φ)`.

## Main results

* `TauCeti.ContinuousRep.map_subtype_liftGLOfMem_frame`
* `TauCeti.ContinuousRep.framedMap_subtype_liftGLOfMem`
* `TauCeti.ContinuousRep.baseChangeOfGLIso_apply`
-/

public section

open Matrix
open scoped TensorProduct Topology

namespace TauCeti.ContinuousRep

section OfFramedCongr

variable {Γ A ι : Type*} [Monoid Γ] [TopologicalSpace Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Fintype ι] [DecidableEq ι]

/-- **Congruence isomorphism for `ofFramed`.** Equal continuous matrix homomorphisms yield
canonically isomorphic continuous representations on `ι → A`. -/
def ofFramedCongr {φ₁ φ₂ : Γ →ₜ* GL ι A} (h : φ₁ = φ₂) :
    Iso (ofFramed φ₁) (ofFramed φ₂) where
  toRepresentationEquiv := .mk (.refl A (ι → A)) fun g ↦ by
    ext v i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply,
      coe_toRepresentation, ofFramed_apply, h]
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
theorem ofFramedCongr_apply {φ₁ φ₂ : Γ →ₜ* GL ι A} (h : φ₁ = φ₂) (v : ι → A) :
    ofFramedCongr h v = v :=
  (rfl)

@[simp]
theorem ofFramedCongr_symm_apply {φ₁ φ₂ : Γ →ₜ* GL ι A} (h : φ₁ = φ₂) (v : ι → A) :
    (ofFramedCongr h).symm v = v :=
  EquivLike.injective (ofFramedCongr h) (by simp)

end OfFramedCongr

section LiftGL

variable {L S ι : Type*} [Field L] [SetLike S L] [SubfieldClass S L]
  [Fintype ι] [DecidableEq ι]

/-- Pushing the matrix of `(frame b ρ).liftGLOfMem E hE g` forward along `SubringClass.subtype E`
recovers `LinearMap.toMatrix b b (ρ g)`. -/
theorem map_subtype_liftGLOfMem_frame {Γ V : Type*} [Group Γ] [TopologicalSpace Γ]
    [ContinuousInv Γ] [TopologicalSpace L] [IsTopologicalRing L]
    [AddCommGroup V] [Module L V] [TopologicalSpace V] [IsModuleTopology L V]
    (ρ : ContinuousRep Γ L V) (b : Module.Basis ι L V) (E : S)
    (hE : ∀ g i j, (frame b ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) :
    ((frame b ρ).liftGLOfMem E hE g : Matrix ι ι E).map (SubringClass.subtype E) =
      LinearMap.toMatrix b b (ρ g) := by
  rw [SubringClass.coe_subtype, ContinuousMonoidHom.map_subtype_liftGLOfMem_matrix,
    coe_frame_apply]

/-- Composing `ρ.liftGLOfMem E hE` with `framedMap (SubringClass.subtype E) hf` recovers `ρ`. -/
@[simp]
theorem framedMap_subtype_liftGLOfMem {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace L] (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E)
    {hf : Continuous (SubringClass.subtype E)} :
    framedMap (SubringClass.subtype E) hf (ρ.liftGLOfMem E hE) = ρ :=
  ContinuousMonoidHom.ext fun g ↦ Units.ext <| by
    simp [SubringClass.coe_subtype]

end LiftGL

section BaseChangeOfGL

variable {Γ A ι : Type*} [Monoid Γ] [TopologicalSpace Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Fintype ι] [DecidableEq ι]

variable (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [Algebra A B] [ContinuousSMul A B]
  [TopologicalSpace (B ⊗[A] (ι → A))] [IsModuleTopology B (B ⊗[A] (ι → A))]

/-- **Extension of scalars of a matrix representation** identifies `B ⊗[A] (ι → A)` (equipped with
its `B`-module topology `IsModuleTopology B (B ⊗[A] (ι → A))`) with `ι → B` on which `Γ` acts by
the image matrices under `algebraMap A B`, through `TensorProduct.piScalarRight`. -/
def baseChangeOfGLIso (φ : Γ →ₜ* GL ι A) :
    Iso ((ofFramed φ).baseChange B)
      (ofFramed (framedMap (algebraMap A B) (continuous_algebraMap A B) φ)) :=
  .ofEquiv (.mk (TensorProduct.piScalarRight A B B ι) fun g ↦ by
    have hrep : (ofFramed φ).toRepresentation g = Matrix.mulVecLin (φ g : Matrix ι ι A) :=
      LinearMap.ext fun v ↦ by
        simp only [coe_toRepresentation, ofFramed_apply, Matrix.mulVecLin_apply]
    refine LinearMap.ext fun x ↦ ?_
    have hpi : TensorProduct.piScalarRight A B B ι
          ((Matrix.mulVecLin (φ g : Matrix ι ι A)).baseChange B x) =
        ((φ g : Matrix ι ι A).map (algebraMap A B)).mulVec
          (TensorProduct.piScalarRight A B B ι x) := by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply] using
        LinearMap.congr_fun
          (Matrix.piScalarRight_comp_baseChange_mulVecLin (S := B) (φ g : Matrix ι ι A)) x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, toRepresentation_baseChange,
      Representation.baseChange_apply, hrep, hpi, coe_toRepresentation, ofFramed_apply,
      coe_framedMap_apply])

/-- Underlying map of `baseChangeOfGLIso` as `TensorProduct.piScalarRight`. -/
@[simp]
theorem baseChangeOfGLIso_apply (φ : Γ →ₜ* GL ι A) (x : B ⊗[A] (ι → A)) :
    baseChangeOfGLIso B φ x = TensorProduct.piScalarRight A B B ι x :=
  (Iso.ofEquiv_apply _ x).trans (Representation.Equiv.mk_apply _ x)

theorem baseChangeOfGLIso_tmul (φ : Γ →ₜ* GL ι A) (b : B) (v : ι → A) :
    baseChangeOfGLIso B φ (b ⊗ₜ v) = fun i ↦ v i • b :=
  (baseChangeOfGLIso_apply B φ _).trans (TensorProduct.piScalarRightHom_tmul A B B ι b v)

@[simp]
theorem baseChangeOfGLIso_symm_apply (φ : Γ →ₜ* GL ι A) (w : ι → B) :
    (baseChangeOfGLIso B φ).symm w = (TensorProduct.piScalarRight A B B ι).symm w :=
  EquivLike.injective (baseChangeOfGLIso B φ) (by
    rw [Iso.apply_symm_apply, baseChangeOfGLIso_apply]
    exact ((TensorProduct.piScalarRight A B B ι).apply_symm_apply w).symm)

end BaseChangeOfGL

end TauCeti.ContinuousRep
