/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.BaseChange
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Framed
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Subfield

import TauCeti.LinearAlgebra.Matrix.BaseChange

/-!
# Subfield lifting and scalar extension for framed continuous representations

This file provides subfield-lifting and scalar-extension bridges for framed continuous
representations `TauCeti.ContinuousRep.ofFramed`, `TauCeti.ContinuousRep.frame`, and
`TauCeti.ContinuousRep.framedMap` from
`TauCeti.RepresentationTheory.Continuous.ContinuousRep.Framed`:

* **Subfield lifting** (`TauCeti.ContinuousRep.framedMap_subtype_liftGLOfMem`):
  `framedMap (SubringClass.subtype E)` cancels `ContinuousMonoidHom.liftGLOfMem`.
* **Scalar extension** (`TauCeti.ContinuousRep.baseChangeOfGLIso`): when `B ⊗[A] (ι → A)` carries
  the `B`-module topology, extending scalars of `ofFramed φ` from `A` to `B` corresponds via
  `TensorProduct.piScalarRight` to `framedMap (algebraMap A B)`.

## Main definitions

* `TauCeti.ContinuousRep.baseChangeOfGLIso`: canonical isomorphism identifying
  `(ofFramed φ).baseChange B` with `ofFramed (framedMap (algebraMap A B) _ φ)`.

## Main results

* `TauCeti.ContinuousRep.framedMap_subtype_liftGLOfMem`
* `TauCeti.ContinuousRep.baseChangeOfGLIso_apply`
-/

public section

open Matrix
open scoped TensorProduct Topology

namespace TauCeti.ContinuousRep

section LiftGL

variable {L S ι : Type*} [Field L] [SetLike S L] [SubfieldClass S L]
  [Fintype ι] [DecidableEq ι]

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
    have hcomp := LinearMap.congr_fun
      (Matrix.piScalarRight_comp_baseChange_mulVecLin (S := B) (φ g : Matrix ι ι A)) x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply] at hcomp
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, toRepresentation_baseChange,
      Representation.baseChange_apply, hrep, hcomp, coe_toRepresentation, ofFramed_apply,
      coe_framedMap_apply])

/-- Underlying map of `baseChangeOfGLIso` as `TensorProduct.piScalarRight`. -/
@[simp]
theorem baseChangeOfGLIso_apply (φ : Γ →ₜ* GL ι A) (x : B ⊗[A] (ι → A)) :
    baseChangeOfGLIso B φ x = TensorProduct.piScalarRight A B B ι x :=
  (Iso.ofEquiv_apply _ x).trans (Representation.Equiv.mk_apply _ x)

@[simp]
theorem baseChangeOfGLIso_symm_apply (φ : Γ →ₜ* GL ι A) (w : ι → B) :
    (baseChangeOfGLIso B φ).symm w = (TensorProduct.piScalarRight A B B ι).symm w :=
  EquivLike.injective (baseChangeOfGLIso B φ) (by
    rw [Iso.apply_symm_apply, baseChangeOfGLIso_apply]
    exact ((TensorProduct.piScalarRight A B B ι).apply_symm_apply w).symm)

end BaseChangeOfGL

end TauCeti.ContinuousRep
