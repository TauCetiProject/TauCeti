/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation

/-!
# The adjoint comodule of the general linear group

This file identifies the fixed-module adjoint comodule of `GLₙ` with conjugation on matrices.
It is the comodule-level adapter between the scheme-theoretic representation API and explicit
matrix subspaces.

## Main declaration

* `TauCeti.GeneralLinear.tangentMatrix_adjointComodule_endOfPoint`: the action induced by the
  adjoint comodule becomes `X ↦ g X g⁻¹` under the tangent-matrix equivalence.
-/

public section

open CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u w

noncomputable section

variable {k : Type u} [Field k] {A : Type w} [CommRing A] [Algebra k A]
variable {n : ℕ}

private theorem counitPointsMulEquiv_pointInCounitAlgebra
    (g : HopfAlgebra.points (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A)) :
    counitPointsMulEquiv n
        (Derivation.pointInCounitAlgebra A g) =
      pointsMulEquiv n g := by
  ext i j
  rw [counitPointsMulEquiv_apply, pointsMulEquiv_apply,
    pointToGeneralLinear_apply, Bialgebra.CounitAlgebra.algEquivSelf_apply,
    Derivation.pointInCounitAlgebra_apply]

private theorem pointInCounitAlgebra_map
    {B : Type u} [CommRing B] [Algebra k B] (phi : B →ₐ[k] A)
    (g : HopfAlgebra.points (H := coordinateHopfAlgebra k n) (CommAlgCat.of k B)) :
    AlgHom.mapValue (Bialgebra.CounitAlgebra.mapAlgHom
        (R := k) (A := coordinateHopfAlgebra k n) (B := B) (C := A) phi)
        (Derivation.pointInCounitAlgebra (CommAlgCat.of k B) g) =
      Derivation.pointInCounitAlgebra A (toConv (phi.comp g.ofConv)) := by
  apply WithConv.ofConv_injective
  ext h
  rw [AlgHom.mapValue_apply, Derivation.pointInCounitAlgebra_apply]
  simp only [AlgHom.comp_apply, Bialgebra.CounitAlgebra.mapAlgHom_apply]
  exact congrArg phi (Derivation.pointInCounitAlgebra_apply (CommAlgCat.of k B) g h)

private theorem tangentScalarExtensionEquiv_adjointComodule_endOfPoint
    (g : HopfAlgebra.points (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A))
    (x : A ⊗[k]
      Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    Derivation.tangentScalarExtensionEquiv
        (R := k) (A := coordinateHopfAlgebra k n) (B := A)
        (letI := Derivation.adjointComodule
            (R := k) (H := coordinateHopfAlgebra k n)
         Comodule.endOfPoint
            (Module.Dual k
              (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
            g.ofConv x) =
      Derivation.adDerivation A (Derivation.pointInCounitAlgebra A g)
        (Derivation.tangentScalarExtensionEquiv
          (R := k) (A := coordinateHopfAlgebra k n) (B := A) x) := by
  let H := coordinateHopfAlgebra k n
  let V := Module.Dual k (Bialgebra.CotangentSpace k H)
  let U := ULift.{u} H
  let g₀ : HopfAlgebra.points (H := H) (CommAlgCat.of k U) :=
    toConv ULift.algEquiv.symm.toAlgHom
  let phi : U →ₐ[k] A := g.ofConv.comp ULift.algEquiv.toAlgHom
  let gA : HopfAlgebra.points (H := H) (CommAlgCat.of k A) :=
    toConv (phi.comp g₀.ofConv)
  let : Comodule k H V := Derivation.adjointComodule (R := k) (H := H)
  have hg : gA = g := by
    apply WithConv.ofConv_injective
    ext h
    rfl
  have hone (v : V) :
      Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := A)
          (Comodule.endOfPoint V g.ofConv (1 ⊗ₜ[k] v)) =
        Derivation.adDerivation A (Derivation.pointInCounitAlgebra A g)
          (Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := A)
            (1 ⊗ₜ[k] v)) := by
    have h₀ := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
      (R := k) (H := H) (CommAlgCat.of k U) g₀ (1 ⊗ₜ[k] v)
    have hm := congrArg (Derivation.mapValue phi) h₀
    rw [Derivation.mapValue_tangentScalarExtensionEquiv,
      Derivation.mapValue_adDerivation,
      Derivation.mapValue_tangentScalarExtensionEquiv] at hm
    -- `gA` names this composite point; the equality only folds its local definition.
    rw [pointInCounitAlgebra_map phi g₀,
      ← show gA = toConv (phi.comp g₀.ofConv) from rfl, hg] at hm
    have hn := DFunLike.congr_fun (Comodule.rTensor_comp_endOfPoint V phi g₀.ofConv)
      (1 ⊗ₜ[k] v)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.rTensor_tmul] at hn
    -- Fold the composite algebra map as `gA.ofConv`; `WithConv` preserves its value.
    change LinearMap.rTensor V phi.toLinearMap
        (Comodule.endOfPoint V g₀.ofConv (1 ⊗ₜ[k] v)) =
      Comodule.endOfPoint V gA.ofConv
        (LinearMap.rTensor V phi.toLinearMap (1 ⊗ₜ[k] v)) at hn
    rw [hg] at hn
    -- After naturality, the local aliases `H` and `V` give this tensor-map expression.
    change Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := A)
        (LinearMap.rTensor V phi.toLinearMap
          (Comodule.endOfPoint V g₀.ofConv (1 ⊗ₜ[k] v))) = _ at hm
    rw [hn] at hm
    simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using hm
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      simp only [map_add, hx, hy]
      simpa only [Derivation.adRepresentation_apply] using
        ((Derivation.adRepresentation A (Derivation.pointInCounitAlgebra A g)).map_add
          (Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := A) x)
          (Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := A) y)).symm
  | tmul a v =>
      -- Normalize the tensor coefficient to one to apply `hone`, then restore it by linearity.
      rw [show a ⊗ₜ[k] v = a • (1 ⊗ₜ[k] v) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      rw [map_smul, map_smul, hone, map_smul]
      simpa only [Derivation.adRepresentation_apply, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one] using
        ((Derivation.adRepresentation A (Derivation.pointInCounitAlgebra A g)).map_smul a
          (Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := A)
            (1 ⊗ₜ[k] v))).symm

/-- Under the tangent-matrix equivalence, the point action induced by the adjoint comodule of
`GLₙ` is conjugation on matrices. -/
@[simp] theorem tangentMatrix_adjointComodule_endOfPoint
    (g : HopfAlgebra.points (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A))
    (x : A ⊗[k]
      Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    tangentMatrix n
        (Derivation.tangentScalarExtensionEquiv
          (R := k) (A := coordinateHopfAlgebra k n) (B := A)
          (letI := Derivation.adjointComodule
              (R := k) (H := coordinateHopfAlgebra k n)
           Comodule.endOfPoint
              (Module.Dual k
                (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
              g.ofConv x)) =
      (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) *
        tangentMatrix n
          (Derivation.tangentScalarExtensionEquiv
            (R := k) (A := coordinateHopfAlgebra k n) (B := A) x) *
        ((pointsMulEquiv n g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) A) := by
  have h := tangentScalarExtensionEquiv_adjointComodule_endOfPoint g x
  have hm := congrArg (tangentMatrix n) h
  rw [tangentMatrix_adDerivation,
    counitPointsMulEquiv_pointInCounitAlgebra] at hm
  exact hm

end

end TauCeti.GeneralLinear
