/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import TauCeti.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Reconstructing comodules from actions of a finite coalgebra's dual

For a finite free coalgebra, every algebra action of the convolution dual comes from a
unique right coaction. No finiteness condition is imposed on the module being acted on.
This is the duality used to describe homogeneous polynomial representations as modules
over Schur algebras, the duals of the homogeneous matrix-coordinate coalgebras.

The reconstruction is characterized by contraction with every linear functional, so it
is independent of the finite basis used to construct it.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2, comodules and modules over the dual algebra.
* J. A. Green, *Polynomial Representations of GLₙ*, §2.
-/

public noncomputable section

open scoped TensorProduct
open TensorProduct WithConv

namespace TauCeti.Comodule

variable {R C M : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid M] [Module R M]

private def actionCoact {ι : Type*} [Fintype ι] (b : Module.Basis ι R C)
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) : M →ₗ[R] M ⊗[R] C :=
  ∑ i, (TensorProduct.mk R M C).flip (b i) ∘ₗ ρ (toConv (b.coord i))

private theorem tensorComponent_actionCoact {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R C) (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M)
    (φ : Module.Dual R C) (m : M) :
    LinearMap.tensorComponent φ (actionCoact b ρ m) = ρ (toConv φ) m := by
  classical
  have hφ : (∑ i, φ (b i) • toConv (b.coord i)) = toConv φ := by
    apply WithConv.ofConv_injective
    apply b.ext
    intro j
    simp
  simp only [actionCoact, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, map_sum, LinearMap.tensorComponent_tmul]
  rw [← hφ, map_sum]
  simp

private theorem actionCoact_coassoc {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R C) (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) :
    (TensorProduct.assoc R M C C).toLinearMap ∘ₗ (actionCoact b ρ).rTensor C ∘ₗ
        actionCoact b ρ = Coalgebra.comul.lTensor M ∘ₗ actionCoact b ρ := by
  let := Module.Free.of_basis b
  ext m
  apply (TensorProduct.assoc R M C C).symm.injective
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro ψ
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.tensorComponent_assoc_symm]
  -- The two contractions are the product of the two dual operators.
  have hleft : LinearMap.tensorComponent ψ ((actionCoact b ρ).rTensor C
      (actionCoact b ρ m)) = actionCoact b ρ (ρ (toConv ψ) m) := by
    rw [LinearMap.rTensor_def, LinearMap.tensorComponent_map, LinearMap.comp_id,
      tensorComponent_actionCoact]
  rw [hleft, tensorComponent_actionCoact]
  have hright : LinearMap.tensorComponent φ
      ((LinearMap.tensorComponent ψ).lTensor M
        (Coalgebra.comul.lTensor M (actionCoact b ρ m))) =
      LinearMap.tensorComponent ((toConv φ * toConv ψ).ofConv) (actionCoact b ρ m) := by
    induction actionCoact b ρ m using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x c =>
      simp only [LinearMap.lTensor_tmul, LinearMap.convMul_def, LinearMap.comp_apply,
        LinearMap.tensorComponent_def]
      congr 1
      induction Coalgebra.comul (R := R) c using TensorProduct.inductionOn with
      | add a b ha hb => simp only [map_add, tmul_add, ha, hb]
      | tmul a b => simp [mul_comm]
  rw [hright, tensorComponent_actionCoact, map_mul]
  rfl

variable [Module.Free R C] [Module.Finite R C]

/-- Reconstruct a right coaction from an algebra action of the convolution dual of a
finite free coalgebra. The acted-on module need not be finite or free. -/
@[implicit_reducible]
def ofConvolutionAction
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) : Comodule R C M := by
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex R C)
  let b := Module.Free.chooseBasis R C
  refine ⟨actionCoact b ρ, actionCoact_coassoc b ρ, ?_⟩
  ext m
  apply (TensorProduct.rid R M).injective
  have h := tensorComponent_actionCoact b ρ (Coalgebra.counit (R := R) (A := C)) m
  have h1 : toConv (Coalgebra.counit (R := R) (A := C)) =
      (1 : WithConv (Module.Dual R C)) := by ext c; simp
  rw [h1, map_one] at h
  simpa [LinearMap.tensorComponent_def] using h

/-- Contracting the reconstructed coaction recovers the prescribed dual action. -/
@[simp]
theorem tensorComponent_ofConvolutionAction
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M)
    (φ : Module.Dual R C) (m : M) :
    LinearMap.tensorComponent φ ((ofConvolutionAction ρ).coact m) = ρ (toConv φ) m := by
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex R C)
  exact tensorComponent_actionCoact (Module.Free.chooseBasis R C) ρ φ m

/-- In any finite basis of the coalgebra, reconstruction applies the dual coordinate
operators and tensors their values with the basis vectors. -/
theorem coact_ofConvolutionAction_eq_sum {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R C) (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) (m : M) :
    (ofConvolutionAction ρ).coact m = ∑ i, ρ (toConv (b.coord i)) m ⊗ₜ[R] b i := by
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  rw [tensorComponent_ofConvolutionAction]
  simpa only [actionCoact, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply] using
    (tensorComponent_actionCoact b ρ φ m).symm

/-- The convolution action of the reconstructed comodule is the original algebra action. -/
@[simp]
theorem convolutionAction_ofConvolutionAction
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) :
    (letI := ofConvolutionAction ρ; convolutionAction (R := R) (C := C) (M := M)) = ρ := by
  let := ofConvolutionAction ρ
  ext f m
  rw [convolutionAction_apply, tensorComponent_ofConvolutionAction, toConv_ofConv]

/-- Reconstructing a coaction from its convolution action recovers the original structure. -/
@[simp]
theorem ofConvolutionAction_convolutionAction [σ : Comodule R C M] :
    ofConvolutionAction (convolutionAction (R := R) (C := C) (M := M)) = σ := by
  apply Comodule.ext
  ext m
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  rw [tensorComponent_ofConvolutionAction, convolutionAction_apply, ofConv_toConv]

variable (R C M) in
/-- Right coactions of a finite free coalgebra correspond bijectively to algebra actions of
its convolution dual. This includes arbitrary modules over the finite Schur algebras. -/
def convolutionActionEquiv :
    Comodule R C M ≃ (WithConv (Module.Dual R C) →ₐ[R] Module.End R M) where
  toFun σ := letI := σ; convolutionAction
  invFun := ofConvolutionAction
  left_inv σ := ofConvolutionAction_convolutionAction (σ := σ)
  right_inv := convolutionAction_ofConvolutionAction

/-- The forward equivalence contracts the coaction. -/
@[simp]
theorem convolutionActionEquiv_apply (σ : Comodule R C M) :
    convolutionActionEquiv R C M σ = (letI := σ; convolutionAction) := (rfl)

/-- The inverse equivalence is the reconstructed coaction. -/
@[simp]
theorem convolutionActionEquiv_symm_apply
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) :
    (convolutionActionEquiv R C M).symm ρ = ofConvolutionAction ρ := (rfl)

end TauCeti.Comodule
