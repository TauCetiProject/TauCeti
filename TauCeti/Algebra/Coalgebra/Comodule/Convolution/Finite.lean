/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Basic
public import Mathlib.LinearAlgebra.Contraction
import TauCeti.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Reconstructing comodules from actions of a finite coalgebra's dual

For a finite projective coalgebra, every algebra action of the convolution dual comes from a
unique right coaction. No finiteness condition is imposed on the module being acted on.
This is the duality used to describe homogeneous polynomial representations as modules
over Schur algebras, the duals of the homogeneous matrix-coordinate coalgebras.

The reconstruction uses `dualTensorHomEquiv` and `Module.evalEquiv` and is characterized by
contraction with every linear functional. It admits a formula in any finite dual family.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2, comodules and modules over the dual algebra.
* J. A. Green, *Polynomial Representations of GLₙ*, §2.
-/

public noncomputable section

open scoped TensorProduct
open TensorProduct WithConv

namespace TauCeti.Comodule

variable {R C M : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C]
  [AddCommMonoid M] [Module R M]

variable [Module.Projective R C] [Module.Finite R C]

variable [Coalgebra R C]

private def actionCoact
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) : M →ₗ[R] M ⊗[R] C :=
  let e := TensorProduct.comm R M C ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv R C) (.refl R M) ≪≫ₗ
    dualTensorHomEquiv R (Module.Dual R C) M
  e.symm.toLinearMap ∘ₗ
    (ρ.toLinearMap ∘ₗ (WithConv.linearEquiv R (Module.Dual R C)).symm.toLinearMap).flip

private theorem tensorComponent_actionCoact
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M)
    (φ : Module.Dual R C) (m : M) :
    LinearMap.tensorComponent φ (actionCoact ρ m) = ρ (toConv φ) m := by
  let e := TensorProduct.comm R M C ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv R C) (.refl R M) ≪≫ₗ
    dualTensorHomEquiv R (Module.Dual R C) M
  have he (x : M ⊗[R] C) : e x φ = LinearMap.tensorComponent φ x := by
    induction x using TensorProduct.inductionOn with
    | tmul m c => simp [e]
    | add x y hx hy => simp [hx, hy]
  rw [← he]
  exact congrArg (fun f : Module.Dual R C →ₗ[R] M ↦ f φ) (e.apply_symm_apply _)

omit [Module.Finite R C] in
private theorem actionCoact_coassoc
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M)
    (δ : M →ₗ[R] M ⊗[R] C)
    (hδ : ∀ φ m, LinearMap.tensorComponent φ (δ m) = ρ (toConv φ) m) :
    (TensorProduct.assoc R M C C).toLinearMap ∘ₗ δ.rTensor C ∘ₗ δ =
      Coalgebra.comul.lTensor M ∘ₗ δ := by
  ext m
  apply (TensorProduct.assoc R M C C).symm.injective
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro ψ
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.tensorComponent_assoc_symm]
  -- The two contractions are the product of the two dual operators.
  rw [LinearMap.tensorComponent_rTensor, hδ, hδ]
  simpa [hδ, _root_.mul_apply_eq_comp] using
    (LinearMap.tensorComponent_lTensor_comul (toConv φ) (toConv ψ) (δ m)).symm

/-- Reconstruct a right coaction from an algebra action of the convolution dual of a
finite projective coalgebra. The acted-on module need not be finite or free. -/
@[implicit_reducible]
def ofConvolutionAction
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) : Comodule R C M := by
  let δ := actionCoact ρ
  have hδ := tensorComponent_actionCoact ρ
  refine ⟨δ, actionCoact_coassoc ρ δ hδ, ?_⟩
  ext m
  apply (TensorProduct.rid R M).injective
  have h := hδ (Coalgebra.counit (R := R) (A := C)) m
  rw [← LinearMap.ofConv_one_eq_counit, toConv_ofConv, map_one] at h
  simpa [δ, LinearMap.tensorComponent_def] using h

/-- Contracting the reconstructed coaction recovers the prescribed dual action. -/
@[simp]
theorem tensorComponent_ofConvolutionAction
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M)
    (φ : Module.Dual R C) (m : M) :
    LinearMap.tensorComponent φ ((ofConvolutionAction ρ).coact m) = ρ (toConv φ) m :=
  tensorComponent_actionCoact ρ φ m

/-- In any finite dual family of the coalgebra, reconstruction applies the dual operators
and tensors their values with the corresponding vectors. For a finite basis `b`, take
`c := b`, `f := b.coord` and `hf := b.sum_dual_apply_smul_coord`. -/
theorem coact_ofConvolutionAction_eq_sum {ι : Type*} [Fintype ι]
    (c : ι → C) (f : ι → Module.Dual R C)
    (hf : ∀ φ : Module.Dual R C, ∑ i, φ (c i) • f i = φ)
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) (m : M) :
    (ofConvolutionAction ρ).coact m = ∑ i, ρ (toConv (f i)) m ⊗ₜ[R] c i := by
  classical
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  have hφ : (∑ i, φ (c i) • toConv (f i)) = toConv φ :=
    WithConv.ofConv_injective (by simpa using hf φ)
  rw [tensorComponent_ofConvolutionAction, ← hφ, map_sum]
  simp

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
/-- Right coactions of a finite projective coalgebra correspond bijectively to algebra actions of
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
