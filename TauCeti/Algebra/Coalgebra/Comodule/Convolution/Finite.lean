/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Basic
public import Mathlib.RingTheory.Finiteness.Projective
import TauCeti.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Reconstructing comodules from actions of a finite coalgebra's dual

For a finite projective coalgebra, every algebra action of the convolution dual comes from a
unique right coaction. No finiteness condition is imposed on the module being acted on.
This is the duality used to describe homogeneous polynomial representations as modules
over Schur algebras, the duals of the homogeneous matrix-coordinate coalgebras.

The reconstruction is characterized by contraction with every linear functional, so it
is independent of the finite dual family used to construct it.

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

private def actionCoact {ι : Type*} [Fintype ι]
    (c : ι → C) (f : ι → Module.Dual R C)
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) : M →ₗ[R] M ⊗[R] C :=
  ∑ i, (TensorProduct.mk R M C).flip (c i) ∘ₗ ρ (toConv (f i))

private theorem tensorComponent_actionCoact {ι : Type*} [Fintype ι]
    (c : ι → C) (f : ι → Module.Dual R C)
    (hf : ∀ φ : Module.Dual R C, ∑ i, φ (c i) • f i = φ)
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M)
    (φ : Module.Dual R C) (m : M) :
    LinearMap.tensorComponent φ (actionCoact c f ρ m) = ρ (toConv φ) m := by
  classical
  have hφ : (∑ i, φ (c i) • toConv (f i)) = toConv φ :=
    WithConv.ofConv_injective (by simpa using hf φ)
  simp only [actionCoact, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, map_sum, LinearMap.tensorComponent_tmul]
  rw [← hφ, map_sum]
  simp

variable [Module.Projective R C]

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
  have hleft : LinearMap.tensorComponent ψ (δ.rTensor C (δ m)) = δ (ρ (toConv ψ) m) := by
    rw [LinearMap.rTensor_def, LinearMap.tensorComponent_map, LinearMap.comp_id, hδ]
  rw [hleft, hδ]
  have hright : LinearMap.tensorComponent φ
      ((LinearMap.tensorComponent ψ).lTensor M (Coalgebra.comul.lTensor M (δ m))) =
      LinearMap.tensorComponent ((toConv φ * toConv ψ).ofConv) (δ m) := by
    rw [← LinearMap.lTensor_comp_apply, LinearMap.lTensor_def,
      LinearMap.tensorComponent_map, LinearMap.id_apply,
      LinearMap.convMul_eq_comp_tensorComponent, ofConv_toConv, ofConv_toConv]
  rw [hright, hδ, toConv_ofConv, map_mul, _root_.mul_apply_eq_comp]

variable [Module.Finite R C]

private theorem exists_actionCoact
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) :
    ∃ δ : M →ₗ[R] M ⊗[R] C,
      ∀ φ m, LinearMap.tensorComponent φ (δ m) = ρ (toConv φ) m := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R C
  let b := Pi.basisFun R (Fin n)
  have hf (φ : Module.Dual R C) :
      ∑ i, φ (p (b i)) • (b.coord i ∘ₗ s) = φ := by
    ext x
    have hx : p (s x) = x := LinearMap.congr_fun hps x
    have h := LinearMap.congr_fun (b.sum_dual_apply_smul_coord (φ ∘ₗ p)) (s x)
    simpa [hx] using h
  exact ⟨actionCoact (fun i => p (b i)) (fun i => b.coord i ∘ₗ s) ρ,
    tensorComponent_actionCoact _ _ hf ρ⟩

/-- Reconstruct a right coaction from an algebra action of the convolution dual of a
finite projective coalgebra. The acted-on module need not be finite or free. -/
@[implicit_reducible]
def ofConvolutionAction
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) : Comodule R C M := by
  let δ := (exists_actionCoact ρ).choose
  have hδ := (exists_actionCoact ρ).choose_spec
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
    LinearMap.tensorComponent φ ((ofConvolutionAction ρ).coact m) = ρ (toConv φ) m := by
  unfold ofConvolutionAction
  exact (exists_actionCoact ρ).choose_spec φ m

/-- In any finite dual family of the coalgebra, reconstruction applies the dual operators
and tensors their values with the corresponding vectors. For a finite basis `b`, take
`c := b`, `f := b.coord` and `hf := b.sum_dual_apply_smul_coord`. -/
theorem coact_ofConvolutionAction_eq_sum {ι : Type*} [Fintype ι]
    (c : ι → C) (f : ι → Module.Dual R C)
    (hf : ∀ φ : Module.Dual R C, ∑ i, φ (c i) • f i = φ)
    (ρ : WithConv (Module.Dual R C) →ₐ[R] Module.End R M) (m : M) :
    (ofConvolutionAction ρ).coact m = ∑ i, ρ (toConv (f i)) m ⊗ₜ[R] c i := by
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  rw [tensorComponent_ofConvolutionAction]
  simpa only [actionCoact, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply] using
    (tensorComponent_actionCoact c f hf ρ φ m).symm

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
