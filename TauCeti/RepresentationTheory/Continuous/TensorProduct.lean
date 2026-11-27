/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Basic
public import TauCeti.RepresentationTheory.Continuous.MatrixCoefficient
public import TauCeti.RepresentationTheory.Tensor.External

/-!
# The tensor product of continuous representations

The tensor product of two continuous representations of the same monoid acts by
`g ↦ (π g) ⊗ (ρ g)`, that is, by Mathlib's `TensorProduct.mapL`. This file builds it and proves the
three facts its use requires: the operator-valued action stays continuous, unitarity is preserved,
and the matrix coefficients **multiply**,
`(π ⊗ ρ)_{v ⊗ v', w ⊗ w'} = π_{v,w} · ρ_{v',w'}`.

The last identity is the reason the construction is here: it is what makes the span of the matrix
coefficients of all finite-dimensional representations of `G` closed under multiplication, hence a
subalgebra of `C(G, 𝕜)` rather than only a subspace.

The *external* tensor product `σ ⊠ τ` of a representation `σ` of `G` and a representation `τ` of
another monoid `H` is the representation of `G × H` on `V ⊗[𝕜] W` in which `(g, h)` acts by
`σ g ⊗ τ h`. Forgetting continuity, it is `Representation.externalTensor`. It is again continuous,
respectively unitary, when `σ` and `τ` are. Applied to finite-dimensional kernels and
cokernels, it computes the equivariant index of an external product of operators.

Mathlib's inner product on `V ⊗[𝕜] W` (`TensorProduct.instInnerProductSpace`) is the one for which
`⟪v ⊗ₜ v', w ⊗ₜ w'⟫ = ⟪v, w⟫ * ⟪v', w'⟫`, so no choice is being made here; the same file supplies
`TensorProduct.mapL` with its multiplicativity `TensorProduct.mapL_mul` and its norm bound.

## Main definitions

* `ContRepresentation.tprod`: the tensor product `π ⊗ ρ` of two continuous
  representations.
* `ContRepresentation.externalTensor`: the external tensor product `σ ⊠ τ` of continuous
  representations of two monoids.

## Main statements

* `ContRepresentation.continuous_tprod` and
  `ContRepresentation.IsUnitary.tprod`: the tensor product of continuous representations is
  continuous, and of unitary ones is unitary.
* `ContRepresentation.matrixCoeff_tprod`: matrix coefficients of a tensor product at pure
  tensors are products of matrix coefficients.
* `ContRepresentation.toRepresentation_externalTensor`: forgetting continuity takes the external
  tensor product to `Representation.externalTensor`.
* `ContRepresentation.continuous_externalTensor` and `ContRepresentation.IsUnitary.externalTensor`:
  the external tensor product of continuous representations is continuous, and of unitary ones is
  unitary.

The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open TauCeti

open scoped InnerProductSpace TensorProduct

namespace ContRepresentation

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- **The tensor product of two continuous representations**, acting by `g ↦ (π g) ⊗ (ρ g)`. -/
noncomputable def tprod (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W) :
    ContRepresentation 𝕜 G (V ⊗[𝕜] W) :=
  .ofMonoidHom
    { toFun g := TensorProduct.mapL (π g) (ρ g)
      map_one' := by simp [ContinuousLinearMap.one_def]
      map_mul' g h := by rw [map_mul, map_mul, TensorProduct.mapL_mul] }

variable (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)

omit [TopologicalSpace G] in
/-- The action operators of a tensor product of representations. -/
@[simp]
theorem tprod_apply (g : G) : (tprod π ρ) g = TensorProduct.mapL (π g) (ρ g) :=
  (rfl)

/-- The tensor product of two continuous representations has a continuous operator-valued action:
`mapL` is the composition of two contractions of the separate actions. -/
theorem continuous_tprod (hπ : Continuous π) (hρ : Continuous ρ) :
    Continuous (tprod π ρ) :=
  (lipschitzWith_one_rTensor.continuous.comp hπ).clm_comp
    (lipschitzWith_one_lTensor.continuous.comp hρ)

omit [TopologicalSpace G] in
/-- The tensor product of two unitary representations is unitary: the tensor product of two linear
isometries is a linear isometry. -/
theorem IsUnitary.tprod {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}
    (hπ : IsUnitary π) (hρ : IsUnitary ρ) : IsUnitary (tprod π ρ) :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦ by
    simpa using TensorProduct.norm_map
      (((π g) : V →ₗ[𝕜] V).isometryOfInner (hπ.inner_map_map g))
      (((ρ g) : W →ₗ[𝕜] W).isometryOfInner (hρ.inner_map_map g)) x

/-- **Matrix coefficients multiply under tensor product.** The matrix coefficient of `π ⊗ ρ` at a
pair of pure tensors is the product of the matrix coefficients of `π` and of `ρ`. -/
@[simp]
theorem matrixCoeff_tprod (hπ : Continuous π) (hρ : Continuous ρ) (v w : V) (v' w' : W) :
    matrixCoeff (tprod π ρ) (continuous_tprod π ρ hπ hρ) (v ⊗ₜ[𝕜] v') (w ⊗ₜ[𝕜] w') =
      matrixCoeff π hπ v w * matrixCoeff ρ hρ v' w' := by
  ext g
  simp

end ContRepresentation

namespace ContRepresentation

section External

variable {𝕜 G H V W : Type*} [RCLike 𝕜] [Monoid G] [Monoid H]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- **The external tensor product** `σ ⊠ τ` of a continuous representation `σ` of `G` on `V` and a
continuous representation `τ` of `H` on `W`: the pair `(g, h)` acts on `V ⊗[𝕜] W` by `σ g ⊗ τ h`
(`TensorProduct.mapL`). -/
noncomputable def externalTensor (σ : ContRepresentation 𝕜 G V) (τ : ContRepresentation 𝕜 H W) :
    ContRepresentation 𝕜 (G × H) (V ⊗[𝕜] W) :=
  .ofMonoidHom
    { toFun g := TensorProduct.mapL (σ g.1) (τ g.2)
      map_one' := by simp [ContinuousLinearMap.one_def]
      map_mul' g h := by
        rw [Prod.fst_mul, Prod.snd_mul, map_mul, map_mul, TensorProduct.mapL_mul] }

variable (σ : ContRepresentation 𝕜 G V) (τ : ContRepresentation 𝕜 H W)

/-- The pair `(g, h)` acts on the external tensor product by `σ g ⊗ τ h`. -/
@[simp]
theorem externalTensor_apply (g : G × H) :
    σ.externalTensor τ g = TensorProduct.mapL (σ g.1) (τ g.2) :=
  (rfl)

/-- Forgetting continuity takes the external tensor product of continuous representations to the
external tensor product `Representation.externalTensor` of the underlying representations. -/
theorem toRepresentation_externalTensor :
    (σ.externalTensor τ).toRepresentation =
      σ.toRepresentation.externalTensor τ.toRepresentation := by
  ext g : 1
  refine TensorProduct.ext' fun v w ↦ ?_
  simp [toMonoidHom_apply]

/-- The external tensor product of two continuous representations has a continuous operator-valued
action. -/
theorem continuous_externalTensor [TopologicalSpace G] [TopologicalSpace H] (hσ : Continuous σ)
    (hτ : Continuous τ) : Continuous (σ.externalTensor τ) :=
  (lipschitzWith_one_rTensor.continuous.comp (hσ.comp continuous_fst)).clm_comp
    (lipschitzWith_one_lTensor.continuous.comp (hτ.comp continuous_snd))

/-- The external tensor product of two unitary representations is unitary: the tensor product of
two linear isometries is a linear isometry. -/
theorem IsUnitary.externalTensor {σ : ContRepresentation 𝕜 G V} {τ : ContRepresentation 𝕜 H W}
    (hσ : IsUnitary σ) (hτ : IsUnitary τ) : IsUnitary (σ.externalTensor τ) :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦ by
    simpa using TensorProduct.norm_map
      (((σ g.1) : V →ₗ[𝕜] V).isometryOfInner (hσ.inner_map_map g.1))
      (((τ g.2) : W →ₗ[𝕜] W).isometryOfInner (hτ.inner_map_map g.2)) x

end External

end ContRepresentation
