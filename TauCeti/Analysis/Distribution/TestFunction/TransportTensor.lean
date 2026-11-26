/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import TauCeti.Analysis.Distribution.TestFunction.Prod

/-!
# Transport of tensor products of test functions

Transport of test functions along continuous linear equivalences
(`ContinuousLinearEquiv.transportTestFunctionComplex`) is compatible with tensor products of
complex test functions (`TestFunction.tensor`): transport along a product `e₁ × e₂` of continuous
linear equivalences takes `φ ⊗ ψ` to the tensor product of the transports of `φ` along `e₁` and
of `ψ` along `e₂`. This reduces statements about tensor products on open sets of
finite-dimensional spaces to linear coordinates.

The result lives in its own file so that neither the transport file nor the product file has to
import the other.

## Main declarations

* `ContinuousLinearEquiv.transportTestFunctionComplex_prodCongr_tensor`: transport along a product
  of continuous linear equivalences takes tensor products of complex test functions to tensor
  products.
-/

public section

namespace ContinuousLinearEquiv

open Set TestFunction TopologicalSpace
open scoped Distributions

variable {E E' D D' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup D'] [NormedSpace ℝ D'] {n : ℕ∞} {V : Opens E} {Ω : Opens E'} {O : Opens D}
  {O' : Opens D'} {W : Opens (E × D)} {W' : Opens (E' × D')}

/-- Transport along a product `e₁ × e₂` of continuous linear equivalences takes the tensor product
`φ ⊗ ψ` to the tensor product of the transports of `φ` and `ψ`. -/
theorem transportTestFunctionComplex_prodCongr_tensor (e₁ : E ≃L[ℝ] E') (e₂ : D ≃L[ℝ] D')
    (h₁ : MapsTo e₁ V Ω) (h₂ : MapsTo e₂ O O') (h : MapsTo (e₁.prodCongr e₂) W W')
    (hW : (V : Set E) ×ˢ (O : Set D) ⊆ W) (hW' : (Ω : Set E') ×ˢ (O' : Set D') ⊆ W')
    (φ : 𝓓^{n}(V, ℂ)) (ψ : 𝓓^{n}(O, ℂ)) :
    transportTestFunctionComplex (e₁.prodCongr e₂) h (φ.tensor ψ hW) =
      (transportTestFunctionComplex e₁ h₁ φ).tensor (transportTestFunctionComplex e₂ h₂ ψ) hW' :=
  TestFunction.ext fun _ ↦ by simp

end ContinuousLinearEquiv
