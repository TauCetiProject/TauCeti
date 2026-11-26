/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Derivatives of equivariant maps at fixed points

If a map `φ` fixes a point `x` and `f ∘ φ = ψ ∘ f` near `x`, then the chain rule applied to both
sides shows that the derivatives intertwine as well: `f' ∘ φ' = ψ' ∘ f'`, where `f'`, `φ'` and `ψ'`
are the derivatives of `f` at `x`, of `φ` at `x` and of `ψ` at `f x`
(`HasFDerivAt.comp_eq_comp_of_eventuallyEq`). For instance, the linearization of a map commuting
with a symmetry at a symmetric point commutes with the linearized symmetry, so the symmetry
preserves its kernel and its range. The case `ψ = id`, in which `f` is invariant, is
`HasFDerivAt.comp_eq_of_eventuallyEq`.
-/

public section

open Filter Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Derivatives of equivariant maps.** If `φ` fixes `x` and `f ∘ φ = ψ ∘ f` near `x`, then the
derivative `f'` of `f` at `x` intertwines the derivative `φ'` of `φ` at `x` with the derivative
`ψ'` of `ψ` at `f x`: `f' ∘ φ' = ψ' ∘ f'`. -/
theorem HasFDerivAt.comp_eq_comp_of_eventuallyEq {f : E → F} {f' : E →L[𝕜] F} {φ : E → E}
    {φ' : E →L[𝕜] E} {ψ : F → F} {ψ' : F →L[𝕜] F} {x : E} (hf : HasFDerivAt f f' x)
    (hφ : HasFDerivAt φ φ' x) (hψ : HasFDerivAt ψ ψ' (f x)) (hfix : φ x = x)
    (h : f ∘ φ =ᶠ[𝓝 x] ψ ∘ f) : f'.comp φ' = ψ'.comp f' := by
  have hfφ : HasFDerivAt f f' (φ x) := by rwa [hfix]
  exact (hfφ.comp x hφ).unique ((hψ.comp x hf).congr_of_eventuallyEq h)
