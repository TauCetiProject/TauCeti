/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite-dimensional normed spaces

Over a complete nontrivially normed field every linear functional on a finite-dimensional normed
space is continuous, so the continuous dual `E →L[𝕜] 𝕜` coincides with the algebraic dual
`Module.Dual 𝕜 E`. Mathlib records that coincidence as the linear equivalence
`LinearMap.toContinuousLinearMap`; this file reads off the one consequence of it that dimension
counts need, namely that the continuous dual has the same dimension as the space.

Two complements of the same space in a finite-dimensional space are continuously linearly
isomorphic. This allows pointwise choices of complements to be identified with a single model.

## Main results

* `ContinuousLinearMap.dual_finrank_eq`: in finite dimensions the continuous dual has the same
  dimension as the space.
* `TauCeti.nonempty_continuousLinearEquiv_of_prod_continuousLinearEquiv`: complements of
  the same space in a finite-dimensional space are isomorphic.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- In finite dimensions the continuous dual `E →L[𝕜] 𝕜` has the same dimension as `E`: every
linear functional on a finite-dimensional space is continuous, so the continuous dual coincides
with the algebraic one. -/
theorem _root_.ContinuousLinearMap.dual_finrank_eq :
    Module.finrank 𝕜 (E →L[𝕜] 𝕜) = Module.finrank 𝕜 E := by
  rw [← LinearEquiv.finrank_eq
    (LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] E →L[𝕜] 𝕜)]
  exact Subspace.dual_finrank_eq

/-- Over a complete field, two complements of the same space `V` in a finite-dimensional space `W`
are continuously linearly isomorphic: both have dimension `finrank W - finrank V`. -/
theorem nonempty_continuousLinearEquiv_of_prod_continuousLinearEquiv {V W F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [AddCommGroup W] [TopologicalSpace W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 W] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (e : (V × F) ≃L[𝕜] W) (e' : (V × F') ≃L[𝕜] W) : Nonempty (F ≃L[𝕜] F') := by
  have : FiniteDimensional 𝕜 (V × F) := e.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional 𝕜 (V × F') := e'.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional 𝕜 F :=
    .of_injective (LinearMap.inr 𝕜 V F) LinearMap.inr_injective
  have : FiniteDimensional 𝕜 F' :=
    .of_injective (LinearMap.inr 𝕜 V F') LinearMap.inr_injective
  have : FiniteDimensional 𝕜 V :=
    .of_injective (LinearMap.inl 𝕜 V F) LinearMap.inl_injective
  apply FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
  have h := e.toLinearEquiv.finrank_eq.trans e'.toLinearEquiv.finrank_eq.symm
  rw [Module.finrank_prod, Module.finrank_prod] at h
  omega

end TauCeti

end
