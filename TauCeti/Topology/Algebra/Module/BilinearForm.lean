/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Analysis.Normed.Module.FiniteDimension

/-!
# Nondegeneracy of the bilinear form of a continuous linear map into the dual

A continuous linear map `L : E →L[𝕜] E →L[𝕜] 𝕜` carries a bilinear form
`ContinuousLinearMap.toBilinForm L`, and that form is left-separating exactly when `L` is
injective: both say that no nonzero vector is annihilated by `L`. Reading nondegeneracy of the
form off injectivity of the map is the step that connects the two ways a Hessian is presented —
as a map into the dual space and as a bilinear form — and it has nothing to do with the analysis
that produces the Hessian, so it is recorded here, next to `ContinuousLinearMap.toBilinForm`
itself, rather than with any of its users.

## Main results

* `ContinuousLinearMap.separatingLeft_toBilinForm_iff_injective`: the bilinear form of a
  continuous linear map into the dual is left-separating if and only if the map is injective.
* `ContinuousLinearMap.isInvertible_of_injective` and
  `ContinuousLinearMap.isInvertible_of_surjective`: in finite dimensions an injective, equivalently
  a surjective, map into the dual is already invertible, the dual having the same dimension as the
  space (`ContinuousLinearMap.finrank_dual_eq`).
-/

public section

namespace TauCeti

section

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- The bilinear form of a continuous linear map into the dual space is left-separating exactly
when the map is injective. -/
theorem _root_.ContinuousLinearMap.separatingLeft_toBilinForm_iff_injective (L : E →L[𝕜] E →L[𝕜] 𝕜)
    :
    L.toBilinForm.SeparatingLeft ↔ Function.Injective L := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ⟨fun h v w hvw ↦ h (LinearMap.ext fun u ↦ by simp [hvw]),
    fun h v w hvw ↦ h (ContinuousLinearMap.ext fun u ↦ by simpa using LinearMap.congr_fun hvw u)⟩

end

section FiniteDimensional

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {L : E →L[𝕜] E →L[𝕜] 𝕜}

/-- In finite dimensions an injective continuous linear map into the dual is invertible: injectivity
makes it a linear equivalence onto its range, and the dual has the same finite dimension as the
space, so that range is everything. -/
theorem _root_.ContinuousLinearMap.isInvertible_of_injective
    (hinj : Function.Injective L) : L.IsInvertible :=
  ⟨((L : E →ₗ[𝕜] E →L[𝕜] 𝕜).linearEquivOfInjective hinj
      ContinuousLinearMap.finrank_dual_eq.symm).toContinuousLinearEquiv, by ext v; simp⟩

/-- In finite dimensions a surjective continuous linear map into the dual is invertible: the dual
has the same finite dimension as the space, so surjectivity forces injectivity. -/
theorem _root_.ContinuousLinearMap.isInvertible_of_surjective
    (hsurj : Function.Surjective L) : L.IsInvertible :=
  ContinuousLinearMap.isInvertible_of_injective
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (V₂ := E →L[𝕜] 𝕜)
      ContinuousLinearMap.finrank_dual_eq.symm (f := (L : E →ₗ[𝕜] E →L[𝕜] 𝕜))).2 hsurj)

end FiniteDimensional

end TauCeti

end
