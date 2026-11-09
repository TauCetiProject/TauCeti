/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The exterior power as the dual of alternating forms

Let `E` be a finite-dimensional normed space over a complete nontrivially normed field `𝕜`. The
`k`-vectors `⋀[𝕜]^k E` and the continuous alternating `k`-forms `E [⋀^Fin k]→L[𝕜] 𝕜` are dual to
each other: a `k`-vector `ξ` acts on forms by `ω ↦ L_ω ξ`, where `L_ω : ⋀[𝕜]^k E →ₗ[𝕜] 𝕜` is
the linear map induced by `ω`. On a wedge of vectors this is evaluation,
`(v₁ ∧ ⋯ ∧ vₖ)(ω) = ω (v₁, …, vₖ)`. This file packages the pairing as the linear equivalence
`exteriorPower.formDualEquiv` of `⋀[𝕜]^k E` with the native normed dual
`StrongDual 𝕜 (E [⋀^Fin k]→L[𝕜] 𝕜)`.

The equivalence uses no norm on `⋀[𝕜]^k E`. Through it, the dual of the operator norm of forms
becomes a norm on `k`-vectors; on a real inner product space the operator norm of forms is the
comass, and this dual norm is the mass norm of `k`-vectors, which is compared with the inner
product norm in `TauCeti.Analysis.InnerProductSpace.Comass`.

## Main declarations

* `exteriorPower.continuousAlternatingMapLinearEquiv`: continuous alternating maps on `E` are the
  linear maps on `⋀[𝕜]^k E`.
* `exteriorPower.formDualEquiv`: the linear equivalence
  `⋀[𝕜]^k E ≃ₗ[𝕜] StrongDual 𝕜 (E [⋀^Fin k]→L[𝕜] 𝕜)`.
* `exteriorPower.formDualEquiv_ιMulti_apply`: a wedge of vectors evaluates forms.

## References

* H. Federer, *Geometric Measure Theory*, §1.4 and §1.8.
-/

public section

noncomputable section

open Module

namespace exteriorPower

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (k : ℕ)

section ContinuousAlternatingMap

variable (N : Type*) [AddCommGroup N] [Module 𝕜 N] [TopologicalSpace N] [ContinuousAdd N]
  [ContinuousSMul 𝕜 N]

/-- The universal property of `⋀[𝕜]^k E` for continuous alternating maps: on a finite-dimensional
normed space, the continuous alternating `k`-linear maps to `N` are the linear maps
`⋀[𝕜]^k E →ₗ[𝕜] N`. -/
def continuousAlternatingMapLinearEquiv : (E [⋀^Fin k]→L[𝕜] N) ≃ₗ[𝕜] ⋀[𝕜]^k E →ₗ[𝕜] N :=
  AlternatingMap.toContinuousAlternatingMap.symm.trans alternatingMapLinearEquiv

variable {𝕜 E k N}

/-- The linear map on `⋀[𝕜]^k E` induced by a continuous alternating map `f` is the one induced by
`f` as an alternating map. -/
theorem continuousAlternatingMapLinearEquiv_apply (f : E [⋀^Fin k]→L[𝕜] N) :
    continuousAlternatingMapLinearEquiv 𝕜 E k N f =
      alternatingMapLinearEquiv f.toAlternatingMap := by
  simp [continuousAlternatingMapLinearEquiv]

/-- The linear map induced by `f` sends `v₁ ∧ ⋯ ∧ vₖ` to `f (v₁, …, vₖ)`. -/
@[simp]
theorem continuousAlternatingMapLinearEquiv_apply_ιMulti (f : E [⋀^Fin k]→L[𝕜] N)
    (v : Fin k → E) : continuousAlternatingMapLinearEquiv 𝕜 E k N f (ιMulti 𝕜 k v) = f v := by
  simp [continuousAlternatingMapLinearEquiv_apply]

/-- The continuous alternating map induced by a linear map `F` on `⋀[𝕜]^k E` sends `v` to
`F (v₁ ∧ ⋯ ∧ vₖ)`. -/
@[simp]
theorem continuousAlternatingMapLinearEquiv_symm_apply (F : ⋀[𝕜]^k E →ₗ[𝕜] N) (v : Fin k → E) :
    (continuousAlternatingMapLinearEquiv 𝕜 E k N).symm F v = F (ιMulti 𝕜 k v) := by
  rw [← continuousAlternatingMapLinearEquiv_apply_ιMulti, LinearEquiv.apply_symm_apply]

end ContinuousAlternatingMap

/-- The identification of the `k`-vectors `⋀[𝕜]^k E` of a finite-dimensional normed space with the
dual of the continuous alternating `k`-forms: `ξ` acts on a form `ω` through the linear map on
`⋀[𝕜]^k E` induced by `ω`, so that `v₁ ∧ ⋯ ∧ vₖ` evaluates `ω` at `(v₁, …, vₖ)`
(`exteriorPower.formDualEquiv_ιMulti_apply`). -/
def formDualEquiv : ⋀[𝕜]^k E ≃ₗ[𝕜] StrongDual 𝕜 (E [⋀^Fin k]→L[𝕜] 𝕜) :=
  (evalEquiv 𝕜 (⋀[𝕜]^k E)).trans
    ((continuousAlternatingMapLinearEquiv 𝕜 E k 𝕜).dualMap.trans LinearMap.toContinuousLinearMap)

variable {𝕜 E k}

/-- A `k`-vector `ξ` acts on a form `ω` through the linear map on `⋀[𝕜]^k E` induced by `ω`. -/
theorem formDualEquiv_apply (ξ : ⋀[𝕜]^k E) (ω : E [⋀^Fin k]→L[𝕜] 𝕜) :
    formDualEquiv 𝕜 E k ξ ω = continuousAlternatingMapLinearEquiv 𝕜 E k 𝕜 ω ξ := by
  simp [formDualEquiv]

/-- The wedge `v₁ ∧ ⋯ ∧ vₖ` evaluates a form `ω` at `(v₁, …, vₖ)`. -/
@[simp]
theorem formDualEquiv_ιMulti_apply (v : Fin k → E) (ω : E [⋀^Fin k]→L[𝕜] 𝕜) :
    formDualEquiv 𝕜 E k (ιMulti 𝕜 k v) ω = ω v := by
  simp [formDualEquiv_apply]

end exteriorPower
