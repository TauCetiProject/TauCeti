/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Finite-dimensionality of a space of linear maps

For vector spaces `M` and `N` over a field, `M →ₗ[K] N` is finite-dimensional when `M` and `N`
are (Mathlib's instance `Module.Finite.linearMap`). Conversely, if `M` and `N` are nonzero and
`M →ₗ[K] N` is finite-dimensional, then so are `M` and `N`: a nonzero functional `φ` on `M`
embeds `N` into `M →ₗ[K] N` by `y ↦ φ(·) y`, and a nonzero vector `y₀` of `N` embeds the dual of
`M` by `ψ ↦ ψ(·) y₀`, whose finiteness gives that of `M` (`Module.finite_dual_iff`).

## Main results

* `Module.finite_linearMap_iff`: for nonzero `M` and `N`, `M →ₗ[K] N` is finite-dimensional if
  and only if `M` and `N` are.
-/

public section

namespace Module

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- **A space of linear maps between nonzero spaces is finite-dimensional exactly when both
spaces are.** The nontriviality hypotheses are needed: `M →ₗ[K] 0` and `0 →ₗ[K] N` are zero
whatever `M` and `N` are. -/
theorem finite_linearMap_iff [Nontrivial M] [Nontrivial N] :
    Module.Finite K (M →ₗ[K] N) ↔ Module.Finite K M ∧ Module.Finite K N := by
  refine ⟨fun _ => ?_, fun ⟨_, _⟩ => inferInstance⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨φ, hφ⟩ := Projective.exists_dual_ne_zero K hx
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : N)
  -- `ψ ↦ ψ(·) y₀` embeds the dual of `M`, and `y ↦ φ(·) y` embeds `N`.
  have hdual : Module.Finite K (Dual K M) :=
    Module.Finite.of_injective (LinearMap.smulRightₗ.flip y₀) fun ψ ψ' h =>
      LinearMap.ext fun x' => smul_left_injective K hy₀ <| by
        simpa only [LinearMap.flip_apply, LinearMap.smulRightₗ_apply,
          LinearMap.smulRight_apply] using LinearMap.congr_fun h x'
  refine ⟨finite_dual_iff K |>.mp hdual,
    Module.Finite.of_injective (LinearMap.smulRightₗ φ) fun y y' h => ?_⟩
  have hx' := LinearMap.congr_fun h x
  simp only [LinearMap.smulRightₗ_apply, LinearMap.smulRight_apply] at hx'
  exact smul_right_injective N hφ hx'

end Module
