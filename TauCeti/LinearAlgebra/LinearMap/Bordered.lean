/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Bordering a map with a one-dimensional kernel and cokernel

Let `D : M →ₗ[R] N` have kernel the line through `v` and range the kernel of a linear form `φ`.
Choosing `ℓ` with `ℓ v = 1` and `c` with `φ c = 1`, the rank-one correction
`D + ℓ ⊗ c : h ↦ D h + ℓ h • c` is bijective: `φ` recovers `ℓ h` from `D h + ℓ h • c`, which kills
the kernel, and `c` spans a complement of the range. This is the derivative of the chart in a
Lyapunov–Schmidt reduction at a point where the linearization has one-dimensional kernel and
cokernel.

## Main results

* `LinearMap.injective_add_smulRight`: `D + ℓ ⊗ c` is injective when `ker D` is the line through
  `v`, `φ ∘ D = 0`, `ℓ v = 1` and `φ c = 1`.
* `LinearMap.surjective_add_smulRight`: `D + ℓ ⊗ c` is onto when `D v = 0`, `range D = ker φ`,
  `ℓ v = 1` and `φ c = 1`.
* `LinearMap.bijective_add_smulRight`: both together.
-/

public section

namespace LinearMap

open Function

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {D : M →ₗ[R] N} {v : M} {φ : N →ₗ[R] R} {ℓ : M →ₗ[R] R} {c : N}

/-- If the kernel of `D` is the line through `v`, `φ` vanishes on the range of `D`, `ℓ v = 1` and
`φ c = 1`, then `h ↦ D h + ℓ h • c` is injective. -/
theorem injective_add_smulRight (hker : ker D = R ∙ v) (hφ : ∀ y, φ (D y) = 0) (hℓ : ℓ v = 1)
    (hc : φ c = 1) : Injective (D + ℓ.smulRight c) := by
  refine (injective_iff_map_eq_zero _).2 fun h hz ↦ ?_
  rw [LinearMap.add_apply, smulRight_apply] at hz
  have hℓh : ℓ h = 0 := by simpa [hφ, hc] using congrArg φ hz
  have hDh : h ∈ ker D := by simpa [hℓh] using hz
  rw [hker, Submodule.mem_span_singleton] at hDh
  obtain ⟨r, rfl⟩ := hDh
  simp_all

/-- If the range of `D` is the kernel of `φ`, `D v = 0`, `ℓ v = 1` and `φ c = 1`, then
`h ↦ D h + ℓ h • c` is onto. -/
theorem surjective_add_smulRight (hv : D v = 0) (hrange : range D = ker φ) (hℓ : ℓ v = 1)
    (hc : φ c = 1) : Surjective (D + ℓ.smulRight c) := by
  intro z
  obtain ⟨h₀, hh₀⟩ : z - φ z • c ∈ range D := by
    rw [hrange, mem_ker]
    simp [hc]
  refine ⟨h₀ + (φ z - ℓ h₀) • v, ?_⟩
  rw [LinearMap.add_apply, smulRight_apply]
  simp only [map_add, map_smul, hv, smul_zero, add_zero, hh₀, hℓ,
    smul_eq_mul, mul_one, add_sub_cancel, sub_add_cancel]

/-- **Bordering a map with one-dimensional kernel and cokernel.** If the kernel of `D` is the line
through `v`, the range of `D` is the kernel of `φ`, `ℓ v = 1` and `φ c = 1`, then
`h ↦ D h + ℓ h • c` is bijective. -/
theorem bijective_add_smulRight (hker : ker D = R ∙ v) (hrange : range D = ker φ)
    (hℓ : ℓ v = 1) (hc : φ c = 1) : Bijective (D + ℓ.smulRight c) :=
  ⟨injective_add_smulRight hker (fun y ↦ mem_ker.1 (hrange ▸ mem_range_self D y)) hℓ hc,
    surjective_add_smulRight (mem_ker.1 (hker ▸ Submodule.mem_span_singleton_self v)) hrange hℓ
      hc⟩

end LinearMap
