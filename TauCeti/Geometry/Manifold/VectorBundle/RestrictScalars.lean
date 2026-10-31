/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
public import TauCeti.Topology.VectorBundle.RestrictScalars

/-!
# Restricting scalars of smooth vector bundles

A `C^n` vector bundle over a manifold modelled on a normed space over a field extension
is a `C^n` vector bundle over the smaller field, with the same fibres and trivialization
atlas. In particular, a holomorphic vector bundle is a smooth real vector bundle on the
underlying real manifold. The result does not require finite rank.

`ContMDiffVectorBundle.restrictScalars` supplies this forgetful operation on Mathlib's
existing mixin, using `VectorBundle.restrictScalars` for its topological vector bundle.
The coordinate changes are identified by
`Bundle.Trivialization.coordChangeL_restrictScalars`. Smoothness follows by composing
the scalar-restricted operator-valued transition function with the continuous linear
map `ContinuousLinearMap.restrictScalarsL`.

The groupoid inclusion `TauCeti.contMDiffFiberwiseLinear_le_restrictScalars` also shows
that every compatible complex-linear bundle chart remains compatible over the smaller
field. It applies to the maximal atlas, rather than only the designated trivializations.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2, for holomorphic
  vector bundles and their underlying smooth bundles.
* Norman Steenrod, *The Topology of Fibre Bundles*, Part I, §§2–3, for linear
  coordinate changes.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

variable {𝕜 𝕜' B EB F : Type*} [NontriviallyNormedField 𝕜]
  [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [NormedSpace 𝕜' EB]
  [IsScalarTower 𝕜 𝕜' EB] [TopologicalSpace B] [ChartedSpace EB B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {n : ℕ∞ω}

namespace TauCeti

/-- Bi-`C^n` fibrewise linear coordinate changes over a field extension remain bi-`C^n`
and fibrewise linear after restricting scalars. -/
theorem contMDiffFiberwiseLinear_le_restrictScalars :
    contMDiffFiberwiseLinear B F 𝓘(𝕜', EB) n ≤
      contMDiffFiberwiseLinear B F 𝓘(𝕜, EB) n := by
  intro e he
  obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := (mem_contMDiffFiberwiseLinear_iff B F 𝓘(𝕜', EB) e).1 he
  let L := ContinuousLinearMap.restrictScalarsL 𝕜' F F 𝕜 𝕜
  refine (mem_contMDiffFiberwiseLinear_iff B F 𝓘(𝕜, EB) e).2
    ⟨fun b ↦ (φ b).restrictScalars 𝕜, U, hU,
      L.contMDiff.comp_contMDiffOn (hφ.restrictScalars 𝕜),
      L.contMDiff.comp_contMDiffOn (h2φ.restrictScalars 𝕜), ?_⟩
  -- Restricting the coefficients changes neither the source nor the underlying function.
  exact ⟨heφ.1, heφ.2⟩

end TauCeti

variable {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, Module 𝕜' (E b)] [∀ b, IsScalarTower 𝕜 𝕜' (E b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle 𝕜' F E]

variable (𝕜) in
/-- A `C^n` vector bundle over a field extension is a `C^n` vector bundle over the
smaller field, on the same fibre bundle. In particular, a holomorphic vector bundle
has an underlying smooth real vector bundle. -/
theorem ContMDiffVectorBundle.restrictScalars
    (h : ContMDiffVectorBundle n F E 𝓘(𝕜', EB)) :
    letI := (inferInstance : VectorBundle 𝕜' F E).restrictScalars 𝕜
    ContMDiffVectorBundle n F E 𝓘(𝕜, EB) := by
  let := (inferInstance : VectorBundle 𝕜' F E).restrictScalars 𝕜
  constructor
  intro e e' _ _
  have hf := (ContinuousLinearMap.restrictScalarsL 𝕜' F F 𝕜 𝕜).contMDiff.comp_contMDiffOn
    ((h.contMDiffOn_coordChangeL e e').restrictScalars 𝕜)
  exact hf.congr fun b _ ↦
    ContinuousLinearMap.ext fun v ↦ DFunLike.congr_fun
      (e.coordChangeL_restrictScalars 𝕜 (S := 𝕜') e' b).symm v
