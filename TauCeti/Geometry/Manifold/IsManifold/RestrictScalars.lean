/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Restricting the scalars of a manifold modelled on its model space

Let `𝕜'` be a normed algebra over `𝕜` and let `E` be a normed space over both fields, compatibly.
A map which is `C^n` over `𝕜'` is `C^n` over `𝕜`, so the `C^n` groupoid of the trivial model
`𝓘(𝕜', E)` is contained in that of `𝓘(𝕜, E)`. Consequently a `C^n` manifold modelled on
`𝓘(𝕜', E)` is, with the same charts, a `C^n` manifold modelled on `𝓘(𝕜, E)`, and every chart of
its maximal atlas over `𝕜'` is a chart of its maximal atlas over `𝕜`.

The groupoid comparison is obtained from Mathlib's `ContDiffOn.restrict_scalars`.

The main example is a complex manifold modelled on `𝓘(ℂ, E)`, which is a real manifold modelled on
`𝓘(ℝ, E)`; its holomorphic charts are real `C^n` charts. This is how real-analytic notions, such as
the real Hessian at a critical point, are applied to complex manifolds.

## Main results

* `TauCeti.contDiffGroupoid_le_restrictScalars`: the `C^n` groupoid over `𝕜'` is contained in the
  `C^n` groupoid over `𝕜`.
* `IsManifold.restrictScalars`: a `C^n` manifold over `𝕜'` is a `C^n` manifold over `𝕜`.
* `IsManifold.maximalAtlas_subset_restrictScalars`: the maximal atlas over `𝕜'` is contained in
  the maximal atlas over `𝕜`.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : WithTop ℕ∞}

/-- The `C^n` groupoid of the trivial model over `𝕜'` is contained in the `C^n` groupoid of the
trivial model over the smaller field `𝕜`. -/
theorem contDiffGroupoid_le_restrictScalars :
    contDiffGroupoid n 𝓘(𝕜', E) ≤ contDiffGroupoid n 𝓘(𝕜, E) := by
  rw [contDiffGroupoid, contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, preimage_id_eq, id_eq, range_id, inter_univ] at hfs ⊢
  exact hfs.restrict_scalars 𝕜

variable (𝕜) in
/-- A `C^n` manifold modelled on `𝓘(𝕜', E)` is a `C^n` manifold modelled on `𝓘(𝕜, E)` with the
same charts. For instance, a complex manifold is a real manifold. -/
theorem _root_.IsManifold.restrictScalars (h : IsManifold 𝓘(𝕜', E) n M) :
    IsManifold 𝓘(𝕜, E) n M :=
  { hasGroupoid_of_le h.toHasGroupoid contDiffGroupoid_le_restrictScalars with }

variable (𝕜) in
/-- Every chart of the `C^n` maximal atlas over `𝕜'` is a chart of the `C^n` maximal atlas over the
smaller field `𝕜`. For instance, a holomorphic chart of a complex manifold is a real `C^n` chart. -/
theorem _root_.IsManifold.maximalAtlas_subset_restrictScalars :
    IsManifold.maximalAtlas 𝓘(𝕜', E) n M ⊆ IsManifold.maximalAtlas 𝓘(𝕜, E) n M :=
  StructureGroupoid.maximalAtlas_mono contDiffGroupoid_le_restrictScalars

end TauCeti
