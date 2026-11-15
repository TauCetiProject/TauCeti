/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart

/-!
# Restricting the scalars of `C^n` maps between manifolds

Let `𝕜'` be a normed algebra over `𝕜`, and let `E` and `E'` be normed spaces over both fields,
compatibly. A boundaryless model `I` and its scalar restriction `I.restrictScalars 𝕜` have the same
coordinate maps and use the same charted space. This file shows that a map which is `C^n`
for boundaryless models over `𝕜'` is `C^n` for their scalar restrictions over `𝕜`: in charts,
apply `ContDiffWithinAt.restrict_scalars`. The models need not be trivial, so the same API
applies to products and continuous-linear changes of model.

For the underlying real manifold construction, see Huybrechts, *Complex Geometry*, Chapter 1.

The main example is a holomorphic map between complex manifolds modelled on `𝓘(ℂ, E)` and
`𝓘(ℂ, E')`, which is a smooth map between the underlying real manifolds modelled on `𝓘(ℝ, E)` and
`𝓘(ℝ, E')`.

## Main results

* `ContMDiffWithinAt.restrictScalars`, `ContMDiffAt.restrictScalars`,
  `ContMDiffOn.restrictScalars`, `ContMDiff.restrictScalars`: a `C^n` map over `𝕜'` (within a set,
  at a point, on a set, globally) is `C^n` over `𝕜`.
-/

public section

open Set
open scoped Manifold

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜' E'] [IsScalarTower 𝕜 𝕜' E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜' E H} {I' : ModelWithCorners 𝕜' E' H'}
  [I.Boundaryless] [I'.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}
  {f : M → N} {s : Set M} {x : M}

variable (𝕜)

/-- A map which is `C^n` within a set at a point for the models over `𝕜'` is `C^n` within that set
at that point for the models over the smaller field `𝕜`. -/
theorem ContMDiffWithinAt.restrictScalars (h : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) n f s x := by
  simp only [contMDiffWithinAt_iff, ModelWithCorners.extChartAt_restrictScalars,
    ModelWithCorners.range_eq_univ, inter_univ] at h ⊢
  exact ⟨h.1, h.2.restrict_scalars 𝕜⟩

/-- A map which is `C^n` at a point for the models over `𝕜'` is `C^n` at that point for the models
over the smaller field `𝕜`. -/
theorem ContMDiffAt.restrictScalars (h : ContMDiffAt I I' n f x) :
    ContMDiffAt (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) n f x :=
  contMDiffWithinAt_univ.mp (h.contMDiffWithinAt.restrictScalars 𝕜)

/-- A map which is `C^n` on a set for the models over `𝕜'` is `C^n` on that set for the models over
the smaller field `𝕜`. -/
theorem ContMDiffOn.restrictScalars (h : ContMDiffOn I I' n f s) :
    ContMDiffOn (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) n f s :=
  fun x hx ↦ (h x hx).restrictScalars 𝕜

/-- A `C^n` map for boundaryless models over `𝕜'` is `C^n` for their scalar restrictions
to `𝕜`. For instance, a holomorphic map between complex manifolds is smooth. -/
theorem ContMDiff.restrictScalars (h : ContMDiff I I' n f) :
    ContMDiff (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) n f :=
  fun x ↦ (h x).restrictScalars 𝕜
