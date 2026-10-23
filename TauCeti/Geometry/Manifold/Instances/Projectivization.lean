/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import TauCeti.Analysis.Calculus.ContDiff.FinInsertNth
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Projective space as an analytic manifold

For a nontrivially normed field `𝕜`, the standard affine charts
`Projectivization.affineOpenPartialHomeomorph i` identify the open sets `U_i = {[v] | v i ≠ 0}` of
the projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, with its quotient topology, with the affine space
`Fin n → 𝕜`. Their transition maps divide the homogeneous coordinates `Fin.insertNth i 1 z` by one
of their entries, so they are analytic where defined. Hence these `n + 1` charts form an atlas
making projective space a manifold modelled on `𝓘(𝕜, Fin n → 𝕜)` at every order of smoothness
`r`, including the analytic order `ω`.

Over `ℂ` this is the standard complex manifold structure on complex projective space `ℂℙⁿ`, and
over `ℝ` the standard smooth structure on real projective space `ℝℙⁿ`.

## Main declarations

* `Projectivization.instChartedSpace`: the atlas of standard affine charts.
* `Projectivization.contDiffOn_affineChart_symm_trans`: the transition maps are `C^r` for
  every `r`.
* `Projectivization.instIsManifold`: projective space is a `C^r` manifold for every `r`.
* `Projectivization.contMDiffOn_affineChart` and `Projectivization.contMDiff_affineChart_symm`:
  the affine charts and their inverses are `C^r` maps.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1.
-/

public section

open Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The atlas of projective space consisting of its `n + 1` standard affine charts. -/
noncomputable instance instChartedSpace : ChartedSpace (Fin n → 𝕜) (ℙ 𝕜 (Fin (n + 1) → 𝕜)) where
  atlas := range affineOpenPartialHomeomorph
  chartAt x := affineOpenPartialHomeomorph (exists_mem_affineOpen x).choose
  mem_chart_source x := by
    simpa using (exists_mem_affineOpen x).choose_spec
  chart_mem_atlas _ := mem_range_self _

/-- The charts of the atlas of projective space are exactly its standard affine charts. -/
theorem mem_atlas_iff (e : OpenPartialHomeomorph (ℙ 𝕜 (Fin (n + 1) → 𝕜)) (Fin n → 𝕜)) :
    e ∈ atlas (Fin n → 𝕜) (ℙ 𝕜 (Fin (n + 1) → 𝕜)) ↔ ∃ i, affineOpenPartialHomeomorph i = e :=
  Iff.rfl

/-- Each standard affine chart belongs to the atlas of projective space. -/
theorem affineOpenPartialHomeomorph_mem_atlas (i : Fin (n + 1)) :
    affineOpenPartialHomeomorph i ∈ atlas (Fin n → 𝕜) (ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
  mem_range_self i

/-- The transition maps between the standard affine charts of projective space are `C^r` for
every `r`, including the analytic order `ω`. -/
theorem contDiffOn_affineChart_symm_trans (i j : Fin (n + 1)) (r : ℕ∞ω) :
    ContDiffOn 𝕜 r ((affineChart i).symm.trans (affineChart j))
      ((affineChart (K := 𝕜) i).symm.trans (affineChart j)).source := by
  rw [affineChart_symm_trans_source]
  exact (Fin.contDiffOn_insertNth_one_div i j).congr fun z _ ↦ affineChart_symm_trans_apply i j z

/-- Projective space over a nontrivially normed field, with its standard affine charts, is a
`C^r` manifold for every `r`; for `r = ω` it is an analytic manifold. Over `ℂ` this is the
standard complex manifold structure on `ℂℙⁿ`. -/
instance instIsManifold (r : ℕ∞ω) :
    IsManifold 𝓘(𝕜, Fin n → 𝕜) r (ℙ 𝕜 (Fin (n + 1) → 𝕜)) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa using contDiffOn_affineChart_symm_trans i j r

/-- Each standard affine chart of projective space is a `C^r` map on its domain. -/
theorem contMDiffOn_affineChart (i : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (affineChart i) (affineOpen (K := 𝕜) i) := by
  simpa using contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (n := r) (affineOpenPartialHomeomorph_mem_atlas (𝕜 := 𝕜) i))

/-- The inverse `z ↦ [Fin.insertNth i 1 z]` of each standard affine chart of projective space is
a `C^r` map. -/
theorem contMDiff_affineChart_symm (i : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (affineChart (K := 𝕜) i).symm := by
  rw [← contMDiffOn_univ]
  simpa using contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (n := r) (affineOpenPartialHomeomorph_mem_atlas (𝕜 := 𝕜) i))

end Projectivization
