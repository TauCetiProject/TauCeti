/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.FinInsertNth
public import TauCeti.Topology.ComplexProjectiveSpace.Charts
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The standard complex manifold structure on complex projective space

The homogeneous-ratio charts on the circle quotient of the unit sphere form the standard
complex atlas on `ComplexProjectiveSpace n`. Their transition maps are ratios of affine coordinate
functions with a nonzero denominator, hence holomorphic. This construction uses only the sphere
quotient and its explicit homogeneous-coordinate charts.

These charts provide the usual complex structure with which to compare realizations of the
projective-space fan.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.ComplexProjectiveSpace

noncomputable section

variable {n : ℕ}

/-- The standard atlas consists of the `n + 1` homogeneous-ratio charts. -/
instance instChartedSpace : ChartedSpace (Fin n → ℂ) (ComplexProjectiveSpace n) where
  atlas := range affineChart
  chartAt p := affineChart (exists_mem_affineOpen p).choose
  mem_chart_source p := by
    simpa only [affineChart_source] using (exists_mem_affineOpen p).choose_spec
  chart_mem_atlas p := mem_range_self _

/-- Membership in the standard projective atlas means being a homogeneous-ratio chart. -/
@[simp]
theorem mem_atlas_iff (e : OpenPartialHomeomorph (ComplexProjectiveSpace n) (Fin n → ℂ)) :
    e ∈ atlas (Fin n → ℂ) (ComplexProjectiveSpace n) ↔ ∃ k, affineChart k = e :=
  Iff.rfl

/-- Homogeneous-ratio transitions are holomorphic wherever the new denominator is nonzero. -/
theorem contDiffOn_affineChart_transition (k l : Fin (n + 1)) (r : ℕ∞ω) :
    ContDiffOn ℂ r ((affineChart k).symm.trans (affineChart l))
      ((affineChart k).symm.trans (affineChart l)).source := by
  refine (contDiffOn_finInsertNth_one_div k l).mono (fun z hz ↦ ?_) |>.congr
    fun z _ ↦ funext (affineChart_transition k l z)
  apply (affineParam_mem_affineOpen_iff k l z).1
  simpa only [OpenPartialHomeomorph.symm_symm, Set.mem_preimage,
    affineChart_symm_apply, affineChart_source] using hz.2

/-- Complex projective space with its standard homogeneous-coordinate atlas is a complex
manifold, at every differentiability order. -/
instance instIsManifold (r : ℕ∞ω) :
    IsManifold 𝓘(ℂ, Fin n → ℂ) r (ComplexProjectiveSpace n) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨k, rfl⟩ := (mem_atlas_iff e).1 he
  obtain ⟨l, rfl⟩ := (mem_atlas_iff e').1 he'
  simpa using contDiffOn_affineChart_transition k l r

/-- Each homogeneous-ratio chart is holomorphic on its affine open. -/
theorem contMDiffOn_affineChart (k : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) r (affineChart k) (affineOpen k) := by
  rw [← affineChart_source k]
  exact contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas ((mem_atlas_iff _).2 ⟨k, rfl⟩))

/-- The inverse of each homogeneous-ratio chart is holomorphic. -/
theorem contMDiff_affineChart_symm (k : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) r (affineChart k).symm := by
  rw [← contMDiffOn_univ, ← affineChart_target k]
  exact contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas ((mem_atlas_iff _).2 ⟨k, rfl⟩))

end

end TauCeti.ComplexProjectiveSpace
