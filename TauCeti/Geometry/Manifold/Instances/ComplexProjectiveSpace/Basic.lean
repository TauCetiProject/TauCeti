/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.FinInsertNth
public import TauCeti.Topology.ComplexProjectiveSpace.Charts
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# The standard complex manifold structure on complex projective space

The homogeneous-ratio charts on the circle quotient of the unit sphere form the standard
complex atlas on `ComplexProjectiveSpace n`. Their transition maps are ratios of affine coordinate
functions with a nonzero denominator, hence holomorphic. This construction uses only the sphere
quotient and its explicit homogeneous-coordinate charts.

These charts provide the usual complex structure with which to compare realizations of the
projective-space fan. Restricting scalars, the same charts make `ComplexProjectiveSpace n` a real
manifold modelled on `𝓘(ℝ, Fin n → ℂ)`, of every order of smoothness: the smooth structure
underlying its complex structure, in which the charts and their inverses are smooth.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.ComplexProjectiveSpace

noncomputable section

variable {n : ℕ}

/-- The index of the preferred chart at `x`: a homogeneous coordinate `k` of `x` that is nonzero,
chosen by `exists_mem_affineOpen x`, so that `x` lies in the affine open `X_k ≠ 0`. -/
def chartIndex (x : ComplexProjectiveSpace n) : Fin (n + 1) := (exists_mem_affineOpen x).choose

/-- Every point `x` lies in the affine open of its chart index. -/
theorem mem_affineOpen_chartIndex (x : ComplexProjectiveSpace n) : x ∈ affineOpen (chartIndex x) :=
  (exists_mem_affineOpen x).choose_spec

/-- The standard atlas consists of the `n + 1` homogeneous-ratio charts. -/
instance instChartedSpace : ChartedSpace (Fin n → ℂ) (ComplexProjectiveSpace n) where
  atlas := range affineChart
  chartAt p := affineChart (chartIndex p)
  mem_chart_source p := by
    simpa only [affineChart_source] using mem_affineOpen_chartIndex p
  chart_mem_atlas p := mem_range_self _

/-- By the definition of the atlas, the preferred chart at `x` is `affineChart (chartIndex x)`. -/
theorem chartAt_def (x : ComplexProjectiveSpace n) :
    chartAt (Fin n → ℂ) x = affineChart (chartIndex x) :=
  (rfl)

/-- Membership in the standard projective atlas means being a homogeneous-ratio chart. -/
@[simp]
theorem mem_atlas_iff (e : OpenPartialHomeomorph (ComplexProjectiveSpace n) (Fin n → ℂ)) :
    e ∈ atlas (Fin n → ℂ) (ComplexProjectiveSpace n) ↔ ∃ k, affineChart k = e :=
  Iff.rfl

/-- The preferred chart at the point `affineParam k 0`, whose only nonzero homogeneous coordinate is
the coordinate `k`, is the homogeneous-ratio chart `X_k ≠ 0`: it is the only chart containing it. -/
@[simp]
theorem chartAt_affineParam_zero (k : Fin (n + 1)) :
    chartAt (Fin n → ℂ) (affineParam k 0) = affineChart k := by
  have h := mem_affineOpen_chartIndex (affineParam k (0 : Fin n → ℂ))
  rw [affineParam_zero_mem_affineOpen_iff] at h
  rw [chartAt_def, h]

/-- Homogeneous-ratio transitions are holomorphic wherever the new denominator is nonzero. -/
theorem contDiffOn_affineChart_transition (k l : Fin (n + 1)) (r : ℕ∞ω) :
    ContDiffOn ℂ r ((affineChart k).symm.trans (affineChart l))
      ((affineChart k).symm.trans (affineChart l)).source := by
  refine (Fin.contDiffOn_insertNth_one_div k l).mono (fun z hz ↦ ?_) |>.congr
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

/-- With the same homogeneous-ratio charts, complex projective space is a real `C^r` manifold
modelled on `𝓘(ℝ, Fin n → ℂ)`, for every `r`: the smooth structure underlying its complex
structure. -/
instance instIsManifoldReal (r : ℕ∞ω) :
    IsManifold 𝓘(ℝ, Fin n → ℂ) r (ComplexProjectiveSpace n) :=
  (instIsManifold r).restrictScalars ℝ

/-- Each homogeneous-ratio chart lies in the maximal atlas of any `C^r` manifold structure on
complex projective space built on the homogeneous-ratio atlas, such as the complex structure
`𝓘(ℂ, Fin n → ℂ)` or the underlying real structure `𝓘(ℝ, Fin n → ℂ)`. -/
theorem affineChart_mem_maximalAtlas {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 (Fin n → ℂ)] {I : ModelWithCorners 𝕜 (Fin n → ℂ) (Fin n → ℂ)} {r : ℕ∞ω}
    [IsManifold I r (ComplexProjectiveSpace n)] (k : Fin (n + 1)) :
    affineChart k ∈ IsManifold.maximalAtlas I r (ComplexProjectiveSpace n) :=
  IsManifold.subset_maximalAtlas ((mem_atlas_iff _).2 ⟨k, rfl⟩)

/-- The standard affine parametrizations `z ↦ [z₀ : ⋯ : 1 : ⋯ : z_{n-1}]` are `C^r` maps of the
underlying real manifolds, for every `r`. -/
theorem contMDiff_affineParam_real (k : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) r (affineParam (n := n) k) := by
  have h := (contMDiff_affineChart_symm k r).restrictScalars ℝ
  simp only [modelWithCornersSelf_restrictScalars] at h
  exact h.congr fun z ↦ (affineChart_symm_apply k z).symm

/-- The derivative of the parametrization `affineParam k` of the preferred chart `affineChart k`
at `x`, taken at the chart point of `x`, is the identity in the coordinates of that chart. -/
@[simp]
theorem mfderiv_affineParam_chartAt_apply (x : ComplexProjectiveSpace n)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) (chartAt (Fin n → ℂ) x x)) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (affineParam (chartIndex x))
        (chartAt (Fin n → ℂ) x x) v = v := by
  have h := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℂ)) (x := x)
  rw [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at h
  have hf : (extChartAt 𝓘(ℝ, Fin n → ℂ) x).symm = affineParam (chartIndex x) := by
    funext z
    simp [chartAt_def, affineChart_symm_apply]
  rw [hf, extChartAt_coe] at h
  exact congrArg (fun L ↦ L v) h

/-- The parametrization of the preferred chart at `x` sends the chart point of `x` back to `x`. -/
@[simp]
theorem affineParam_chartAt (x : ComplexProjectiveSpace n) :
    affineParam (chartIndex x) (chartAt (Fin n → ℂ) x x) = x := by
  rw [← affineChart_symm_apply, ← chartAt_def]
  exact (chartAt (Fin n → ℂ) x).left_inv (mem_chart_source (Fin n → ℂ) x)

end

end TauCeti.ComplexProjectiveSpace
