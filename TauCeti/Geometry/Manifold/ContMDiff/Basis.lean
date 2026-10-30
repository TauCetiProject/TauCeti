/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# `C^n` families of bases

Let `B : M → Basis ι 𝕜 F` be a family of bases of a normed space `F`, indexed by a finite type and
parametrized by a manifold `M`. If every basis vector `B y i` depends `C^n` on `y`, then so do the
frame `(B y).equivFunL.symm : (ι → 𝕜) →L[𝕜] F`, `x ↦ ∑ i, x i • B y i`, and the coordinate map
`(B y).equivFunL : F →L[𝕜] ι → 𝕜`, both in the operator norm. The frame is the image of the vectors
`B y i` under the continuous linear equivalence `ContinuousLinearEquiv.piRing`, and the coordinate
map is its inverse, which depends smoothly on the frame by `contDiffAt_map_inverse`.

These are the smooth counterparts of `Module.Basis.continuous_equivFunL_symm_of_continuous` and
`Module.Basis.continuous_equivFunL_of_continuous`. They give smooth local coordinates adapted to a
smoothly varying basis, as for the period frame of a smooth family of lattices.

## Main results

* `Module.Basis.contMDiffAt_equivFunL_symm_of_contMDiffAt`,
  `Module.Basis.contMDiff_equivFunL_symm_of_contMDiff`: the frame of a `C^n` family of bases
  is `C^n`.
* `Module.Basis.contMDiffAt_equivFunL_of_contMDiffAt`,
  `Module.Basis.contMDiff_equivFunL_of_contMDiff`: the coordinate map of a `C^n` family of bases
  is `C^n`.
-/

public section

open scoped Manifold ContDiff

namespace Module.Basis

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 EM H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} [Fintype ι] {B : M → Basis ι 𝕜 F} {n : WithTop ℕ∞} {y : M}

/-- **Smoothness of a family of frames at a point.** If every vector of a family of bases is `C^n`
at `y` as a function of the parameter, then so is the frame `x ↦ ∑ i, x i • B y i`, in the
operator norm. -/
theorem contMDiffAt_equivFunL_symm_of_contMDiffAt
    (h : ∀ i, ContMDiffAt I 𝓘(𝕜, F) n (fun y ↦ B y i) y) :
    ContMDiffAt I 𝓘(𝕜, (ι → 𝕜) →L[𝕜] F) n
      (fun y ↦ ((B y).equivFunL.symm : (ι → 𝕜) →L[𝕜] F)) y := by
  classical
  -- The frame is the image of its vectors under `(ι → F) ≃L[𝕜] ((ι → 𝕜) →L[𝕜] F)`.
  let e : (ι → F) →L[𝕜] (ι → 𝕜) →L[𝕜] F :=
    (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := F) ι).symm.toContinuousLinearMap
  have hframe : (fun y ↦ ((B y).equivFunL.symm : (ι → 𝕜) →L[𝕜] F)) = fun y ↦ e fun i ↦ B y i := by
    ext1 y
    refine ((ContinuousLinearEquiv.piRing ι).symm_apply_eq.2 ?_).symm
    ext i
    -- `ContinuousLinearEquiv.piRing` has no `apply` lemma; unfold it to `LinearEquiv.piRing`.
    simp [ContinuousLinearEquiv.piRing]
  rw [hframe]
  exact e.contMDiffAt.comp y (contMDiffAt_pi_module_iff.2 h)

/-- **Smoothness of a family of frames.** If every vector of a family of bases depends `C^n` on the
parameter, then so does the frame `x ↦ ∑ i, x i • B y i`, in the operator norm. -/
theorem contMDiff_equivFunL_symm_of_contMDiff (h : ∀ i, ContMDiff I 𝓘(𝕜, F) n fun y ↦ B y i) :
    ContMDiff I 𝓘(𝕜, (ι → 𝕜) →L[𝕜] F) n
      fun y ↦ ((B y).equivFunL.symm : (ι → 𝕜) →L[𝕜] F) :=
  fun y ↦ contMDiffAt_equivFunL_symm_of_contMDiffAt fun i ↦ h i y

/-- **Smoothness of a family of coordinate maps at a point.** If every vector of a family of bases
is `C^n` at `y` as a function of the parameter, then so is the coordinate map `F → ι → 𝕜`, in the
operator norm. -/
theorem contMDiffAt_equivFunL_of_contMDiffAt
    (h : ∀ i, ContMDiffAt I 𝓘(𝕜, F) n (fun y ↦ B y i) y) :
    ContMDiffAt I 𝓘(𝕜, F →L[𝕜] ι → 𝕜) n (fun y ↦ ((B y).equivFunL : F →L[𝕜] ι → 𝕜)) y := by
  -- The coordinate map is the inverse of the frame, and inversion is smooth.
  have hinv : (fun y ↦ ((B y).equivFunL : F →L[𝕜] ι → 𝕜)) =
      ContinuousLinearMap.inverse ∘ fun y ↦ ((B y).equivFunL.symm : (ι → 𝕜) →L[𝕜] F) := by
    ext1 y
    rw [Function.comp_apply, ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.symm_symm]
  rw [hinv]
  exact ContDiffAt.comp_contMDiffAt (contDiffAt_map_inverse (B y).equivFunL.symm)
    (contMDiffAt_equivFunL_symm_of_contMDiffAt h)

/-- **Smoothness of a family of coordinate maps.** If every vector of a family of bases depends
`C^n` on the parameter, then so does the coordinate map `F → ι → 𝕜`, in the operator norm. -/
theorem contMDiff_equivFunL_of_contMDiff (h : ∀ i, ContMDiff I 𝓘(𝕜, F) n fun y ↦ B y i) :
    ContMDiff I 𝓘(𝕜, F →L[𝕜] ι → 𝕜) n fun y ↦ ((B y).equivFunL : F →L[𝕜] ι → 𝕜) :=
  fun y ↦ contMDiffAt_equivFunL_of_contMDiffAt fun i ↦ h i y

end Module.Basis
