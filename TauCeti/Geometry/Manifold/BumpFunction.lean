/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Notation

/-!
# Smooth bump functions on `C^n` manifolds

Mathlib's `SmoothBumpFunction.contMDiff` shows that a smooth bump function on a smooth manifold is
smooth. A smooth bump function is supported in a single chart, where it is a smooth function read
in that chart, so on a `C^n` manifold, `n ≤ ∞`, it is `C^n`
(`SmoothBumpFunction.contMDiff_of_isManifold`). So every neighbourhood of a point `x` of a
finite-dimensional Hausdorff `C^n` manifold contains the topological support of a real `C^n`
function equal to `1` near `x` (`ContMDiffMap.exists_tsupport_subset_eventually_eq_one`).

On a manifold modelled on a real normed space `E` itself, a closed coordinate ball of radius `r'`
inside the preferred chart at `c` carries the bump function with radii `r < r'`
(`SmoothBumpFunction.ofClosedBallSubset`). Read in that chart, every smooth bump function is its
bump function on `E` (`SmoothBumpFunction.apply_chartAt_symm`), supported over the closed
coordinate ball of radius `rOut`
(`SmoothBumpFunction.tsupport_subset_chartAt_symm_image_closedBall`).
-/

public section

open scoped ContDiff Manifold Topology

namespace SmoothBumpFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] {c : M}

/-- A smooth bump function on a `C^n` manifold, `n ≤ ∞`, is `C^n`; Mathlib's
`SmoothBumpFunction.contMDiff` assumes a smooth manifold. -/
theorem contMDiff_of_isManifold {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I n M]
    (ρ : SmoothBumpFunction I c) : CMDiff n ρ := by
  refine contMDiff_of_tsupport fun y hy ↦ ?_
  have hy' := ρ.tsupport_subset_chartAt_source hy
  exact (((ρ.contDiffAt (n := ⊤)).of_le ENat.LEInfty.out).contMDiffAt.comp _
    (contMDiffAt_extChartAt' hy')).congr_of_eventuallyEq
      (ρ.eqOn_source.eventuallyEq_of_mem <| (chartAt H c).open_source.mem_nhds hy')

section Model

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M]

/-- The smooth bump function about `c` with radii `r < r'`, for a closed coordinate ball of radius
`r'` inside the target of the preferred chart at `c`. -/
def ofClosedBallSubset (c : M) {r r' : ℝ} (hr : 0 < r) (hrr' : r < r')
    (hsub : closedBall (chartAt E c c) r' ⊆ (chartAt E c).target) :
    SmoothBumpFunction 𝓘(ℝ, E) c where
  rIn := r
  rOut := r'
  rIn_pos := hr
  rIn_lt_rOut := hrr'
  closedBall_subset := by simpa using hsub

@[simp]
theorem ofClosedBallSubset_rIn (c : M) {r r' : ℝ} (hr : 0 < r) (hrr' : r < r')
    (hsub : closedBall (chartAt E c c) r' ⊆ (chartAt E c).target) :
    (ofClosedBallSubset c hr hrr' hsub).rIn = r := (rfl)

@[simp]
theorem ofClosedBallSubset_rOut (c : M) {r r' : ℝ} (hr : 0 < r) (hrr' : r < r')
    (hsub : closedBall (chartAt E c c) r' ⊆ (chartAt E c).target) :
    (ofClosedBallSubset c hr hrr' hsub).rOut = r' := (rfl)

variable [FiniteDimensional ℝ E] {c : M}

/-- In the preferred chart at `c`, a smooth bump function about `c` is its bump function on the
model space. -/
theorem apply_chartAt_symm (f : SmoothBumpFunction 𝓘(ℝ, E) c) {z : E}
    (hz : z ∈ (chartAt E c).target) :
    f ((chartAt E c).symm z) = f.toContDiffBump z := by
  rw [f.eqOn_source ((chartAt E c).map_target hz)]
  simp [(chartAt E c).right_inv hz]

/-- A smooth bump function about `c` is supported over the closed coordinate ball of radius
`rOut` in the preferred chart at `c`. -/
theorem tsupport_subset_chartAt_symm_image_closedBall [T2Space M]
    (f : SmoothBumpFunction 𝓘(ℝ, E) c) :
    tsupport f ⊆ (chartAt E c).symm '' closedBall (chartAt E c c) f.rOut := by
  simpa using f.tsupport_subset_symm_image_closedBall

end Model

end SmoothBumpFunction

namespace ContMDiffMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M]

/-- On a finite-dimensional Hausdorff `C^n` manifold, `n ≤ ∞`, every neighbourhood `s` of `x`
contains the topological support of a real `C^n` function equal to `1` near `x`. -/
theorem exists_tsupport_subset_eventually_eq_one {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I n M]
    {x : M} {s : Set M} (hs : s ∈ 𝓝 x) :
    ∃ ρ : C^n⟮I, M; ℝ⟯, tsupport ρ ⊆ s ∧ ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  obtain ⟨f, -, hf⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.1 hs
  exact ⟨⟨f, f.contMDiff_of_isManifold⟩, hf, f.eventuallyEq_one⟩

end ContMDiffMap
