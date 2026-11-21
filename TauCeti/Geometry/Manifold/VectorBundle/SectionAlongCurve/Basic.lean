/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Coordinates of vector-bundle sections along curves

This file specializes `TauCeti.Manifold.sectionCoord` from
`VectorBundle/SectionAlongMap/Basic.lean` to curves, relating manifold differentiability of the
total-space section to `DifferentiableWithinAt` and `ContDiffWithinAt` regularity of its reading.

## Main results

* `TauCeti.Manifold.differentiableWithinAt_sectionCoord`: a differentiability entry point for
  `sectionCoord` within a parameter set.
* `TauCeti.Manifold.eq_sum_repr_sectionCoord_smul_localFrame`,
  `TauCeti.Manifold.eventually_eq_sum_repr_sectionCoord_smul_localFrame`: pointwise and
  filter-eventually expansion of a section along a curve in a local frame using `sectionCoord`.
* `TauCeti.Manifold.differentiableWithinAt_repr_sectionCoord`,
  `TauCeti.Manifold.differentiableAt_repr_sectionCoord`: differentiability of basis coordinates of
  `sectionCoord`.
* `TauCeti.Manifold.differentiableWithinAt_sectionCoord_sum`: finite sums of sections with
  differentiable readings have differentiable readings.
* `TauCeti.Manifold.contDiffWithinAt_sectionCoord_iff`: the `C^n` coordinate characterization
  for a section along a `C^n` base curve.
-/

public section

open Bundle Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

variable (γ : 𝕜 → M) (W : ∀ t, V (γ t))

/-! ### Local-frame expansion -/

/-- At a parameter where `γ t` lies in the trivialization base set at `x`, `W t` expands in the
local frame of a finite model-fibre basis `b` with coefficients read from `sectionCoord γ W x t`. -/
theorem eq_sum_repr_sectionCoord_smul_localFrame {ι : Type*} [Fintype ι]
    (b : Module.Basis ι 𝕜 F) {x : M} {t : 𝕜}
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    W t = ∑ i, b.repr (sectionCoord 𝕜 (F := F) γ W x t) i •
      (trivializationAt F V x).localFrame b i (γ t) := by
  simpa only [sectionCoord_apply] using
    b.eq_sum_repr_continuousLinearMapAt_smul_localFrame (𝕜 := 𝕜) hx (W t)

/-- Along a filter `l` where `γ` tends to a point `y` in the trivialization base set at `x`, `W`
eventually expands in the local frame of a finite model-fibre basis `b` with coefficients read from
`sectionCoord γ W x`. -/
theorem eventually_eq_sum_repr_sectionCoord_smul_localFrame {ι : Type*} [Fintype ι]
    (b : Module.Basis ι 𝕜 F) {x y : M} {l : Filter 𝕜}
    (hγ : Tendsto γ l (𝓝 y)) (hy : y ∈ (trivializationAt F V x).baseSet) :
    ∀ᶠ r in l, W r = ∑ i, b.repr (sectionCoord 𝕜 (F := F) γ W x r) i •
      (trivializationAt F V x).localFrame b i (γ r) :=
  (hγ.eventually ((trivializationAt F V x).open_baseSet.mem_nhds hy)).mono fun _ hr ↦
    eq_sum_repr_sectionCoord_smul_localFrame γ W b hr

/-! ### Differentiability of the coordinate reading -/

/-- If the coordinate reading `sectionCoord γ W x` is differentiable within `s` at `t`, then each
coordinate function in a model-fibre basis `b` is differentiable within `s` at `t`. -/
theorem differentiableWithinAt_repr_sectionCoord [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    {ι : Type*} (b : Module.Basis ι 𝕜 F) {x : M} {s : Set 𝕜} {t : 𝕜}
    (hW : DifferentiableWithinAt 𝕜 (sectionCoord 𝕜 (F := F) γ W x) s t) (i : ι) :
    DifferentiableWithinAt 𝕜 (fun r ↦ b.repr (sectionCoord 𝕜 (F := F) γ W x r) i) s t :=
  (b.coord i).toContinuousLinearMap.differentiableAt.comp_differentiableWithinAt t hW

/-- If the coordinate reading `sectionCoord γ W x` is differentiable at `t`, then each coordinate
function in a model-fibre basis `b` is differentiable at `t`. -/
theorem differentiableAt_repr_sectionCoord [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    {ι : Type*} (b : Module.Basis ι 𝕜 F) {x : M} {t : 𝕜}
    (hW : DifferentiableAt 𝕜 (sectionCoord 𝕜 (F := F) γ W x) t) (i : ι) :
    DifferentiableAt 𝕜 (fun r ↦ b.repr (sectionCoord 𝕜 (F := F) γ W x r) i) t :=
  (b.coord i).toContinuousLinearMap.differentiableAt.comp t hW

/-- A finite sum of sections along a curve whose coordinate readings are differentiable within
`s` at `t` again has a coordinate reading differentiable within `s` at `t`. -/
theorem differentiableWithinAt_sectionCoord_sum {ι : Type*} {A : Finset ι}
    {U : ι → ∀ t, V (γ t)} {x : M} {s : Set 𝕜} {t : 𝕜}
    (hU : ∀ i ∈ A, DifferentiableWithinAt 𝕜 (sectionCoord 𝕜 (F := F) γ (U i) x) s t) :
    DifferentiableWithinAt 𝕜 (sectionCoord 𝕜 (F := F) γ (fun r ↦ ∑ i ∈ A, U i r) x) s t := by
  rw [sectionCoord_fun_sum]
  exact DifferentiableWithinAt.fun_sum hU

/-- Given a `C^n` base curve, a section along it is `C^n` as a map into the total space if
and only if its coordinate reading in any trivialization containing the base point is `C^n`.
This statement uses the section's original fibre carriers. -/
theorem contDiffWithinAt_sectionCoord_iff {n : ℕ∞ω} {s : Set 𝕜} {x : M} {t : 𝕜}
    [ContMDiffVectorBundle n F V I]
    (hγ : ContMDiffWithinAt 𝓘(𝕜, 𝕜) I n γ s t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    ContDiffWithinAt 𝕜 n (sectionCoord 𝕜 (F := F) γ W x) s t ↔
      ContMDiffWithinAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, F)) n
        (fun r ↦ TotalSpace.mk' F (γ r) (W r)) s t := by
  rw [← contMDiffWithinAt_iff_contDiffWithinAt]
  exact contMDiffWithinAt_sectionCoord_iff γ W hγ hx

/-- A section along a curve which is differentiable within `s` at `t` as a map into the total
space has a differentiable coordinate reading in the canonical trivialization at any point `x`
whose base set contains `γ t`. -/
theorem differentiableWithinAt_sectionCoord {s : Set 𝕜} {x : M} {t : 𝕜}
    [ContMDiffVectorBundle 1 F V I]
    (h : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, F))
      (fun r ↦ TotalSpace.mk' F (γ r) (W r)) s t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    DifferentiableWithinAt 𝕜 (sectionCoord 𝕜 (F := F) γ W x) s t :=
  (mdifferentiableWithinAt_sectionCoord γ W h hx).differentiableWithinAt

/-- A section along a curve which is differentiable at `t` as a map into the total space has a
differentiable coordinate reading in the canonical trivialization at any point `x` whose base set
contains `γ t`. -/
theorem differentiableAt_sectionCoord {x : M} {t : 𝕜} [ContMDiffVectorBundle 1 F V I]
    (h : MDifferentiableAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, F))
      (fun r ↦ TotalSpace.mk' F (γ r) (W r)) t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    DifferentiableAt 𝕜 (sectionCoord 𝕜 (F := F) γ W x) t :=
  (mdifferentiableAt_sectionCoord γ W h hx).differentiableAt

/-- Given a differentiable base curve, differentiability of a section along it is equivalent
to differentiability of its reading in any bundle chart containing the current base point. -/
theorem differentiableAt_sectionCoord_iff {x : M} {t : 𝕜}
    [ContMDiffVectorBundle 1 F V I]
    (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) I γ t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    DifferentiableAt 𝕜 (sectionCoord 𝕜 (F := F) γ W x) t ↔
      MDifferentiableAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, F))
        (fun r ↦ TotalSpace.mk' F (γ r) (W r)) t := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  exact mdifferentiableAt_sectionCoord_iff γ W hγ hx

end TauCeti.Manifold
