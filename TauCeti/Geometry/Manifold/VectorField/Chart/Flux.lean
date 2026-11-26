/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Density-weighted chart fluxes of a vector field

Given a `C²` manifold `M` modeled on `I : ModelWithCorners 𝕜 E H`, a basis `b` of `E`, a scalar
density `ρ : M → 𝕜`, and a vector field `X`, the `i`-th **chart flux** at `α : M` is the scalar
function `E → 𝕜` obtained by taking `ρ` times the `i`-th local-frame coefficient of `X` in the
canonical tangent-bundle trivialization at `α`, read in the extended chart `extChartAt I α` and
extended by zero outside its target.

This module is purely differential-topological (metric-independent) and applies equally to
manifolds with or without boundary.

## Main definitions and results

* `Module.Basis.chartFlux`: the density-weighted chart-frame flux in coordinates, extended by
  zero off the extended chart target.
* `Module.Basis.chartFlux_apply_of_mem` and `Module.Basis.chartFlux_apply_of_notMem`: evaluation
  inside and outside the extended chart target.
* `Module.Basis.chartFlux_eq_zero` and `Module.Basis.chartFlux_eventuallyEq_zero`: vanishing outside
  the chart image of `tsupport X`.
* `Module.Basis.contDiffOn_chartFlux`: `C^k` regularity of `chartFlux` on `range I` when the chart
  image of `tsupport X` is compact and contained in the chart target.
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace Module.Basis

variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- The `i`-th density-weighted flux of a vector field `X` in the extended chart at `α` relative to
a basis `b` of the model space and a scalar density `ρ`, extended by zero off the chart target. -/
noncomputable def chartFlux (b : Module.Basis ι 𝕜 E) (ρ : M → 𝕜) (α : M)
    (X : (x : M) → TangentSpace I x) (i : ι) : E → 𝕜 :=
  (extChartAt I α).target.indicator fun z ↦ ρ ((extChartAt I α).symm z) *
    (trivializationAt E (TangentSpace I) α).localFrameCoeff I b i
      ((extChartAt I α).symm z) (X ((extChartAt I α).symm z))

variable {α : M} {X : (x : M) → TangentSpace I x}

/-- On the extended chart target at `α`, `chartFlux` evaluates to the density times the local-frame
coefficient of `X` at `(extChartAt I α).symm z`.

Not `@[simp]`: Mathlib marks `extChartAt` `@[simp]`, so `simp` unfolds `z ∈ (extChartAt I α).target`
and the `simpNF` linter rejects this lemma with `@[simp]`. -/
theorem chartFlux_apply_of_mem (b : Module.Basis ι 𝕜 E) (ρ : M → 𝕜) (i : ι) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    chartFlux b ρ α X i z = ρ ((extChartAt I α).symm z) *
      (trivializationAt E (TangentSpace I) α).localFrameCoeff I b i
        ((extChartAt I α).symm z) (X ((extChartAt I α).symm z)) := by
  exact indicator_of_mem hz _

/-- Outside the extended chart target at `α`, `chartFlux` vanishes.

Not `@[simp]`: Mathlib marks `extChartAt` `@[simp]`, so `simp` unfolds `z ∉ (extChartAt I α).target`
and the `simpNF` linter rejects this lemma with `@[simp]`. -/
theorem chartFlux_apply_of_notMem (b : Module.Basis ι 𝕜 E) (ρ : M → 𝕜) (i : ι) {z : E}
    (hz : z ∉ (extChartAt I α).target) : chartFlux b ρ α X i z = 0 := by
  exact indicator_of_notMem hz _

/-- The chart flux vanishes outside the chart image of `tsupport X`. -/
theorem chartFlux_eq_zero (b : Module.Basis ι 𝕜 E) (ρ : M → 𝕜) (i : ι) {z : E}
    (hz : z ∉ extChartAt I α '' tsupport (α := E) X) : chartFlux b ρ α X i z = 0 := by
  by_cases ht : z ∈ (extChartAt I α).target
  · have hX0 : X ((extChartAt I α).symm z) = 0 :=
      image_eq_zero_of_notMem_tsupport (α := E) fun h ↦ hz ⟨_, h, (extChartAt I α).right_inv ht⟩
    rw [chartFlux_apply_of_mem b ρ i ht, hX0, map_zero, mul_zero]
  · exact chartFlux_apply_of_notMem b ρ i ht

/-- When the chart image of `tsupport X` is compact, the chart flux vanishes near any point outside
it. -/
theorem chartFlux_eventuallyEq_zero (b : Module.Basis ι 𝕜 E) (ρ : M → 𝕜)
    (hKc : IsCompact (extChartAt I α '' tsupport (α := E) X)) (i : ι) {z : E}
    (hz : z ∉ extChartAt I α '' tsupport (α := E) X) : chartFlux b ρ α X i =ᶠ[𝓝 z] 0 :=
  Filter.eventually_of_mem (hKc.isClosed.isOpen_compl.mem_nhds hz) fun _ h ↦
    chartFlux_eq_zero b ρ i h

/-- When the chart image of `tsupport X` is closed, it contains `tsupport` of each chart flux. -/
theorem tsupport_chartFlux_subset (b : Module.Basis ι 𝕜 E) (ρ : M → 𝕜)
    (hclosed : IsClosed (extChartAt I α '' tsupport (α := E) X)) (i : ι) :
    tsupport (chartFlux b ρ α X i) ⊆ extChartAt I α '' tsupport (α := E) X :=
  closure_minimal (fun _ h ↦ by_contra fun hz ↦ h (chartFlux_eq_zero b ρ i hz)) hclosed

/-- When the chart image of `tsupport X` is compact, each chart flux has compact support. -/
theorem hasCompactSupport_chartFlux (b : Module.Basis ι 𝕜 E) (ρ : M → 𝕜)
    (hKc : IsCompact (extChartAt I α '' tsupport (α := E) X)) (i : ι) :
    HasCompactSupport (chartFlux b ρ α X i) :=
  hKc.of_isClosed_subset isClosed_closure (tsupport_chartFlux_subset b ρ hKc.isClosed i)

/-- When the chart image of `tsupport X` is compact and contained in the chart target, each chart
flux is `C^k` on `range I`. -/
theorem contDiffOn_chartFlux [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] {k : ℕ∞ω}
    [IsManifold I (k + 1) M] (b : Module.Basis ι 𝕜 E) {ρ : M → 𝕜}
    (hρ : ContMDiffOn I 𝓘(𝕜) k ρ (chartAt H α).source)
    (hX : ContMDiffOn I I.tangent k (T% X) (chartAt H α).source)
    (hKc : IsCompact (extChartAt I α '' tsupport (α := E) X))
    (himage : extChartAt I α '' tsupport (α := E) X ⊆ (extChartAt I α).target) (i : ι) :
    ContDiffOn 𝕜 k (chartFlux b ρ α X i) (range I) := by
  have : IsManifold I k M := IsManifold.of_le (n := k + 1) le_self_add
  let _ : ContMDiffVectorBundle k E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro z _
  by_cases hz : z ∈ (extChartAt I α).target
  · have hy : (extChartAt I α).symm z ∈ (chartAt H α).source := by
      rw [← extChartAt_source (I := I)]; exact (extChartAt I α).map_target hz
    have hcoeff := ContMDiffOn.mul
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hρ)
      (contMDiffOn_baseSet_localFrameCoeff (e := trivializationAt E (TangentSpace I) α) b
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hX) i)
    have hg : ContDiffWithinAt 𝕜 k _ (range I) z := contMDiffWithinAt_iff_contDiffWithinAt.1
      ((hcoeff.contMDiffAt
        (by simpa only [TangentBundle.trivializationAt_baseSet] using
          (chartAt H α).open_source.mem_nhds hy)).comp_contMDiffWithinAt z
          (contMDiffWithinAt_extChartAt_symm_range (n := k) α hz))
    exact hg.congr_of_eventuallyEq
      (Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin_of_mem hz) fun _ h ↦
        chartFlux_apply_of_mem b ρ i h) (chartFlux_apply_of_mem b ρ i hz)
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (chartFlux_eventuallyEq_zero b ρ hKc i fun h ↦ hz (himage h))).contDiffWithinAt

end Module.Basis
