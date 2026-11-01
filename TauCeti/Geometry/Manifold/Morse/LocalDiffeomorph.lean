/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# Critical points under local diffeomorphisms

Let `π : M → M'` be a `C^n` local diffeomorphism between boundaryless manifolds with the same
model, and let `f : M' → ℝ`. Near `x`, a chart of `M'` at `π x` composed with `π` is a chart of
the maximal atlas of `M`, and in it the coordinate expression of `f ∘ π` is the coordinate
expression of `f`. Since criticality, nondegeneracy and the Morse index of a `C²` function can be
read in any chart of the maximal atlas, all three are unchanged under composition with `π`.

This is how Morse data is lifted to a covering space: the critical points of `f ∘ π` are the
preimages of those of `f`, with the same nondegeneracy and indices.

## Main results

* `IsLocalDiffeomorphAt.mem_criticalPoints_comp_iff`: `x` is a critical point of `f ∘ π` exactly
  when `π x` is a critical point of `f`.
* `IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp_iff`: the same for
  nondegenerate critical points.
* `IsLocalDiffeomorphAt.manifoldMorseIndex_comp`: at a critical point the Morse index of `f ∘ π`
  at `x` is that of `f` at `π x`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H M'] {n : WithTop ℕ∞} [IsManifold I n M]
  [IsManifold I n M'] {π : M → M'} {x : M}

/-- Near a point `x` where `π` is a local diffeomorphism, the preferred chart of `M'` at `π x`
pulls back to a chart `e` of the maximal atlas of `M` at `x`, in which the coordinate expression of
every `g ∘ π` is the coordinate expression of `g` in that preferred chart. -/
private theorem exists_mem_maximalAtlas_comp_eventuallyEq (hπ : IsLocalDiffeomorphAt I I n π x) :
    ∃ e ∈ IsManifold.maximalAtlas I n M, x ∈ e.source ∧
      e.extend I x = (chartAt H (π x)).extend I (π x) ∧ ∀ g : M' → ℝ,
        (g ∘ π) ∘ (e.extend I).symm =ᶠ[𝓝 (e.extend I x)]
          g ∘ ((chartAt H (π x)).extend I).symm := by
  obtain ⟨e, he, hx, heq⟩ := hπ.exists_mem_maximalAtlas_eventuallyEq
    (IsManifold.chart_mem_maximalAtlas (π x)) (mem_chart_source H (π x))
  set c := chartAt H (π x)
  -- On a neighbourhood of `x`, the extended chart `e` is the extended chart `c` after `π`.
  have hext : ∀ᶠ y in 𝓝 x, y ∈ e.source ∧ π y ∈ c.source ∧ e.extend I y = c.extend I (π y) := by
    filter_upwards [heq, e.open_source.mem_nhds hx, hπ.contMDiffAt.continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds (mem_chart_source H (π x)))] with y hy hye hyc
    exact ⟨hye, hyc, by simp only [OpenPartialHomeomorph.extend_coe, comp_apply, hy]⟩
  refine ⟨e, he, hx, hext.self_of_nhds.2.2, fun g ↦ ?_⟩
  rw [← e.map_extend_nhds_of_boundaryless hx, EventuallyEq, eventually_map]
  filter_upwards [hext] with y ⟨hye, hyc, hy⟩
  simp only [comp_apply, e.extend_left_inv hye]
  rw [hy, c.extend_left_inv hyc]

/-- **Criticality under a local diffeomorphism.** If `π` is a `C^n` local diffeomorphism at `x`
with `1 ≤ n` and `f` is differentiable at `π x`, then `x` is a critical point of `f ∘ π` exactly
when `π x` is a critical point of `f`. -/
theorem _root_.IsLocalDiffeomorphAt.mem_criticalPoints_comp_iff
    (hπ : IsLocalDiffeomorphAt I I n π x) (hn : 1 ≤ n) {f : M' → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ) f (π x)) :
    x ∈ criticalPoints I (f ∘ π) ↔ π x ∈ criticalPoints I f := by
  obtain ⟨e, he, hx, hpt, hcomp⟩ := exists_mem_maximalAtlas_comp_eventuallyEq hπ
  rw [mem_criticalPoints, mem_criticalPoints,
    mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
      (IsManifold.maximalAtlas_subset_of_le hn he) hx
      (hf.comp x (hπ.mdifferentiableAt (zero_lt_one.trans_le hn).ne')),
    mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
      (IsManifold.maximalAtlas_subset_of_le hn (IsManifold.chart_mem_maximalAtlas (π x)))
      (mem_chart_source H (π x)) hf,
    (hcomp f).fderiv_eq, hpt]

/-- **Nondegeneracy under a local diffeomorphism.** If `π` is a `C^n` local diffeomorphism at `x`
with `2 ≤ n`, then `x` is a nondegenerate critical point of `f ∘ π` exactly when `π x` is a
nondegenerate critical point of `f`. -/
theorem _root_.IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp_iff
    (hπ : IsLocalDiffeomorphAt I I n π x) (hn : 2 ≤ n) {f : M' → ℝ} :
    IsManifoldNondegenerateCriticalPoint I (f ∘ π) x ↔
      IsManifoldNondegenerateCriticalPoint I f (π x) := by
  have : IsManifold I 2 M := IsManifold.of_le hn
  have : IsManifold I 2 M' := IsManifold.of_le hn
  obtain ⟨e, he, hx, hpt, hcomp⟩ := exists_mem_maximalAtlas_comp_eventuallyEq hπ
  rw [isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_of_le hn he) hx,
    isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (π x)) (mem_chart_source H (π x)), ← hpt]
  exact ⟨fun h ↦ h.congr_of_eventuallyEq (hcomp f), fun h ↦ h.congr_of_eventuallyEq (hcomp f).symm⟩

/-- **The Morse index under a local diffeomorphism.** If `π` is a `C^n` local diffeomorphism at
`x` with `2 ≤ n`, and `π x` is a critical point of a function `f` which is `C²` there, then the
Morse index of `f ∘ π` at `x` is the Morse index of `f` at `π x`. -/
theorem _root_.IsLocalDiffeomorphAt.manifoldMorseIndex_comp
    (hπ : IsLocalDiffeomorphAt I I n π x) (hn : 2 ≤ n) {f : M' → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f (π x)) (hcrit : π x ∈ criticalPoints I f) :
    manifoldMorseIndex I (f ∘ π) x = manifoldMorseIndex I f (π x) := by
  have : IsManifold I 2 M := IsManifold.of_le hn
  have : IsManifold I 2 M' := IsManifold.of_le hn
  have hcrit' : x ∈ criticalPoints I (f ∘ π) :=
    (hπ.mem_criticalPoints_comp_iff (one_le_two.trans hn) (hf.mdifferentiableAt two_ne_zero)).2
      hcrit
  obtain ⟨e, he, hx, hpt, hcomp⟩ := exists_mem_maximalAtlas_comp_eventuallyEq hπ
  rw [manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_of_le hn he) hx (hf.comp x (hπ.contMDiffAt.of_le hn))
      (mem_criticalPoints.1 hcrit'),
    manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (π x))
      (mem_chart_source H (π x)) hf (mem_criticalPoints.1 hcrit),
    morseIndex_congr_of_eventuallyEq (hcomp f), hpt]

end TauCeti
