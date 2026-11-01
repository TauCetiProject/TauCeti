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

/-- **Criticality under a local diffeomorphism.** If `π` is a `C^n` local diffeomorphism at `x`
with `1 ≤ n`, then `x` is a critical point of `f ∘ π` exactly when `π x` is a critical point of
`f`. -/
theorem _root_.IsLocalDiffeomorphAt.mem_criticalPoints_comp_iff
    (hπ : IsLocalDiffeomorphAt I I n π x) (hn : 1 ≤ n) {f : M' → ℝ} :
    x ∈ criticalPoints I (f ∘ π) ↔ π x ∈ criticalPoints I f := by
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  by_cases hf : MDifferentiableAt I 𝓘(ℝ) f (π x)
  · obtain ⟨e, he, hx, hpt, hcomp⟩ := hπ.exists_mem_maximalAtlas_extend_eventuallyEq
      (IsManifold.chart_mem_maximalAtlas (π x)) (mem_chart_source H (π x))
    rw [mem_criticalPoints, mem_criticalPoints,
      mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
        (IsManifold.maximalAtlas_subset_of_le hn he) hx (hf.comp x (hπ.mdifferentiableAt hn0)),
      mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
        (IsManifold.maximalAtlas_subset_of_le hn (IsManifold.chart_mem_maximalAtlas (π x)))
        (mem_chart_source H (π x)) hf,
      (hcomp f).fderiv_eq, hpt]
  -- Near `π x`, `f` is `f ∘ π` after a local inverse of `π`, so `f ∘ π` is not differentiable at
  -- `x` either, and both derivatives vanish by convention.
  have hfπ : ¬MDifferentiableAt I 𝓘(ℝ) (f ∘ π) x := fun h ↦ hf <|
    (h.comp_of_eq (π x) (hπ.mdifferentiableAt_localInverse hn0)
      (hπ.localInverse_left_inv hπ.localInverse_mem_target)).congr_of_eventuallyEq
      (hπ.localInverse_eventuallyEq_right.fun_comp f).symm
  simp only [mem_criticalPoints_iff_mfderiv_eq_zero, mfderiv_zero_of_not_mdifferentiableAt hf,
    mfderiv_zero_of_not_mdifferentiableAt hfπ]

/-- **Nondegeneracy under a local diffeomorphism.** If `π` is a `C^n` local diffeomorphism at `x`
with `2 ≤ n`, then `x` is a nondegenerate critical point of `f ∘ π` exactly when `π x` is a
nondegenerate critical point of `f`. -/
theorem _root_.IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp_iff
    (hπ : IsLocalDiffeomorphAt I I n π x) (hn : 2 ≤ n) {f : M' → ℝ} :
    IsManifoldNondegenerateCriticalPoint I (f ∘ π) x ↔
      IsManifoldNondegenerateCriticalPoint I f (π x) := by
  have : IsManifold I 2 M := IsManifold.of_le hn
  have : IsManifold I 2 M' := IsManifold.of_le hn
  obtain ⟨e, he, hx, hpt, hcomp⟩ := hπ.exists_mem_maximalAtlas_extend_eventuallyEq
    (IsManifold.chart_mem_maximalAtlas (π x)) (mem_chart_source H (π x))
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
    (hπ.mem_criticalPoints_comp_iff (one_le_two.trans hn)).2 hcrit
  obtain ⟨e, he, hx, hpt, hcomp⟩ := hπ.exists_mem_maximalAtlas_extend_eventuallyEq
    (IsManifold.chart_mem_maximalAtlas (π x)) (mem_chart_source H (π x))
  rw [manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_of_le hn he) hx (hf.comp x (hπ.contMDiffAt.of_le hn))
      (mem_criticalPoints.1 hcrit'),
    manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (π x))
      (mem_chart_source H (π x)) hf (mem_criticalPoints.1 hcrit),
    morseIndex_congr_of_eventuallyEq (hcomp f), hpt]

end TauCeti
