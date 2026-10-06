/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Chart
public import TauCeti.Geometry.Manifold.SymmetricPower.Transition

/-!
# The symmetric power of a complex curve is a complex analytic manifold

Let `α` be a Hausdorff one-dimensional complex manifold, a Riemann surface in the case of interest.
Its `n`-th symmetric power `Sym α n` carries the elementary-symmetric charted structure
`TauCeti.symChartedSpace`, modelled on `Fin n → ℂ`. Its charts are the explicit charts
`TauCeti.symOpenPartialHomeomorph`, built from disjoint coordinate patches of `α` around the
distinct points of a tuple, and the transition between any two of them is analytic on its source
(`TauCeti.contDiffOn_symOpenPartialHomeomorph_trans`), because the changes of coordinate on `α`
are (`TauCeti.analyticAt_symm_trans`). Hence `Sym α n` is an analytic manifold: this
is the complex structure of `Sym^g(Σ)` in Ozsváth–Szabó, *Holomorphic disks and topological
invariants for closed three-manifolds*
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206)), §2.2, given there by the observation
that the elementary symmetric functions of local coordinates are holomorphic coordinates on the
symmetric power.

The statement is phrased with the explicit charted structure `TauCeti.symChartedSpace`, which is
deliberately not an instance; see its docstring.

## Main declarations

* `TauCeti.isManifold_symChartedSpace`: the symmetric power of a Hausdorff complex curve is a
  complex analytic manifold for its elementary-symmetric charts.
* `TauCeti.analyticAt_symChartAt_symm_trans`: the transition between two chosen
  elementary-symmetric charts is analytic, so that analyticity of a map into the symmetric power
  can be checked in any of them (`TauCeti.analyticAt_symChartAt_comp_of_analyticAt`).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace ℂ α] [IsManifold 𝓘(ℂ) 1 α]
  {n : ℕ}

/-- **The symmetric power of a complex curve is a complex analytic manifold.** For a Hausdorff
one-dimensional complex manifold `α`, the elementary-symmetric charts of `Sym α n` have analytic
transition maps, so `TauCeti.symChartedSpace` makes `Sym α n` an analytic manifold modelled on
`Fin n → ℂ`. -/
theorem isManifold_symChartedSpace :
    @IsManifold ℂ _ (Fin n → ℂ) _ _ (Fin n → ℂ) _ 𝓘(ℂ, Fin n → ℂ) ω (Sym α n) _
      symChartedSpace := by
  refine @isManifold_of_contDiffOn ℂ _ (Fin n → ℂ) _ _ (Fin n → ℂ) _ 𝓘(ℂ, Fin n → ℂ) ω (Sym α n) _
    symChartedSpace fun C D hC hD => ?_
  rw [symChartedSpace_atlas, Set.mem_range] at hC hD
  obtain ⟨s, rfl⟩ := hC
  obtain ⟨s', rfl⟩ := hD
  obtain ⟨V, m, hm, hVo, hVsub, hVdisj, e, hq, hs⟩ := symChartAt_spec (K := ℂ) s
  obtain ⟨W, p, hp, hWo, hWsub, hWdisj, e', hr, hs'⟩ := symChartAt_spec (K := ℂ) s'
  rw [hs, hs']
  simp only [mfld_simps]
  exact contDiffOn_symOpenPartialHomeomorph_trans _ _ V m hm W p hp hVo hVsub hVdisj hWo hWsub
    hWdisj e e' hq hr fun _ _ i j z hz _ =>
      analyticAt_symm_trans (IsManifold.chart_mem_maximalAtlas _)
          (IsManifold.chart_mem_maximalAtlas _) (hVsub i hz.1) (hWsub j hz.2)

/-- **The transition between two chosen elementary-symmetric charts is analytic.** For tuples `s`,
`s'` of a complex curve, the change of coordinates from `symChartAt s` to `symChartAt s'` is
analytic at the coordinates of every tuple lying in both chart sources. -/
theorem analyticAt_symChartAt_symm_trans {s s' x : Sym α n}
    (hs : x ∈ (symChartAt (K := ℂ) s).source) (hs' : x ∈ (symChartAt (K := ℂ) s').source) :
    AnalyticAt ℂ (fun c => symChartAt (K := ℂ) s' ((symChartAt (K := ℂ) s).symm c))
      (symChartAt (K := ℂ) s x) := by
  obtain ⟨V, m, hm, hVo, hVsub, hVdisj, e, hq, h⟩ := symChartAt_spec (K := ℂ) s
  obtain ⟨W, p, hp, hWo, hWsub, hWdisj, e', hr, h'⟩ := symChartAt_spec (K := ℂ) s'
  rw [h] at hs ⊢
  rw [h'] at hs' ⊢
  exact analyticAt_symOpenPartialHomeomorph_transition _ _ V m hm W p hp hVo hVsub hVdisj hWo
    hWsub hWdisj e e' hq hr hs hs' fun i j z hz _ =>
      analyticAt_symm_trans (IsManifold.chart_mem_maximalAtlas _)
        (IsManifold.chart_mem_maximalAtlas _) (hVsub i hz.1) (hWsub j hz.2)

/-- **Analyticity of a map into a symmetric power does not depend on the elementary-symmetric
chart.** If `f` is continuous at `w` and its coordinates in the chosen chart at `s` are analytic at
`w`, then so are its coordinates in the chosen chart at any `s'` whose source contains `f w`. -/
theorem analyticAt_symChartAt_comp_of_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → Sym α n} {w : E} {s s' : Sym α n} (hf : ContinuousAt f w)
    (hs : f w ∈ (symChartAt (K := ℂ) s).source) (hs' : f w ∈ (symChartAt (K := ℂ) s').source)
    (ha : AnalyticAt ℂ (fun t => symChartAt (K := ℂ) s (f t)) w) :
    AnalyticAt ℂ (fun t => symChartAt (K := ℂ) s' (f t)) w := by
  refine ((analyticAt_symChartAt_symm_trans hs hs').comp
    (f := fun t => symChartAt (K := ℂ) s (f t)) ha).congr ?_
  filter_upwards [hf.preimage_mem_nhds ((symChartAt (K := ℂ) s).open_source.mem_nhds hs)]
    with t ht
  exact congrArg (symChartAt (K := ℂ) s') ((symChartAt (K := ℂ) s).left_inv ht)

end TauCeti

end
