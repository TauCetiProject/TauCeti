/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Chart
public import TauCeti.Geometry.Manifold.SymmetricPower.Transition
import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Geometry.Manifold.ChartedSpace

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
* `TauCeti.symOpenPartialHomeomorph_mem_maximalAtlas`: every explicit elementary-symmetric chart
  built from surface charts belongs to the maximal analytic atlas.
* `TauCeti.analyticAt_symChartAt_symm_trans`: the transition between two chosen
  elementary-symmetric charts is analytic, so that analyticity of a map into the symmetric power
  can be checked in any of them (`TauCeti.analyticAt_symChartAt_comp_of_analyticAt`).
* `TauCeti.exists_injective_hasFDerivAt_symChartAt_ofFn`: near a tuple of distinct points, every
  chart of the symmetric power is an analytic function of the product coordinates, with injective
  derivative.
-/

public section

open Filter Topology
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

/-- Every explicit elementary-symmetric chart built from analytic surface charts belongs to the
maximal analytic atlas of the symmetric power. Thus local calculations may use common disjoint
patches rather than the independently chosen preferred charts. -/
theorem symOpenPartialHomeomorph_mem_maximalAtlas {ι : Type*} [Fintype ι]
    (φ : ι → OpenPartialHomeomorph α ℂ) (V : ι → Set α)
    (m : ι → ℕ) (hm : ∑ i, m i = n)
    (hVo : ∀ i, IsOpen (V i)) (hVsub : ∀ i, V i ⊆ (φ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V))
    (e : (Σ i, Fin (m i)) ≃ Fin n) (hq : Nonempty (∀ i, Sym (V i) (m i)))
    (hφ : ∀ i, φ i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 α) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin n → ℂ) ω (Sym α n) := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
  intro D hD
  rw [symChartedSpace_atlas, Set.mem_range] at hD
  obtain ⟨s, rfl⟩ := hD
  obtain ⟨W, p, hp, hWo, hWsub, hWdisj, e', hr, hs⟩ := symChartAt_spec (K := ℂ) s
  rw [hs]
  have hCD := contDiffOn_symOpenPartialHomeomorph_trans φ _ V m hm W p hp hVo hVsub hVdisj
    hWo hWsub hWdisj e e' hq hr fun _ _ i j z hz _ =>
      analyticAt_symm_trans (hφ i) (IsManifold.chart_mem_maximalAtlas _)
        (hVsub i hz.1) (hWsub j hz.2)
  have hDC := contDiffOn_symOpenPartialHomeomorph_trans _ φ W p hp V m hm hWo hWsub hWdisj
    hVo hVsub hVdisj e' e hr hq fun _ _ i j z hz _ =>
      analyticAt_symm_trans (IsManifold.chart_mem_maximalAtlas _) (hφ j)
        (hWsub i hz.1) (hVsub j hz.2)
  constructor
  · constructor
    · simpa only [contDiffPregroupoid, mfld_simps] using hCD
    · simpa only [contDiffPregroupoid, mfld_simps] using hDC
  · constructor
    · simpa only [contDiffPregroupoid, mfld_simps] using hDC
    · simpa only [contDiffPregroupoid, mfld_simps] using hCD

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

/-- Near a tuple `p` of pairwise distinct points, every chart of the symmetric power is a function
of the product coordinates `(φᵢ(wᵢ))ᵢ`, where `φᵢ` is the chart of `α` at `p i`, and this function
is complex analytic at `p`, with injective derivative. -/
theorem exists_injective_hasFDerivAt_symChartAt_ofFn {p : Fin n → α}
    (hinj : Function.Injective p) (s : Sym α n)
    (hs : Sym.ofFn p ∈ (symChartAt (K := ℂ) s).source) :
    ∃ (T : (Fin n → ℂ) → Fin n → ℂ) (T' : (Fin n → ℂ) →L[ℂ] Fin n → ℂ),
      AnalyticAt ℂ T (fun j => chartAt ℂ (p j) (p j)) ∧
      Function.Injective T' ∧ HasFDerivAt T T' (fun j => chartAt ℂ (p j) (p j)) ∧
      ∀ᶠ w in 𝓝 p, symChartAt (K := ℂ) s (Sym.ofFn w) = T fun j => chartAt ℂ (p j) (w j) := by
  -- disjoint coordinate patches around the distinct points `p i`
  obtain ⟨V, hVo, hVsub, hpV, hVdisj⟩ :=
    exists_pairwise_disjoint_isOpen_subset_chartAt_source (H := ℂ) hinj
  have hm : ∑ _i : Fin n, 1 = n := by simp
  set e : (Σ _i : Fin n, Fin 1) ≃ Fin n := Equiv.sigmaUnique (Fin n) fun _ => Fin 1
  have hq : Nonempty (∀ i, Sym ↥(V i) 1) := ⟨fun i => Sym.ofFn fun _ => ⟨p i, hpV i⟩⟩
  -- the chart `C` with one block per point reads a nearby tuple as its negated coordinates
  set C := symOpenPartialHomeomorph (fun i => chartAt ℂ (p i)) V (fun _ => 1) hm hVo hVsub
    hVdisj e hq
  have hC_apply : ∀ᶠ w in 𝓝 p, Sym.ofFn w ∈ C.source ∧
      C (Sym.ofFn w) = -fun j => chartAt ℂ (p j) (w j) :=
    eventually_mem_source_symOpenPartialHomeomorph_ofFn (K := ℂ) hVo hpV hVsub hVdisj hm hq
  obtain ⟨hpC, hCp⟩ := hC_apply.self_of_nhds
  -- the given chart `D` is also elementary-symmetric, so both transitions are analytic
  obtain ⟨W, r, hr, hWo, hWsub, hWdisj, e', hr', hs'⟩ := symChartAt_spec (K := ℂ) s
  set D := symChartAt (K := ℂ) s
  have hpD : Sym.ofFn p ∈ D.source := hs
  rw [hs'] at hpD
  have hT : AnalyticAt ℂ (fun c => D (C.symm c)) (C (Sym.ofFn p)) := by
    rw [hs']
    exact analyticAt_symOpenPartialHomeomorph_transition _ _ V _ hm W r hr hVo hVsub hVdisj
      hWo hWsub hWdisj e e' hq hr' hpC hpD fun i j z hz _ =>
        analyticAt_symm_trans (IsManifold.chart_mem_maximalAtlas _)
          (IsManifold.chart_mem_maximalAtlas _) (hVsub i hz.1) (hWsub j hz.2)
  have hS : AnalyticAt ℂ (fun c => C (D.symm c)) (D (Sym.ofFn p)) := by
    rw [hs']
    exact analyticAt_symOpenPartialHomeomorph_transition _ _ W _ hr V _ hm hWo hWsub hWdisj
      hVo hVsub hVdisj e' e hr' hq hpD hpC fun i j z hz _ =>
        analyticAt_symm_trans (IsManifold.chart_mem_maximalAtlas _)
          (IsManifold.chart_mem_maximalAtlas _) (hWsub i hz.1) (hVsub j hz.2)
  rw [← hs'] at hpD
  set T₀ := fun c => D (C.symm c) with hT₀
  have hT₀' : HasFDerivAt T₀ (fderiv ℂ T₀ (C (Sym.ofFn p))) (C (Sym.ofFn p)) :=
    hT.differentiableAt.hasFDerivAt
  -- the inverse transition is a local left inverse, so the derivative of `T₀` is injective
  have hinjT₀ : Function.Injective (fderiv ℂ T₀ (C (Sym.ofFn p))) := by
    have hST : (fun c => C (D.symm c)) ∘ T₀ =ᶠ[𝓝 (C (Sym.ofFn p))] id := by
      have h₁ : C.target ∈ 𝓝 (C (Sym.ofFn p)) := C.open_target.mem_nhds (C.map_source hpC)
      have h₂ : C.symm ⁻¹' D.source ∈ 𝓝 (C (Sym.ofFn p)) :=
        (C.continuousAt_symm (C.map_source hpC)).preimage_mem_nhds
          (D.open_source.mem_nhds (by rwa [C.left_inv hpC]))
      filter_upwards [h₁, h₂] with c hc₁ hc₂
      simp only [Function.comp_apply, hT₀, D.left_inv hc₂, C.right_inv hc₁, id]
    refine hT₀'.injective_of_eventuallyEq_id
      (g' := fderiv ℂ (fun c => C (D.symm c)) (T₀ (C (Sym.ofFn p)))) ?_ hST
    simpa only [hT₀, C.left_inv hpC] using hS.differentiableAt.hasFDerivAt
  -- compose with the negation, which turns the coordinates of `C` into the product coordinates
  refine ⟨fun c => T₀ (-c), (fderiv ℂ T₀ (C (Sym.ofFn p))).comp (-ContinuousLinearMap.id ℂ _),
    ?_, hinjT₀.comp neg_injective, ?_, ?_⟩
  · refine AnalyticAt.comp (g := T₀) ?_ analyticAt_id.neg
    simpa [hCp] using hT
  · refine HasFDerivAt.comp (g := T₀) _ ?_ (hasFDerivAt_id _).neg
    simpa [hCp] using hT₀'
  · filter_upwards [hC_apply] with w ⟨hw, hCw⟩
    simp only [hT₀, ← hCw, C.left_inv hw]
end TauCeti

end
