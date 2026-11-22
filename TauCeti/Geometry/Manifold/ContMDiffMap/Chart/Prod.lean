/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation

/-!
# Continuity of pairing in the manifold weak Whitney topology

Pairing `C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯ → C^n⟮I, M; J.prod J', N × N'⟯`,
`(f, g) ↦ (x ↦ (f x, g x))`, is continuous for the weak Whitney topologies, provided the model
of the source is locally compact. Together with the continuity of composition
(`ContMDiffMap.continuous_comp_manifoldWeakWhitney`) this makes pointwise operations continuous:
for a `C^n` map `μ : N × N' → P`, the map `(f, g) ↦ (x ↦ μ (f x, g x))` is continuous. For
instance, pointwise addition of maps into an additive Lie group is continuous.

The proof is local in the source. The chart of `N × N'` at `(y, y')` is the product of the charts
at `y` and `y'` (`extChartAt_prod`), so a coordinate derivative of the pair is the pair of the
coordinate derivatives (`iteratedFDerivWithin_prodMk`). These depend continuously on the maps and
the chart point jointly (`ContMDiffMap.tendsto_iteratedFDerivWithin_extChartAt`), and a
compactness argument over the compact set of a derivative test gives continuity.

## Main results

* `ContMDiffMap.continuous_prodMk_manifoldWeakWhitney`: pairing is jointly continuous.

The weak topology is treated in M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1.
-/

public section

open Set Filter Topology
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N'] [IsManifold J' n N']

omit [LocallyCompactSpace E] in
/-- The coordinate derivatives of a pair of maps, read in the product chart, are the pairs of the
coordinate derivatives. -/
private theorem iteratedFDerivWithin_extChartAt_prodMk (f : C^n⟮I, M; J, N⟯)
    (g : C^n⟮I, M; J', N'⟯) {x : M} {y : N × N'} {w : E} (hw : w ∈ (extChartAt I x).target)
    (hf : f ((extChartAt I x).symm w) ∈ (extChartAt J y.1).source)
    (hg : g ((extChartAt I x).symm w) ∈ (extChartAt J' y.2).source) {m : ℕ} (hm : m ≤ n) :
    iteratedFDerivWithin 𝕜 m (extChartAt (J.prod J') y ∘ f.prodMk g ∘ (extChartAt I x).symm)
        (extChartAt I x).target w =
      ContinuousMultilinearMap.prodL 𝕜 _ F F'
        (iteratedFDerivWithin 𝕜 m (extChartAt J y.1 ∘ f ∘ (extChartAt I x).symm)
          (extChartAt I x).target w,
        iteratedFDerivWithin 𝕜 m (extChartAt J' y.2 ∘ g ∘ (extChartAt I x).symm)
          (extChartAt I x).target w) := by
  have heq : extChartAt (J.prod J') y ∘ f.prodMk g ∘ (extChartAt I x).symm =
      fun v ↦ ((extChartAt J y.1 ∘ f ∘ (extChartAt I x).symm) v,
        (extChartAt J' y.2 ∘ g ∘ (extChartAt I x).symm) v) := by
    rw [extChartAt_prod]
    rfl
  rw [heq, iteratedFDerivWithin_prodMk (f.contDiffWithinAt_extChartAt hw hf)
    (g.contDiffWithinAt_extChartAt hw hg) (uniqueDiffOn_extChartAt_target x) hw hm]
  rfl

/-- The local form of continuity of pairing: a coordinate derivative test passed by the pair of
`f₀` and `g₀` at a chart point is passed near that point by the pair of `f` and `g` for all `f`
near `f₀` and `g` near `g₀`. -/
private theorem eventually_prodMk_mem_source_and_iteratedFDerivWithin_mem
    {f₀ : C^n⟮I, M; J, N⟯} {g₀ : C^n⟮I, M; J', N'⟯} {x : M} {y : N × N'} {w₀ : E}
    (hw₀ : w₀ ∈ (extChartAt I x).target)
    (h₀ : f₀.prodMk g₀ ((extChartAt I x).symm w₀) ∈ (extChartAt (J.prod J') y).source)
    {m : ℕ} (hm : m ≤ n) {V : Set (E [×m]→L[𝕜] (F × F'))}
    (hV : V ∈ 𝓝 (iteratedFDerivWithin 𝕜 m
      (extChartAt (J.prod J') y ∘ f₀.prodMk g₀ ∘ (extChartAt I x).symm)
      (extChartAt I x).target w₀)) :
    ∀ᶠ q : (C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯) × E in
        𝓝 (f₀, g₀) ×ˢ 𝓝[(extChartAt I x).target] w₀,
      q.1.1.prodMk q.1.2 ((extChartAt I x).symm q.2) ∈ (extChartAt (J.prod J') y).source ∧
        iteratedFDerivWithin 𝕜 m
          (extChartAt (J.prod J') y ∘ q.1.1.prodMk q.1.2 ∘ (extChartAt I x).symm)
          (extChartAt I x).target q.2 ∈ V := by
  set φ := extChartAt I x
  -- The source of the product chart is the product of the sources.
  have hsrc (p : N × N') : p ∈ (extChartAt (J.prod J') y).source ↔
      p.1 ∈ (extChartAt J y.1).source ∧ p.2 ∈ (extChartAt J' y.2).source := by
    rw [extChartAt_prod, PartialEquiv.prod_source, mem_prod]
  obtain ⟨hf₀, hg₀⟩ := (hsrc _).1 h₀
  set l := 𝓝 (f₀, g₀) ×ˢ 𝓝[φ.target] w₀
  have hfl : Tendsto (fun q : (C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯) × E ↦ (q.1.1, q.2)) l
      (𝓝 f₀ ×ˢ 𝓝[φ.target] w₀) :=
    ((continuous_fst.tendsto _).comp tendsto_fst).prodMk tendsto_snd
  have hgl : Tendsto (fun q : (C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯) × E ↦ (q.1.2, q.2)) l
      (𝓝 g₀ ×ˢ 𝓝[φ.target] w₀) :=
    ((continuous_snd.tendsto _).comp tendsto_fst).prodMk tendsto_snd
  have hsf := hfl.eventually (eventually_mem_extChartAt_source hw₀ hf₀)
  have hsg := hgl.eventually (eventually_mem_extChartAt_source hw₀ hg₀)
  -- Along `l`, the derivative of the pair is the pair of the derivatives, which converges.
  have hlim := ((ContinuousMultilinearMap.prodL 𝕜 _ F F').continuous.tendsto _).comp
    (((tendsto_iteratedFDerivWithin_extChartAt hw₀ hf₀ hm).comp hfl).prodMk_nhds
      ((tendsto_iteratedFDerivWithin_extChartAt hw₀ hg₀ hm).comp hgl))
  have hpair : ∀ᶠ q in l, ContinuousMultilinearMap.prodL 𝕜 _ F F'
        (iteratedFDerivWithin 𝕜 m (extChartAt J y.1 ∘ q.1.1 ∘ φ.symm) φ.target q.2,
          iteratedFDerivWithin 𝕜 m (extChartAt J' y.2 ∘ q.1.2 ∘ φ.symm) φ.target q.2) =
      iteratedFDerivWithin 𝕜 m (extChartAt (J.prod J') y ∘ q.1.1.prodMk q.1.2 ∘ φ.symm)
        φ.target q.2 := by
    filter_upwards [hsf, hsg, tendsto_snd.eventually self_mem_nhdsWithin] with q h₁ h₂ h₃
    exact (iteratedFDerivWithin_extChartAt_prodMk q.1.1 q.1.2 h₃ h₁ h₂ hm).symm
  rw [iteratedFDerivWithin_extChartAt_prodMk f₀ g₀ hw₀ hf₀ hg₀ hm] at hV
  exact (hsf.and hsg).mono (fun q hq ↦ (hsrc _).2 hq) |>.and
    ((hlim.congr' hpair).eventually_mem hV)

/-- Pairing of `C^n` maps is jointly continuous for the manifold weak Whitney topologies,
provided the model of the source is locally compact. -/
theorem continuous_prodMk_manifoldWeakWhitney :
    Continuous (fun p : C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯ ↦ p.1.prodMk p.2) := by
  refine continuous_iff_continuousAt.mpr fun ⟨f₀, g₀⟩ ↦ ?_
  refine tendsto_manifoldWeakWhitney_iff.mpr fun x y m hm K hK V hV h₀ ↦ ?_
  simp only [mem_chartJetSet]
  -- A compactness argument over `K` reduces the test to a neighbourhood of each of its points.
  refine hK.eventually_forall_of_forall_eventually fun w hw ↦ ?_
  have h := eventually_prodMk_mem_source_and_iteratedFDerivWithin_mem w.property
    ((mem_chartJetSet.mp h₀) w hw).1 hm (hV.mem_nhds ((mem_chartJetSet.mp h₀) w hw).2)
  rw [nhds_prod_eq]
  exact (tendsto_id.prodMap (map_nhds_subtypeVal w).le).eventually h

end ContMDiffMap
