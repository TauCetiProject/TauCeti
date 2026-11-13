/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation

/-!
# Pairing maps in the manifold weak Whitney topology

Pairing `C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯ → C^n⟮I, M; J.prod J', N × N'⟯`, `(f, g) ↦ (f, g)`,
is continuous for the weak Whitney topologies when the source model is locally compact.

A chart of `N × N'` at a pair of points is the product of the charts of the factors, and a
coordinate derivative of a pair is the pair of the coordinate derivatives
(`iteratedFDerivWithin_prodMk`). Each of these depends continuously on the map and the chart point
jointly (`ContMDiffMap.tendsto_iteratedFDerivWithin_extChartAt`), so a compactness argument over
the compact set of a derivative test gives continuity. Together with
`ContMDiffMap.continuous_comp_manifoldWeakWhitney`, this makes the pointwise application of a
fixed smooth map of several variables continuous.
-/

public section

open Set Filter Topology
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N'] [IsManifold J' n N']
  [LocallyCompactSpace E]

/-- The local form of continuity of pairing: a coordinate derivative test passed by the pair of
`f₀` and `g₀` at a chart point is passed near that point by the pair of `f` and `g`, for all `f`
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
  rw [extChartAt_prod] at h₀ hV ⊢
  set ψ₁ := extChartAt J y.1
  set ψ₂ := extChartAt J' y.2
  have h₁ : f₀ (φ.symm w₀) ∈ ψ₁.source := h₀.1
  have h₂ : g₀ (φ.symm w₀) ∈ ψ₂.source := h₀.2
  -- A coordinate derivative of a pair is the pair of the coordinate derivatives.
  have key (f : C^n⟮I, M; J, N⟯) (g : C^n⟮I, M; J', N'⟯) (w : E) (hw : w ∈ φ.target)
      (hf : f (φ.symm w) ∈ ψ₁.source) (hg : g (φ.symm w) ∈ ψ₂.source) :
      iteratedFDerivWithin 𝕜 m (ψ₁.prod ψ₂ ∘ f.prodMk g ∘ φ.symm) φ.target w =
        (iteratedFDerivWithin 𝕜 m (ψ₁ ∘ f ∘ φ.symm) φ.target w).prod
          (iteratedFDerivWithin 𝕜 m (ψ₂ ∘ g ∘ φ.symm) φ.target w) :=
    iteratedFDerivWithin_prodMk (f.contDiffWithinAt_extChartAt hw hf)
      (g.contDiffWithinAt_extChartAt hw hg) (uniqueDiffOn_extChartAt_target x) hw hm
  rw [key f₀ g₀ w₀ hw₀ h₁ h₂] at hV
  set l := 𝓝 (f₀, g₀) ×ˢ 𝓝[φ.target] w₀
  have hl₁ : Tendsto (fun q : (C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯) × E ↦ (q.1.1, q.2)) l
      (𝓝 f₀ ×ˢ 𝓝[φ.target] w₀) :=
    ((continuous_fst.tendsto _).comp tendsto_fst).prodMk tendsto_snd
  have hl₂ : Tendsto (fun q : (C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯) × E ↦ (q.1.2, q.2)) l
      (𝓝 g₀ ×ˢ 𝓝[φ.target] w₀) :=
    ((continuous_snd.tendsto _).comp tendsto_fst).prodMk tendsto_snd
  have hD := ((ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m ↦ E) F F').continuous.tendsto
    _).comp (((tendsto_iteratedFDerivWithin_extChartAt hw₀ h₁ hm).comp hl₁).prodMk_nhds
      ((tendsto_iteratedFDerivWithin_extChartAt hw₀ h₂ hm).comp hl₂))
  filter_upwards [hl₁.eventually (eventually_mem_extChartAt_source hw₀ h₁),
    hl₂.eventually (eventually_mem_extChartAt_source hw₀ h₂),
    tendsto_snd.eventually self_mem_nhdsWithin, hD.eventually_mem hV] with q hq₁ hq₂ hq hqV
  exact ⟨⟨hq₁, hq₂⟩, (key q.1.1 q.1.2 q.2 hq hq₁ hq₂).symm ▸ hqV⟩

/-- Pairing of `C^n` maps is jointly continuous for the manifold weak Whitney topologies,
provided the source model is locally compact. -/
theorem continuous_prodMk_manifoldWeakWhitney :
    Continuous (fun p : C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯ ↦ p.1.prodMk p.2) := by
  refine continuous_iff_continuousAt.mpr fun ⟨f₀, g₀⟩ ↦ ?_
  refine tendsto_manifoldWeakWhitney_iff.mpr fun x y m hm K hK V hV h₀ ↦ ?_
  simp only [mem_chartJetSet]
  -- A compactness argument over `K` reduces the test to a neighbourhood of each of its points.
  refine hK.eventually_forall_of_forall_eventually fun w hw ↦ ?_
  have h := eventually_prodMk_mem_source_and_iteratedFDerivWithin_mem w.2
    ((mem_chartJetSet.mp h₀) w hw).1 hm (hV.mem_nhds ((mem_chartJetSet.mp h₀) w hw).2)
  rw [nhds_prod_eq]
  exact (tendsto_id.prodMap (map_nhds_subtype_val w).le).eventually h

end ContMDiffMap
