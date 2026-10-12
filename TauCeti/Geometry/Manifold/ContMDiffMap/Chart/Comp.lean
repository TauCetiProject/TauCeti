/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# Continuity of composition in the manifold weak Whitney topology

Composition `C^n⟮J, N; I', P⟯ × C^n⟮I, M; J, N⟯ → C^n⟮I, M; I', P⟯` is continuous for the weak
Whitney topologies, provided the models of the source and of the middle manifold are locally
compact. No compactness of the manifolds themselves is needed.

The proof is local in the source. Reading `g ∘ f` in charts through a chart of `N` at the image
point, the Faà di Bruno formula `iteratedFDerivWithin_comp_of_eventually_mem` expresses each
coordinate derivative of `g ∘ f` through the coordinate derivatives of `g` and of `f` of no
larger order (`ContMDiffMap.iteratedFDerivWithin_extChartAt_comp`). These depend continuously on
the maps and the chart point jointly (`ContMDiffMap.tendsto_iteratedFDerivWithin_extChartAt`),
and the Faà di Bruno composition depends continuously on them (`Filter.Tendsto.taylorComp`). A
compactness argument over the compact set of a derivative test then gives continuity.

## Main results

* `ContMDiffMap.iteratedFDerivWithin_extChartAt_comp`: the Faà di Bruno formula for coordinate
  derivatives of a composite, through any chart of the middle manifold.
* `ContMDiffMap.continuous_comp_manifoldWeakWhitney`: composition is jointly continuous.

The weak topology and the continuity properties of composition are treated in M. Hirsch,
*Differential Topology*, GTM 33, Chapter 2; the coordinate computation is Mathlib's Faà di Bruno
formula.
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
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold I' n P]

/-- The Faà di Bruno formula in charts: a coordinate derivative of `g ∘ f` is the Taylor
composition of the coordinate derivatives of `g` and of `f`, read through any chart of the middle
manifold in which `f` is visible at the point. -/
theorem iteratedFDerivWithin_extChartAt_comp (g : C^n⟮J, N; I', P⟯) (f : C^n⟮I, M; J, N⟯)
    {x : M} {y : N} {z : P} {w : E} (hw : w ∈ (extChartAt I x).target)
    (hf : f ((extChartAt I x).symm w) ∈ (extChartAt J y).source)
    (hg : g (f ((extChartAt I x).symm w)) ∈ (extChartAt I' z).source) {m : ℕ} (hm : m ≤ n) :
    iteratedFDerivWithin 𝕜 m (extChartAt I' z ∘ g.comp f ∘ (extChartAt I x).symm)
        (extChartAt I x).target w =
      (ftaylorSeriesWithin 𝕜 (extChartAt I' z ∘ g ∘ (extChartAt J y).symm)
          (extChartAt J y).target (extChartAt J y (f ((extChartAt I x).symm w)))).taylorComp
        (ftaylorSeriesWithin 𝕜 (extChartAt J y ∘ f ∘ (extChartAt I x).symm)
          (extChartAt I x).target w) m := by
  set φ := extChartAt I x
  set ψ := extChartAt J y
  have hev : ∀ᶠ v in 𝓝[φ.target] w, f (φ.symm v) ∈ ψ.source :=
    (map_continuous f).continuousAt.eventually_mem_extChartAt_source hw hf
  have hg' : g (ψ.symm (ψ (f (φ.symm w)))) ∈ (extChartAt I' z).source := by
    rwa [ψ.left_inv hf]
  -- Away from the chart of `N`, `g ∘ f` is read through `ψ`.
  have heq : extChartAt I' z ∘ g.comp f ∘ φ.symm =ᶠ[𝓝[φ.target] w]
      (extChartAt I' z ∘ g ∘ ψ.symm) ∘ (ψ ∘ f ∘ φ.symm) :=
    hev.mono fun v hv ↦ by simp only [Function.comp_apply, comp_apply, ψ.left_inv hv]
  rw [heq.iteratedFDerivWithin_eq (by simp only [Function.comp_apply, comp_apply, ψ.left_inv hf])]
  exact iteratedFDerivWithin_comp_of_eventually_mem (f := ψ ∘ f ∘ φ.symm)
    (g := extChartAt I' z ∘ g ∘ ψ.symm) (g.contDiffWithinAt_extChartAt (ψ.map_source hf) hg')
    (f.contDiffWithinAt_extChartAt hw hf)
    (uniqueDiffOn_extChartAt_target y) (uniqueDiffOn_extChartAt_target x) hw
    (hev.mono fun _ hv ↦ ψ.map_source hv) hm

variable [LocallyCompactSpace E] [LocallyCompactSpace F]

/-- The local form of continuity of composition: a coordinate derivative test passed by
`g₀ ∘ f₀` at a chart point is passed near that point by `g ∘ f` for all `g` near `g₀` and `f`
near `f₀`. -/
private theorem eventually_comp_mem_source_and_iteratedFDerivWithin_mem
    {g₀ : C^n⟮J, N; I', P⟯} {f₀ : C^n⟮I, M; J, N⟯} {x : M} {z : P} {w₀ : E}
    (hw₀ : w₀ ∈ (extChartAt I x).target)
    (h₀ : g₀.comp f₀ ((extChartAt I x).symm w₀) ∈ (extChartAt I' z).source) {m : ℕ} (hm : m ≤ n)
    {V : Set (E [×m]→L[𝕜] E')}
    (hV : V ∈ 𝓝 (iteratedFDerivWithin 𝕜 m (extChartAt I' z ∘ g₀.comp f₀ ∘ (extChartAt I x).symm)
      (extChartAt I x).target w₀)) :
    ∀ᶠ q : (C^n⟮J, N; I', P⟯ × C^n⟮I, M; J, N⟯) × E in
        𝓝 (g₀, f₀) ×ˢ 𝓝[(extChartAt I x).target] w₀,
      q.1.1.comp q.1.2 ((extChartAt I x).symm q.2) ∈ (extChartAt I' z).source ∧
        iteratedFDerivWithin 𝕜 m (extChartAt I' z ∘ q.1.1.comp q.1.2 ∘ (extChartAt I x).symm)
          (extChartAt I x).target q.2 ∈ V := by
  set φ := extChartAt I x
  set χ := extChartAt I' z
  -- Read the middle manifold in the chart at the image point `f₀ (φ.symm w₀)`.
  set ψ := extChartAt J (f₀ (φ.symm w₀))
  have hf₀ : f₀ (φ.symm w₀) ∈ ψ.source := mem_extChartAt_source _
  have hu₀ : ψ (f₀ (φ.symm w₀)) ∈ ψ.target := mem_extChartAt_target _
  have hg₀ : g₀ (ψ.symm (ψ (f₀ (φ.symm w₀)))) ∈ χ.source := by
    rw [ψ.left_inv hf₀]
    exact h₀
  set l := 𝓝 (g₀, f₀) ×ˢ 𝓝[φ.target] w₀
  -- The inner map, its coordinate derivatives, and its value in the chart `ψ`.
  have hfl : Tendsto (fun q : (C^n⟮J, N; I', P⟯ × C^n⟮I, M; J, N⟯) × E ↦ (q.1.2, q.2)) l
      (𝓝 f₀ ×ˢ 𝓝[φ.target] w₀) :=
    ((continuous_snd.tendsto _).comp tendsto_fst).prodMk tendsto_snd
  have hsrc : ∀ᶠ q in l, q.1.2 (φ.symm q.2) ∈ ψ.source :=
    hfl.eventually (eventually_mem_extChartAt_source hw₀ hf₀)
  have hjf (k : ℕ) (hk : k ≤ m) := (tendsto_iteratedFDerivWithin_extChartAt hw₀ hf₀
    ((Nat.cast_le.mpr hk).trans hm)).comp hfl
  have hu : Tendsto (fun q : (C^n⟮J, N; I', P⟯ × C^n⟮I, M; J, N⟯) × E ↦ ψ (q.1.2 (φ.symm q.2))) l
      (𝓝[ψ.target] ψ (f₀ (φ.symm w₀))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hsrc.mono fun _ h ↦ ψ.map_source h⟩
    have h := ((continuous_eval_const (0 : Fin 0 → E)).tendsto _).comp (hjf 0 (Nat.zero_le m))
    simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using h
  -- The outer map, read at the moving point of the chart `ψ`.
  have hgl : Tendsto (fun q : (C^n⟮J, N; I', P⟯ × C^n⟮I, M; J, N⟯) × E ↦
      (q.1.1, ψ (q.1.2 (φ.symm q.2)))) l (𝓝 g₀ ×ˢ 𝓝[ψ.target] ψ (f₀ (φ.symm w₀))) :=
    ((continuous_fst.tendsto _).comp tendsto_fst).prodMk hu
  have hjg (k : ℕ) (hk : k ≤ m) := (tendsto_iteratedFDerivWithin_extChartAt hu₀ hg₀
    ((Nat.cast_le.mpr hk).trans hm)).comp hgl
  have hcsrc : ∀ᶠ q in l, q.1.1.comp q.1.2 (φ.symm q.2) ∈ χ.source := by
    filter_upwards [hsrc, hgl.eventually (eventually_mem_extChartAt_source hu₀ hg₀)] with q h₁ h₂
    rwa [ψ.left_inv h₁] at h₂
  -- Along `l`, the derivative of the composite is the Taylor composition of these derivatives,
  -- which converges to that of `g₀` and `f₀`.
  have hfdb : ∀ᶠ q in l, (ftaylorSeriesWithin 𝕜 (χ ∘ q.1.1 ∘ ψ.symm) ψ.target
        (ψ (q.1.2 (φ.symm q.2)))).taylorComp (ftaylorSeriesWithin 𝕜 (ψ ∘ q.1.2 ∘ φ.symm)
          φ.target q.2) m =
      iteratedFDerivWithin 𝕜 m (χ ∘ q.1.1.comp q.1.2 ∘ φ.symm) φ.target q.2 := by
    filter_upwards [hsrc, hcsrc, tendsto_snd.eventually self_mem_nhdsWithin] with q h₁ h₂ h₃
    exact (iteratedFDerivWithin_extChartAt_comp q.1.1 q.1.2 h₃ h₁ h₂ hm).symm
  have hlim := (Filter.Tendsto.taylorComp hjg hjf).congr' hfdb
  rw [iteratedFDerivWithin_extChartAt_comp g₀ f₀ hw₀ hf₀ h₀ hm] at hV
  exact hcsrc.and (hlim.eventually_mem hV)

/-- Composition of `C^n` maps is jointly continuous for the manifold weak Whitney topologies,
provided the models of the source and of the middle manifold are locally compact. -/
theorem continuous_comp_manifoldWeakWhitney :
    Continuous (fun p : C^n⟮J, N; I', P⟯ × C^n⟮I, M; J, N⟯ ↦ p.1.comp p.2) := by
  refine continuous_iff_continuousAt.mpr fun ⟨g₀, f₀⟩ ↦ ?_
  refine tendsto_manifoldWeakWhitney_iff.mpr fun x z m hm K hK V hV h₀ ↦ ?_
  simp only [mem_chartJetSet]
  -- A compactness argument over `K` reduces the test to a neighbourhood of each of its points.
  refine hK.eventually_forall_of_forall_eventually fun w hw ↦ ?_
  have h := eventually_comp_mem_source_and_iteratedFDerivWithin_mem w.2
    ((mem_chartJetSet.mp h₀) w hw).1 hm (hV.mem_nhds ((mem_chartJetSet.mp h₀) w hw).2)
  rw [nhds_prod_eq]
  exact (tendsto_id.prodMap (map_nhds_subtype_val w).le).eventually h

end ContMDiffMap
