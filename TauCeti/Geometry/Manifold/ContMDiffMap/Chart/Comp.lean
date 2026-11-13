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
compact. No compactness of the manifolds themselves is needed. Postcomposition with a fixed map
is continuous as soon as the source model is locally compact: the coordinate derivatives of the
fixed outer map are continuous in the chart point alone.

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
* `ContMDiffMap.continuous_postcomp_manifoldWeakWhitney`: postcomposition with a fixed map is
  continuous, without local compactness of the model of the middle manifold.

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

variable [LocallyCompactSpace E]

/-- The local form of continuity of `x ↦ g x ∘ f x`: a coordinate derivative test passed by
`g x₀ ∘ f x₀` at a chart point is passed near that point by `g x ∘ f x` for all `x` near `x₀`.
The inner family `f` is continuous at `x₀`; the outer family `g` stays visible in charts and has
convergent coordinate derivatives, jointly in the parameter and the chart point. -/
private theorem eventually_comp_mem_source_and_iteratedFDerivWithin_mem {X : Type*}
    [TopologicalSpace X] {g : X → C^n⟮J, N; I', P⟯} {f : X → C^n⟮I, M; J, N⟯} {x₀ : X}
    (hF : ContinuousAt f x₀) {x : M} {z : P}
    (hG : ∀ {y : N} {u₀ : F}, u₀ ∈ (extChartAt J y).target →
      g x₀ ((extChartAt J y).symm u₀) ∈ (extChartAt I' z).source →
      (∀ᶠ p : X × F in 𝓝 x₀ ×ˢ 𝓝[(extChartAt J y).target] u₀,
        g p.1 ((extChartAt J y).symm p.2) ∈ (extChartAt I' z).source) ∧
      ∀ k : ℕ, k ≤ n → Tendsto (fun p : X × F ↦
          iteratedFDerivWithin 𝕜 k (extChartAt I' z ∘ g p.1 ∘ (extChartAt J y).symm)
            (extChartAt J y).target p.2) (𝓝 x₀ ×ˢ 𝓝[(extChartAt J y).target] u₀)
        (𝓝 (iteratedFDerivWithin 𝕜 k (extChartAt I' z ∘ g x₀ ∘ (extChartAt J y).symm)
          (extChartAt J y).target u₀)))
    {w₀ : E} (hw₀ : w₀ ∈ (extChartAt I x).target)
    (h₀ : (g x₀).comp (f x₀) ((extChartAt I x).symm w₀) ∈ (extChartAt I' z).source)
    {m : ℕ} (hm : m ≤ n) {V : Set (E [×m]→L[𝕜] E')}
    (hV : V ∈ 𝓝 (iteratedFDerivWithin 𝕜 m
      (extChartAt I' z ∘ (g x₀).comp (f x₀) ∘ (extChartAt I x).symm)
      (extChartAt I x).target w₀)) :
    ∀ᶠ q : X × E in 𝓝 x₀ ×ˢ 𝓝[(extChartAt I x).target] w₀,
      (g q.1).comp (f q.1) ((extChartAt I x).symm q.2) ∈ (extChartAt I' z).source ∧
        iteratedFDerivWithin 𝕜 m
          (extChartAt I' z ∘ (g q.1).comp (f q.1) ∘ (extChartAt I x).symm)
          (extChartAt I x).target q.2 ∈ V := by
  set φ := extChartAt I x
  set χ := extChartAt I' z
  set f₀ := f x₀
  -- Read the middle manifold in the chart at the image point `f₀ (φ.symm w₀)`.
  set ψ := extChartAt J (f₀ (φ.symm w₀))
  have hf₀ : f₀ (φ.symm w₀) ∈ ψ.source := mem_extChartAt_source _
  have hu₀ : ψ (f₀ (φ.symm w₀)) ∈ ψ.target := mem_extChartAt_target _
  have hg₀ : g x₀ (ψ.symm (ψ (f₀ (φ.symm w₀)))) ∈ χ.source := by
    rw [ψ.left_inv hf₀]
    exact h₀
  set l := 𝓝 x₀ ×ˢ 𝓝[φ.target] w₀
  -- The inner map, its coordinate derivatives, and its value in the chart `ψ`.
  have hfl : Tendsto (fun q : X × E ↦ (f q.1, q.2)) l (𝓝 f₀ ×ˢ 𝓝[φ.target] w₀) :=
    (hF.tendsto.comp tendsto_fst).prodMk tendsto_snd
  have hsrc : ∀ᶠ q in l, f q.1 (φ.symm q.2) ∈ ψ.source :=
    hfl.eventually (eventually_mem_extChartAt_source hw₀ hf₀)
  have hjf (k : ℕ) (hk : k ≤ m) := (tendsto_iteratedFDerivWithin_extChartAt hw₀ hf₀
    ((Nat.cast_le.mpr hk).trans hm)).comp hfl
  have hu : Tendsto (fun q : X × E ↦ ψ (f q.1 (φ.symm q.2))) l
      (𝓝[ψ.target] ψ (f₀ (φ.symm w₀))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hsrc.mono fun _ h ↦ ψ.map_source h⟩
    have h := ((continuous_eval_const (0 : Fin 0 → E)).tendsto _).comp (hjf 0 (Nat.zero_le m))
    simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using h
  -- The outer map, read at the moving point of the chart `ψ`.
  have hgl : Tendsto (fun q : X × E ↦ (q.1, ψ (f q.1 (φ.symm q.2)))) l
      (𝓝 x₀ ×ˢ 𝓝[ψ.target] ψ (f₀ (φ.symm w₀))) :=
    tendsto_fst.prodMk hu
  obtain ⟨hGsrc, hGlim⟩ := hG hu₀ hg₀
  have hjg (k : ℕ) (hk : k ≤ m) := (hGlim k ((Nat.cast_le.mpr hk).trans hm)).comp hgl
  have hcsrc : ∀ᶠ q in l, (g q.1).comp (f q.1) (φ.symm q.2) ∈ χ.source := by
    filter_upwards [hsrc, hgl.eventually hGsrc] with q h₁ h₂
    rwa [ψ.left_inv h₁] at h₂
  -- Along `l`, the derivative of the composite is the Taylor composition of these derivatives,
  -- which converges to that of `g x₀` and `f₀`.
  have hfdb : ∀ᶠ q in l, (ftaylorSeriesWithin 𝕜 (χ ∘ g q.1 ∘ ψ.symm) ψ.target
        (ψ (f q.1 (φ.symm q.2)))).taylorComp (ftaylorSeriesWithin 𝕜 (ψ ∘ f q.1 ∘ φ.symm)
          φ.target q.2) m =
      iteratedFDerivWithin 𝕜 m (χ ∘ (g q.1).comp (f q.1) ∘ φ.symm) φ.target q.2 := by
    filter_upwards [hsrc, hcsrc, tendsto_snd.eventually self_mem_nhdsWithin] with q h₁ h₂ h₃
    exact (iteratedFDerivWithin_extChartAt_comp (g q.1) (f q.1) h₃ h₁ h₂ hm).symm
  have hlim := (Filter.Tendsto.taylorComp hjg fun k _ hk ↦ hjf k hk).congr' hfdb
  rw [iteratedFDerivWithin_extChartAt_comp (g x₀) f₀ hw₀ hf₀ h₀ hm] at hV
  exact hcsrc.and (hlim.eventually_mem hV)

/-- `x ↦ g x ∘ f x` is continuous for the manifold weak Whitney topology when `f` is continuous
and `g` stays visible in charts and has convergent coordinate derivatives, jointly in the
parameter and the chart point. -/
private theorem continuous_comp_of_tendsto_iteratedFDerivWithin {X : Type*} [TopologicalSpace X]
    {g : X → C^n⟮J, N; I', P⟯} {f : X → C^n⟮I, M; J, N⟯} (hF : Continuous f)
    (hG : ∀ (x₀ : X) (z : P) {y : N} {u₀ : F}, u₀ ∈ (extChartAt J y).target →
      g x₀ ((extChartAt J y).symm u₀) ∈ (extChartAt I' z).source →
      (∀ᶠ p : X × F in 𝓝 x₀ ×ˢ 𝓝[(extChartAt J y).target] u₀,
        g p.1 ((extChartAt J y).symm p.2) ∈ (extChartAt I' z).source) ∧
      ∀ k : ℕ, k ≤ n → Tendsto (fun p : X × F ↦
          iteratedFDerivWithin 𝕜 k (extChartAt I' z ∘ g p.1 ∘ (extChartAt J y).symm)
            (extChartAt J y).target p.2) (𝓝 x₀ ×ˢ 𝓝[(extChartAt J y).target] u₀)
        (𝓝 (iteratedFDerivWithin 𝕜 k (extChartAt I' z ∘ g x₀ ∘ (extChartAt J y).symm)
          (extChartAt J y).target u₀))) :
    Continuous (fun x ↦ (g x).comp (f x)) := by
  refine continuous_iff_continuousAt.mpr fun x₀ ↦ ?_
  refine tendsto_manifoldWeakWhitney_iff.mpr fun x z m hm K hK V hV h₀ ↦ ?_
  simp only [mem_chartJetSet]
  -- A compactness argument over `K` reduces the test to a neighbourhood of each of its points.
  refine hK.eventually_forall_of_forall_eventually fun w hw ↦ ?_
  have h := eventually_comp_mem_source_and_iteratedFDerivWithin_mem hF.continuousAt (hG x₀ z) w.2
    ((mem_chartJetSet.mp h₀) w hw).1 hm (hV.mem_nhds ((mem_chartJetSet.mp h₀) w hw).2)
  rw [nhds_prod_eq]
  exact (tendsto_id.prodMap (map_nhds_subtype_val w).le).eventually h

/-- Composition of `C^n` maps is jointly continuous for the manifold weak Whitney topologies,
provided the models of the source and of the middle manifold are locally compact. -/
theorem continuous_comp_manifoldWeakWhitney [LocallyCompactSpace F] :
    Continuous (fun p : C^n⟮J, N; I', P⟯ × C^n⟮I, M; J, N⟯ ↦ p.1.comp p.2) := by
  refine continuous_comp_of_tendsto_iteratedFDerivWithin continuous_snd
    fun _ _ _ _ hu₀ hg₀ ↦ ⟨?_, fun k hk ↦ ?_⟩
  -- The outer map moves with the parameter.
  · exact ((continuous_fst.tendsto _).prodMap tendsto_id).eventually
      (eventually_mem_extChartAt_source hu₀ hg₀)
  · exact (tendsto_iteratedFDerivWithin_extChartAt hu₀ hg₀ hk).comp
      ((continuous_fst.tendsto _).prodMap tendsto_id)

/-- Postcomposition with a fixed `C^n` map is continuous for the manifold weak Whitney
topologies, provided the source model is locally compact. Unlike joint continuity of composition,
this needs no local compactness of the model of the middle manifold. -/
theorem continuous_postcomp_manifoldWeakWhitney (g : C^n⟮J, N; I', P⟯) :
    Continuous (fun f : C^n⟮I, M; J, N⟯ ↦ g.comp f) := by
  refine continuous_comp_of_tendsto_iteratedFDerivWithin (g := fun _ ↦ g) continuous_id
    fun _ _ _ _ hu₀ hg₀ ↦ ⟨?_, fun k hk ↦ ?_⟩
  -- The outer map is fixed, so only the chart point moves.
  · exact tendsto_snd.eventually
      ((map_continuous g).continuousAt.eventually_mem_extChartAt_source hu₀ hg₀)
  · exact ((g.contDiffWithinAt_extChartAt hu₀ hg₀).continuousWithinAt_iteratedFDerivWithin
      (uniqueDiffOn_extChartAt_target _) hk hu₀).tendsto.comp tendsto_snd

end ContMDiffMap
