/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Hom.ContinuousEval

/-!
# Joint evaluation in the manifold weak Whitney topology

The weak Whitney topology controls coordinate derivatives on compact subsets of source charts.
For a locally compact source model, local compactness gives a compact chart neighbourhood of
each point, so a coordinate derivative of a map is continuous jointly in the map and the chart
point: `ContMDiffMap.tendsto_iteratedFDerivWithin_extChartAt`. In order zero this is the
continuity of evaluation jointly in the map and the source point, which is what the natural
action of the diffeomorphism group on its manifold needs. In higher order it is the input for
continuity of composition.

The compact-neighbourhood argument is the standard one for compact-open evaluation; see
M. Hirsch, *Differential Topology*, Chapter 2, §1.
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

/-- A map continuous at a point and visible there in a target chart stays visible at the nearby
points of a source chart target. -/
theorem _root_.ContinuousAt.eventually_mem_extChartAt_source {f : M → N} {x : M} {y : N}
    {w : E} (hfc : ContinuousAt f ((extChartAt I x).symm w)) (hw : w ∈ (extChartAt I x).target)
    (hf : f ((extChartAt I x).symm w) ∈ (extChartAt J y).source) :
    ∀ᶠ v in 𝓝[(extChartAt I x).target] w, f ((extChartAt I x).symm v) ∈ (extChartAt J y).source :=
  (hfc.comp_continuousWithinAt (continuousOn_extChartAt_symm x w hw)).preimage_mem_nhdsWithin
    ((isOpen_extChartAt_source y).mem_nhds hf)

/-- The coordinate representative of a `C^n` map in any pair of extended charts is `C^n` within
the source chart target, at every point where the map is visible in the target chart. -/
theorem contDiffWithinAt_extChartAt (f : C^n⟮I, M; J, N⟯) {x : M} {y : N} {w : E}
    (hw : w ∈ (extChartAt I x).target)
    (hf : f ((extChartAt I x).symm w) ∈ (extChartAt J y).source) :
    ContDiffWithinAt 𝕜 n (extChartAt J y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x).target w :=
  (contDiffWithinAt_inter'
    ((map_continuous f).continuousAt.eventually_mem_extChartAt_source hw hf)).mp
    ((contMDiff_iff.mp f.contMDiff).2 x y w ⟨hw, hf⟩)

section LocallyCompact

variable [LocallyCompactSpace E]

/-- A coordinate derivative test passed near a chart point is passed, in a neighbourhood of
that point, by every nearby map. This is the compact-neighbourhood argument behind
`tendsto_iteratedFDerivWithin_extChartAt` and `eventually_mem_extChartAt_source`. -/
private theorem eventually_mem_source_and_iteratedFDerivWithin_mem {f₀ : C^n⟮I, M; J, N⟯}
    {x : M} {y : N} {w₀ : E} (hw₀ : w₀ ∈ (extChartAt I x).target)
    (hf₀ : f₀ ((extChartAt I x).symm w₀) ∈ (extChartAt J y).source) {m : ℕ} (hm : m ≤ n)
    {V : Set (E [×m]→L[𝕜] F)}
    (hV : V ∈ 𝓝 (iteratedFDerivWithin 𝕜 m (extChartAt J y ∘ f₀ ∘ (extChartAt I x).symm)
      (extChartAt I x).target w₀)) :
    ∀ᶠ p : C^n⟮I, M; J, N⟯ × E in 𝓝 f₀ ×ˢ 𝓝[(extChartAt I x).target] w₀,
      p.1 ((extChartAt I x).symm p.2) ∈ (extChartAt J y).source ∧
        iteratedFDerivWithin 𝕜 m (extChartAt J y ∘ p.1 ∘ (extChartAt I x).symm)
          (extChartAt I x).target p.2 ∈ V := by
  set φ := extChartAt I x
  set ψ := extChartAt J y
  let : LocallyCompactSpace φ.target := by
    rw [extChartAt_target]
    exact ((chartAt H x).open_target.preimage I.continuous_symm).isLocallyClosed.inter
      I.isClosed_range.isLocallyClosed |>.locallyCompactSpace
  obtain ⟨W, hWV, hW, hW₀⟩ := mem_nhds_iff.mp hV
  -- Near `w₀`, the map `f₀` passes the test with the open set `W`.
  have hA : {v | f₀ (φ.symm v) ∈ ψ.source ∧
      iteratedFDerivWithin 𝕜 m (ψ ∘ f₀ ∘ φ.symm) φ.target v ∈ W} ∈ 𝓝[φ.target] w₀ :=
    inter_mem ((map_continuous f₀).continuousAt.eventually_mem_extChartAt_source hw₀ hf₀)
      (((f₀.contDiffWithinAt_extChartAt hw₀ hf₀).continuousWithinAt_iteratedFDerivWithin
        (uniqueDiffOn_extChartAt_target x) hm hw₀).preimage_mem_nhdsWithin (hW.mem_nhds hW₀))
  rw [← preimage_coe_mem_nhds_subtype (a := ⟨w₀, hw₀⟩)] at hA
  -- A compact chart neighbourhood of `w₀` turns this into an open condition on the map.
  obtain ⟨C, hC, hCA, hCc⟩ := local_compact_nhds hA
  have hT : chartJetSet x y m C W ∈ 𝓝 f₀ :=
    (isOpen_chartJetSet x y m hm hCc hW).mem_nhds (mem_chartJetSet.mpr fun z hz ↦ hCA hz)
  have hC' : Subtype.val '' C ∈ 𝓝[φ.target] w₀ := by
    have h := image_mem_map (m := Subtype.val) hC
    rwa [map_nhds_subtype_val] at h
  filter_upwards [prod_mem_prod hT hC'] with ⟨f, v⟩ ⟨hf, z, hz, hzv⟩
  obtain rfl := hzv
  obtain ⟨h₁, h₂⟩ := mem_chartJetSet.mp hf z hz
  exact ⟨h₁, hWV h₂⟩

/-- A coordinate derivative of a `C^n` map is continuous jointly in the map, for the manifold
weak Whitney topology, and the point of the source chart target, provided the source model is
locally compact. Derivatives are taken within the chart target, so boundary and corner points
are included. -/
theorem tendsto_iteratedFDerivWithin_extChartAt {f₀ : C^n⟮I, M; J, N⟯} {x : M} {y : N} {w₀ : E}
    (hw₀ : w₀ ∈ (extChartAt I x).target)
    (hf₀ : f₀ ((extChartAt I x).symm w₀) ∈ (extChartAt J y).source) {m : ℕ} (hm : m ≤ n) :
    Tendsto (fun p : C^n⟮I, M; J, N⟯ × E ↦
        iteratedFDerivWithin 𝕜 m (extChartAt J y ∘ p.1 ∘ (extChartAt I x).symm)
          (extChartAt I x).target p.2)
      (𝓝 f₀ ×ˢ 𝓝[(extChartAt I x).target] w₀)
      (𝓝 (iteratedFDerivWithin 𝕜 m (extChartAt J y ∘ f₀ ∘ (extChartAt I x).symm)
        (extChartAt I x).target w₀)) := fun _ hV ↦
  (eventually_mem_source_and_iteratedFDerivWithin_mem hw₀ hf₀ hm hV).mono fun _ h ↦ h.2

/-- A map visible in a target chart at a point of a source chart stays visible there, jointly
for nearby maps and nearby chart points, provided the source model is locally compact. -/
theorem eventually_mem_extChartAt_source {f₀ : C^n⟮I, M; J, N⟯} {x : M} {y : N} {w₀ : E}
    (hw₀ : w₀ ∈ (extChartAt I x).target)
    (hf₀ : f₀ ((extChartAt I x).symm w₀) ∈ (extChartAt J y).source) :
    ∀ᶠ p : C^n⟮I, M; J, N⟯ × E in 𝓝 f₀ ×ˢ 𝓝[(extChartAt I x).target] w₀,
      p.1 ((extChartAt I x).symm p.2) ∈ (extChartAt J y).source :=
  (eventually_mem_source_and_iteratedFDerivWithin_mem hw₀ hf₀ (m := 0) (by simp)
    univ_mem).mono fun _ h ↦ h.1

/-- Evaluation of a `C^n` map is continuous jointly in the map and the source point for the
manifold weak Whitney topology, provided the source model is locally compact. -/
theorem continuous_eval_manifoldWeakWhitney :
    Continuous (fun p : C^n⟮I, M; J, N⟯ × M ↦ p.1 p.2) := by
  refine continuous_iff_continuousAt.mpr fun ⟨f, x⟩ ↦ ?_
  set φ := extChartAt I x
  set ψ := extChartAt J (f x)
  have hw : φ x ∈ φ.target := mem_extChartAt_target x
  have hf : f (φ.symm (φ x)) ∈ ψ.source := by
    rw [extChartAt_to_inv]
    exact mem_extChartAt_source (f x)
  -- Read the source point in the chart at `x`.
  have hφ : Tendsto (fun p : C^n⟮I, M; J, N⟯ × M ↦ (p.1, φ p.2)) (𝓝 (f, x))
      (𝓝 f ×ˢ 𝓝[φ.target] (φ x)) := by
    rw [nhds_prod_eq]
    refine tendsto_fst.prodMk (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
    · exact (continuousAt_extChartAt x).tendsto.comp tendsto_snd
    · exact tendsto_snd.eventually
        (eventually_of_mem (extChartAt_source_mem_nhds x) fun _ h ↦ φ.map_source h)
  have hsymm : ∀ᶠ p : C^n⟮I, M; J, N⟯ × M in 𝓝 (f, x), φ.symm (φ p.2) = p.2 :=
    (continuous_snd.tendsto (f, x)).eventually
      (eventually_of_mem (extChartAt_source_mem_nhds x) fun _ h ↦ φ.left_inv h)
  -- In order zero, the joint continuity of coordinate derivatives is that of the value in the
  -- target chart.
  have h₀ : Tendsto (fun q : C^n⟮I, M; J, N⟯ × E ↦ ψ (q.1 (φ.symm q.2)))
      (𝓝 f ×ˢ 𝓝[φ.target] (φ x)) (𝓝 (ψ (f x))) := by
    have := ((continuous_eval_const (0 : Fin 0 → E)).tendsto _).comp
      (tendsto_iteratedFDerivWithin_extChartAt hw hf (m := 0) (by simp))
    simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply, φ, extChartAt_to_inv]
      using this
  have hsrc := eventually_mem_extChartAt_source hw hf
  have hval : Tendsto (fun q : C^n⟮I, M; J, N⟯ × E ↦ q.1 (φ.symm q.2))
      (𝓝 f ×ˢ 𝓝[φ.target] (φ x)) (𝓝 (f x)) := by
    have h := ((continuousOn_extChartAt_symm (f x)) _ (mem_extChartAt_target (f x))).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨h₀, hsrc.mono fun _ h ↦ ψ.map_source h⟩)
    rw [extChartAt_to_inv] at h
    exact h.congr' (hsrc.mono fun _ h ↦ ψ.left_inv h)
  exact (hval.comp hφ).congr' (hsymm.mono fun _ h ↦ by simp only [Function.comp_apply, h])

/-- Joint evaluation is continuous for the manifold weak Whitney topology. -/
theorem continuousEval_manifoldWeakWhitney :
    ContinuousEval C^n⟮I, M; J, N⟯ M N :=
  ⟨continuous_eval_manifoldWeakWhitney⟩

scoped[TauCeti.ManifoldWeakWhitney] attribute [instance]
  ContMDiffMap.continuousEval_manifoldWeakWhitney

end LocallyCompact

end ContMDiffMap
