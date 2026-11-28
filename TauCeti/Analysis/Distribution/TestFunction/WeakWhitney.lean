/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Basic

/-!
# Test functions as `C^n` maps with the weak Whitney topology

A function in `𝓓^{n}_{K}(E, F)`, smooth of class `C^n` with support in a fixed compact set `K`, is
in particular a bundled `C^n` map `E → F`
(`ContDiffMapSupportedIn.toContMDiffMap`). The topology of `𝓓^{n}_{K}(E, F)` is uniform
convergence of every derivative of order at most `n` on all of `E`, which is stronger than
convergence of these derivatives uniformly on compact sets, the weak Whitney topology on `C^n`
maps. So this inclusion is continuous (`ContDiffMapSupportedIn.continuous_toContMDiffMap`).
Conversely, since every function in `𝓓^{n}_{K}(E, F)` vanishes with all its derivatives outside the
compact set `K`, uniform convergence of the derivatives on `K` already is uniform convergence on
`E`. Hence the inclusion induces the topology of `𝓓^{n}_{K}(E, F)`
(`ContDiffMapSupportedIn.isInducing_toContMDiffMap`,
`ContDiffMapSupportedIn.isEmbedding_toContMDiffMap`): a family of test functions supported in `K`
is continuous exactly when it is continuous as a family of `C^n` maps
(`ContDiffMapSupportedIn.continuous_iff_continuous_toContMDiffMap`).

The weak Whitney topology on maps between manifolds is built from charts, and is functorial
under composition with fixed smooth maps. Through this embedding, test functions on a chart
target can be transported back and forth to a manifold with continuous dependence in both
directions, which is how chart extensions of test functions identify the chart-generated and
fixed-compact topologies on bundle test sections.
-/

public section

open scoped Manifold ContDiff Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞} {K : TopologicalSpace.Compacts E}

/-- A test function supported in `K`, as a bundled `C^n` map. -/
def toContMDiffMap (f : 𝓓^{n}_{K}(E, F)) : C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ :=
  ⟨f, f.contDiff.contMDiff⟩

@[simp]
theorem coe_toContMDiffMap (f : 𝓓^{n}_{K}(E, F)) : ⇑(toContMDiffMap f) = f :=
  (rfl)

/-- Viewing a supported test function as a `C^n` map is injective. -/
theorem toContMDiffMap_injective :
    Function.Injective
      (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) := by
  intro f g h
  ext x
  simpa only [coe_toContMDiffMap] using DFunLike.congr_fun h x

/-- The inclusion of the test functions supported in `K` into the `C^n` maps is continuous for
the weak Whitney topology: uniform convergence of every derivative on `E` implies its uniform
convergence on compact sets. -/
theorem continuous_toContMDiffMap :
    Continuous (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) := by
  refine ContMDiffMap.continuous_weakWhitney_of_continuous_iteratedFDeriv fun m hm ↦ ?_
  have hm' : (m : ℕ∞) ≤ n := by exact_mod_cast hm
  refine (continuous_eval.comp
    ((structureMapCLM ℝ n m).continuous.prodMap continuous_id)).congr fun z ↦ ?_
  simp [structureMapCLM_apply, hm']

/-- On a fixed compact support the weak Whitney topology is the topology of test functions: a
family of test functions supported in `K` is continuous exactly when it is continuous as a family
of `C^n` maps. Outside `K` all derivatives vanish, so uniform convergence of the derivatives on
the compact set `K` is uniform convergence on all of `E`. -/
theorem continuous_iff_continuous_toContMDiffMap {X : Type*} [TopologicalSpace X]
    {φ : X → 𝓓^{n}_{K}(E, F)} :
    Continuous φ ↔ Continuous (fun x ↦ toContMDiffMap (φ x)) := by
  refine ⟨continuous_toContMDiffMap.comp, fun h ↦ ?_⟩
  refine (continuous_iff_comp_order_le φ).2 fun i hi ↦ continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  have hi' : ((i : ℕ∞) : WithTop ℕ∞) ≤ n := by exact_mod_cast hi
  have hK := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
    ((ContMDiffMap.continuous_weakWhitney_iff.1 h i hi').tendsto x₀) K K.isCompact
  rw [ContinuousAt, BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
  intro u hu
  filter_upwards [hK u hu] with x hx y
  by_cases hy : y ∈ K
  · simpa [structureMapCLM_apply, hi] using hx y hy
  · simp only [Function.comp_apply, structureMapCLM_apply, hi, ite_true]
    rw [(φ x₀).iteratedFDeriv_zero_on_compl hy, (φ x).iteratedFDeriv_zero_on_compl hy]
    exact refl_mem_uniformity hu

/-- The topology on `𝓓^{n}_{K}(E, F)` is induced by its inclusion into `C^n` maps with the weak
Whitney topology: because all derivatives vanish off the compact set `K`, uniform convergence on
`K` already controls the global sup norm of every derivative through order `n`. -/
theorem isInducing_toContMDiffMap :
    Topology.IsInducing
      (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) := by
  refine ⟨le_antisymm continuous_toContMDiffMap.le_induced ?_⟩
  let _ : TopologicalSpace 𝓓^{n}_{K}(E, F) := TopologicalSpace.induced toContMDiffMap inferInstance
  exact continuous_id_iff_le.1 <| continuous_iff_continuous_toContMDiffMap.2 continuous_induced_dom

/-- `ContDiffMapSupportedIn.toContMDiffMap` is a topological embedding of `𝓓^{n}_{K}(E, F)` into
the weak Whitney topology on `C^n` maps. -/
theorem isEmbedding_toContMDiffMap :
    Topology.IsEmbedding
      (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) :=
  ⟨isInducing_toContMDiffMap, toContMDiffMap_injective⟩

end ContDiffMapSupportedIn
