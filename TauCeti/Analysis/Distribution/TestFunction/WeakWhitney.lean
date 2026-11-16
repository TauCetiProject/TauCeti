/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Test functions as `C^n` maps with the weak Whitney topology

A function in `𝓓^{n}_{K}(E, F)`, smooth of class `C^n` with support in a fixed compact set `K`,
is in particular a bundled `C^n` map `E → F`
(`ContDiffMapSupportedIn.toContMDiffMap`). Because every derivative vanishes outside the compact
set `K`, uniform convergence of each derivative of order at most `n` on all of `E` is equivalent to
its uniform convergence on `K`, and hence to compact-open convergence on `E`. Therefore
`ContDiffMapSupportedIn.toContMDiffMap` is not only continuous
(`ContDiffMapSupportedIn.continuous_toContMDiffMap`), but a topological embedding
(`ContDiffMapSupportedIn.isEmbedding_toContMDiffMap`).

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

/-- The topology on `𝓓^{n}_{K}(E, F)` is induced by its inclusion into `C^n` maps with the weak
Whitney topology: because all derivatives vanish off the compact set `K`, uniform convergence on
`K` already controls the global sup norm of every derivative through order `n`. -/
theorem isInducing_toContMDiffMap :
    Topology.IsInducing
      (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) := by
  refine ⟨le_antisymm continuous_toContMDiffMap.le_induced ?_⟩
  rw [← continuous_id_iff_le]
  let _ : TopologicalSpace 𝓓^{n}_{K}(E, F) :=
    TopologicalSpace.induced toContMDiffMap inferInstance
  refine (continuous_iff_comp_order_le (id : 𝓓^{n}_{K}(E, F) → 𝓓^{n}_{K}(E, F))).2
    fun m hm ↦ ?_
  have hm' : (m : WithTop ℕ∞) ≤ n := by exact_mod_cast hm
  have hcont : Continuous fun f : 𝓓^{n}_{K}(E, F) ↦
      ContMDiffMap.iteratedFDerivContinuousMap (toContMDiffMap f) m hm' :=
    (ContMDiffMap.continuous_iteratedFDerivContinuousMap m hm').comp continuous_induced_dom
  refine continuous_iff_continuousAt.2 fun f₀ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hu := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
    (hcont.continuousAt (x := f₀)).tendsto K K.isCompact
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu (ε / 2) (half_pos hε)] with f hf
  have hle : dist (structureMapCLM ℝ n m f) (structureMapCLM ℝ n m f₀) ≤ ε / 2 := by
    refine (BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun x ↦ ?_
    by_cases hx : x ∈ K
    · simpa only [structureMapCLM_apply, hm, ↓reduceIte, dist_comm,
        ContMDiffMap.iteratedFDerivContinuousMap_apply, coe_toContMDiffMap] using (hf x hx).le
    · simp [structureMapCLM_apply, hm, f.iteratedFDeriv_zero_on_compl hx,
        f₀.iteratedFDeriv_zero_on_compl hx, (half_pos hε).le]
  exact hle.trans_lt (half_lt_self hε)

/-- `ContDiffMapSupportedIn.toContMDiffMap` is a topological embedding of `𝓓^{n}_{K}(E, F)` into
the weak Whitney topology on `C^n` maps. -/
theorem isEmbedding_toContMDiffMap :
    Topology.IsEmbedding
      (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) :=
  ⟨isInducing_toContMDiffMap, toContMDiffMap_injective⟩

end ContDiffMapSupportedIn
