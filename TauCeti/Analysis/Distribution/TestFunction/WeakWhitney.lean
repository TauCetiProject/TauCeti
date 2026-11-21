/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Basic

/-!
# Test functions as `C^n` maps with the weak Whitney topology

A function in `𝓓^{n}_{K}(E, F)`, smooth of class `C^n` with support in a fixed compact set `K`, is
in particular a bundled `C^n` map `E → F` (`ContDiffMapSupportedIn.toContMDiffMap`). The topology of
`𝓓^{n}_{K}(E, F)` is uniform convergence of every derivative of order at most `n` on all of `E`,
which is stronger than convergence of these derivatives uniformly on compact sets, the weak Whitney
topology on `C^n` maps (`ContDiffMapSupportedIn.continuous_toContMDiffMap`). Conversely, because
every derivative of a function in `𝓓^{n}_{K}(E, F)` vanishes outside `K`, its global sup-norm
coincides with the uniform norm of its restriction to `K`
(`ContDiffMapSupportedIn.seminorm_eq_norm_restrict`), and uniform convergence of derivatives on
`K` is uniform convergence on `E`. Hence the inclusion induces the topology of `𝓓^{n}_{K}(E, F)`
(`ContDiffMapSupportedIn.continuous_iff_continuous_toContMDiffMap`,
`ContDiffMapSupportedIn.isEmbedding_toContMDiffMap`).

The weak Whitney topology on maps between manifolds is built from charts, and is functorial
under composition with fixed smooth maps. Through this embedding, test functions on a chart
target can be transported to a manifold and localized sections can be read back as test functions
with continuous dependence in both directions.
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

/-- Bundled test functions supported in `K` are determined by their underlying `C^n` maps. -/
theorem toContMDiffMap_injective :
    Function.Injective (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) :=
  fun _ _ h ↦ ext fun x ↦ congr($h x)

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

/-- For `i ≤ n`, the `i`-th derivative seminorm of a test function supported in `K` equals the
uniform norm on `K` of its `i`-th derivative, since all derivatives vanish outside `K`. -/
theorem seminorm_eq_norm_restrict (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] {i : ℕ} (hi : i ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} f =
      ‖(ContMDiffMap.iteratedFDerivContinuousMap (toContMDiffMap f) i
        (by exact_mod_cast hi)).restrict (K : Set E)‖ := by
  set g : C((K : Set E), E [×i]→L[ℝ] F) :=
    (ContMDiffMap.iteratedFDerivContinuousMap (toContMDiffMap f) i
      (by exact_mod_cast hi)).restrict (K : Set E)
  apply le_antisymm
  · refine (f.seminorm_le_iff 𝕜 (norm_nonneg g) i).2 fun _ x hx ↦ ?_
    have hgx : g ⟨x, hx⟩ = iteratedFDeriv ℝ i f x := by
      simp [g, -SetLike.coe_sort_coe]
    exact hgx ▸ g.norm_coe_le_norm ⟨x, hx⟩
  · refine (g.norm_le (apply_nonneg (ContDiffMapSupportedIn.seminorm 𝕜 E F n K i) f)).2 fun z ↦ ?_
    have hgz : g z = iteratedFDeriv ℝ i f z := by
      simp [g, -SetLike.coe_sort_coe]
    exact hgz.symm ▸ norm_iteratedFDeriv_apply_le_seminorm 𝕜 hi

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

/-- The inclusion of `𝓓^{n}_{K}(E, F)` into `C^n(E, F)` with the weak Whitney topology induces its
topology. Neither local compactness nor finite dimensionality of `E` is needed. -/
theorem isInducing_toContMDiffMap :
    Topology.IsInducing
      (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) := by
  refine ⟨le_antisymm (continuous_iff_le_induced.1 continuous_toContMDiffMap) ?_⟩
  refine (continuous_id_iff_le (t := TopologicalSpace.induced toContMDiffMap inferInstance)
    (t' := inferInstance)).1 ?_
  let := TopologicalSpace.induced
    (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) inferInstance
  exact (continuous_iff_continuous_toContMDiffMap (X := 𝓓^{n}_{K}(E, F))
    (φ := id)).2 continuous_induced_dom

/-- The inclusion of `𝓓^{n}_{K}(E, F)` into `C^n(E, F)` with the weak Whitney topology is a
topological embedding. -/
theorem isEmbedding_toContMDiffMap :
    Topology.IsEmbedding
      (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) :=
  ⟨isInducing_toContMDiffMap, toContMDiffMap_injective⟩

end ContDiffMapSupportedIn
