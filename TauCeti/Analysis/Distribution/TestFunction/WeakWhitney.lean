/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Test functions as `C^n` maps with the weak Whitney topology

A function in `𝓓^{n}_{K}(E, F)`, smooth of class `C^n` with support in a fixed compact set `K`, is
in particular a bundled `C^n` map `E → F` (`ContDiffMapSupportedIn.toContMDiffMap`). Because every
derivative of a function in `𝓓^{n}_{K}(E, F)` vanishes outside `K`, its global sup-norm coincides
with the uniform norm of its restriction to `K`
(`ContDiffMapSupportedIn.seminorm_eq_norm_restrict`). Consequently, uniform convergence of every
derivative of order at most `n` on all of `E` is equivalent to compact-open convergence of those
derivatives, so `ContDiffMapSupportedIn.toContMDiffMap` is a topological embedding into the weak
Whitney topology (`ContDiffMapSupportedIn.isEmbedding_toContMDiffMap`).

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
theorem seminorm_eq_norm_restrict {i : ℕ} (hi : i ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    N[ℝ]_{K, n, i} f =
      ‖(ContMDiffMap.iteratedFDerivContinuousMap (toContMDiffMap f) i
        (by exact_mod_cast hi)).restrict (K : Set E)‖ := by
  set g : C((K : Set E), E [×i]→L[ℝ] F) :=
    (ContMDiffMap.iteratedFDerivContinuousMap (toContMDiffMap f) i
      (by exact_mod_cast hi)).restrict (K : Set E)
  apply le_antisymm
  · refine (f.seminorm_le_iff ℝ (norm_nonneg g) i).2 fun _ x hx ↦ ?_
    have hgx : g ⟨x, hx⟩ = iteratedFDeriv ℝ i f x := by
      simp [g, -SetLike.coe_sort_coe]
    exact hgx ▸ g.norm_coe_le_norm ⟨x, hx⟩
  · refine (g.norm_le (apply_nonneg (ContDiffMapSupportedIn.seminorm ℝ E F n K i) f)).2 fun z ↦ ?_
    have hgz : g z = iteratedFDeriv ℝ i f z := by
      simp [g, -SetLike.coe_sort_coe]
    exact hgz.symm ▸ norm_iteratedFDeriv_apply_le_seminorm ℝ hi

/-- Continuity into `𝓓^{n}_{K}(E, F)` is equivalent to continuity into the weak Whitney space of
`C^n` maps, because functions supported in `K` have derivatives supported in `K`. -/
theorem continuous_iff_toContMDiffMap {X : Type*} [TopologicalSpace X]
    {φ : X → 𝓓^{n}_{K}(E, F)} :
    Continuous φ ↔ Continuous (fun x ↦ toContMDiffMap (φ x)) := by
  refine ⟨fun h ↦ continuous_toContMDiffMap.comp h, fun hφ ↦ ?_⟩
  refine (continuous_iff_comp_order_le φ).2 fun i hi ↦ ?_
  have hi' : (i : WithTop ℕ∞) ≤ n := by exact_mod_cast hi
  let ψ : X → BoundedContinuousFunction (K : Set E) (E [×i]→L[ℝ] F) := fun x ↦
    ContinuousMap.equivBoundedOfCompact (K : Set E) _
      ((ContMDiffMap.iteratedFDerivContinuousMap (toContMDiffMap (φ x)) i hi').restrict
        (K : Set E))
  have hψ : Continuous ψ :=
    (ContinuousMap.isUniformInducing_equivBoundedOfCompact (K : Set E)
      _).uniformContinuous.continuous.comp
      ((ContinuousMap.continuous_restrict (K : Set E)).comp
        ((ContMDiffMap.continuous_iteratedFDerivContinuousMap i hi').comp hφ))
  have hdist (x y : X) :
      dist (structureMapCLM ℝ n i (φ x)) (structureMapCLM ℝ n i (φ y)) = dist (ψ x) (ψ y) := by
    have hsub :
        (ContMDiffMap.iteratedFDerivContinuousMap (toContMDiffMap (φ x - φ y)) i hi').restrict
            (K : Set E) =
          (ψ x - ψ y).toContinuousMap := by
      ext z : 1
      simp only [ψ, ContinuousMap.restrict_apply, ContMDiffMap.iteratedFDerivContinuousMap_apply,
        coe_toContMDiffMap, FunLike.coe_sub, BoundedContinuousFunction.coe_toContinuousMap,
        sub_apply, ContinuousMap.equivBoundedOfCompact_apply,
        BoundedContinuousFunction.mkOfCompact_apply]
      exact iteratedFDeriv_sub_apply (((φ x).contDiff.of_le hi').contDiffAt)
        (((φ y).contDiff.of_le hi').contDiffAt)
    rw [dist_eq_norm (structureMapCLM ℝ n i (φ x)) (structureMapCLM ℝ n i (φ y)),
      show structureMapCLM ℝ n i (φ x) - structureMapCLM ℝ n i (φ y) =
          structureMapCLM ℝ n i (φ x - φ y) by
        ext z : 1
        simp only [structureMapCLM_apply, hi, ↓reduceIte, sub_apply, FunLike.coe_sub]
        exact (iteratedFDeriv_sub_apply (((φ x).contDiff.of_le hi').contDiffAt)
          (((φ y).contDiff.of_le hi').contDiffAt)).symm,
      ← ContDiffMapSupportedIn.seminorm_apply,
      seminorm_eq_norm_restrict hi, hsub, BoundedContinuousFunction.norm_toContinuousMap_eq,
      ← dist_eq_norm (ψ x) (ψ y)]
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.1 (hψ.continuousAt (x := x))) ε hε] with y hy
  simpa only [Function.comp_apply, hdist] using hy

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
  exact (continuous_iff_toContMDiffMap (X := 𝓓^{n}_{K}(E, F)) (φ := id)).2 continuous_induced_dom

/-- The inclusion of `𝓓^{n}_{K}(E, F)` into `C^n(E, F)` with the weak Whitney topology is a
topological embedding. -/
theorem isEmbedding_toContMDiffMap :
    Topology.IsEmbedding
      (toContMDiffMap : 𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) :=
  ⟨isInducing_toContMDiffMap, toContMDiffMap_injective⟩

end ContDiffMapSupportedIn
