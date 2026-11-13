/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import TauCeti.Analysis.Normed.Module.Multilinear.Curry
import TauCeti.Topology.MetricSpace.Pseudo.Constructions

/-!
# Second countability of the spaces of functions supported in a compact set

For a compact set `K` in a real normed space `E` and a second countable real normed space `F`, the
space `𝓓^{n}_{K}(E, F)` of `C^n` functions `E → F` supported in `K` is second countable
(`ContDiffMapSupportedIn.instSecondCountableTopology`), hence separable. Together with
completeness (`ContDiffMapSupportedIn.instCompleteSpace`) this makes it a separable Fréchet space
when `F` is a separable Banach space. Separability is what gives a countable dense family of
smooth functions supported in `K`, from which separable Banach spaces of smooth perturbations are
built by weighted series (`TauCeti.Analysis.Distribution.TestFunction.SynthesisCarrier`).

The topology of `𝓓^{n}_{K}(E, F)` is the coarsest one making each derivative
`f ↦ D^i f ∈ E →ᵇ (E [×i]→L[ℝ] F)` continuous. The space of all bounded continuous functions on `E`
is not separable, but `D^i f` vanishes off `K`, so its sup norm over `E` is its sup norm over `K`.
Hence the same topology is induced by the restrictions `D^i f|_K ∈ C(K, E [×i]→L[ℝ] F)`
(`ContDiffMapSupportedIn.restrictStructureMapCLM`, whose norm is the seminorm `N_i`), and the map
`f ↦ (D^i f|_K)ᵢ` into the countable product `Π i, C(K, E [×i]→L[ℝ] F)` is a uniform
embedding. When `E` is finite-dimensional, each factor is second countable because `K` is
a compact metric space and `E [×i]→L[ℝ] F` is second countable
(`ContinuousMultilinearMap.secondCountableTopology'`). When `E` is infinite-dimensional, every
compactly supported continuous function on `E` vanishes, so `𝓓^{n}_{K}(E, F)` is trivial.

## Main definitions

* `ContDiffMapSupportedIn.restrictStructureMapCLM`: the `i`-th derivative restricted to `K`, as a
  continuous linear map `𝓓^{n}_{K}(E, F) →L[𝕜] C(K, E [×i]→L[ℝ] F)`.

## Main results

* `ContDiffMapSupportedIn.norm_restrictStructureMapCLM`: the norm of the restricted `i`-th
  derivative is the seminorm `N_i`.
* `ContDiffMapSupportedIn.isUniformEmbedding_pi_restrictStructureMapCLM`: the restricted
  derivatives embed `𝓓^{n}_{K}(E, F)` uniformly into `Π i, C(K, E [×i]→L[ℝ] F)`.
* `ContDiffMapSupportedIn.instSecondCountableTopology`: `𝓓^{n}_{K}(E, F)` is second countable.

## References

* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Academic Press, 1967,
  Chapter 13 (the spaces `C^m_c(K)` of functions supported in a compact set).
-/

public section

open TopologicalSpace Topology Set
open scoped Distributions

namespace ContDiffMapSupportedIn

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [SMulCommClass ℝ 𝕜 F] {n : ℕ∞} {K : Compacts E}

variable (n) in
/-- The `i`-th derivative of `f ∈ 𝓓^{n}_{K}(E, F)`, restricted to `K`, as a continuous linear map
into the continuous maps on `K`. It is the derivative given by
`ContDiffMapSupportedIn.structureMapCLM` (zero when `n < i`), read on `K`, outside of which it
vanishes. -/
noncomputable def restrictStructureMapCLM (i : ℕ) :
    𝓓^{n}_{K}(E, F) →L[𝕜] C(K, E [×i]→L[ℝ] F) :=
  (ContinuousMap.linearIsometryBoundedOfCompact K (E [×i]→L[ℝ] F) 𝕜).symm.toContinuousLinearEquiv
    ∘L BoundedContinuousFunction.compContinuousCLM _ 𝕜 (ContinuousMap.subtypeVal (K : Set E))
    ∘L structureMapCLM 𝕜 n i

/-- The restricted derivative at a point of `K` is the structure map at that point. -/
theorem restrictStructureMapCLM_apply_eq (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) (x : K) :
    restrictStructureMapCLM 𝕜 n i f x = structureMapCLM 𝕜 n i f x :=
  (rfl)

@[simp]
theorem restrictStructureMapCLM_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) (x : K) :
    restrictStructureMapCLM 𝕜 n i f x = if i ≤ n then iteratedFDeriv ℝ i f x else 0 := by
  rw [restrictStructureMapCLM_apply_eq, structureMapCLM_apply]
  split_ifs <;> simp

/-- The norm of the `i`-th derivative restricted to `K` is the seminorm `N_i`: restricting to `K`
does not change sup norms, since derivatives vanish off `K`. -/
@[simp]
theorem norm_restrictStructureMapCLM (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ‖restrictStructureMapCLM 𝕜 n i f‖ = N[𝕜]_{K, n, i} f := by
  rw [ContDiffMapSupportedIn.seminorm_apply]
  refine le_antisymm
    ((ContinuousMap.norm_le _ (norm_nonneg (structureMapCLM 𝕜 n i f))).2 fun x ↦ ?_)
    ((BoundedContinuousFunction.norm_le (norm_nonneg (restrictStructureMapCLM 𝕜 n i f))).2
      fun x ↦ ?_)
  · rw [restrictStructureMapCLM_apply_eq]
    exact BoundedContinuousFunction.norm_coe_le_norm _ (x : E)
  by_cases hx : x ∈ K
  · rw [← restrictStructureMapCLM_apply_eq 𝕜 i f ⟨x, hx⟩]
    exact ContinuousMap.norm_coe_le_norm _ _
  · rw [structureMapCLM_apply_eq_zero_of_notMem 𝕜 i f hx, norm_zero]
    exact norm_nonneg _

/-- Restricting a derivative to `K` does not change sup distances. -/
theorem dist_restrictStructureMapCLM (i : ℕ) (f g : 𝓓^{n}_{K}(E, F)) :
    dist (restrictStructureMapCLM 𝕜 n i f) (restrictStructureMapCLM 𝕜 n i g) =
      dist (structureMapCLM 𝕜 n i f) (structureMapCLM 𝕜 n i g) := by
  calc dist (restrictStructureMapCLM 𝕜 n i f) (restrictStructureMapCLM 𝕜 n i g)
      = ‖restrictStructureMapCLM 𝕜 n i (f - g)‖ := by
        rw [map_sub]
        exact dist_eq_norm (restrictStructureMapCLM 𝕜 n i f) (restrictStructureMapCLM 𝕜 n i g)
    _ = ‖structureMapCLM 𝕜 n i (f - g)‖ :=
      (norm_restrictStructureMapCLM 𝕜 i (f - g)).trans
        (ContDiffMapSupportedIn.seminorm_apply 𝕜 i (f - g))
    _ = dist (structureMapCLM 𝕜 n i f) (structureMapCLM 𝕜 n i g) := by
      rw [map_sub]
      exact (dist_eq_norm (structureMapCLM 𝕜 n i f) (structureMapCLM 𝕜 n i g)).symm

/-- The derivatives restricted to `K` embed `𝓓^{n}_{K}(E, F)` uniformly into the product
`Π i, C(K, E [×i]→L[ℝ] F)`. -/
theorem isUniformEmbedding_pi_restrictStructureMapCLM :
    IsUniformEmbedding (ContinuousLinearMap.pi (restrictStructureMapCLM 𝕜 n) :
      𝓓^{n}_{K}(E, F) →L[𝕜] Π i, C(K, E [×i]→L[ℝ] F)) where
  injective f g hfg := structureMapCLM_zero_injective 𝕜 <| dist_eq_zero.1 <|
    (dist_restrictStructureMapCLM 𝕜 0 f g).symm.trans (dist_eq_zero.2 congr($hfg 0))
  toIsUniformInducing := by
    -- Each restricted derivative has the same distances as the corresponding structure map, so
    -- both families induce the uniform structure of `𝓓^{n}_{K}(E, F)`.
    have h := (isUniformEmbedding_pi_structureMapCLM 𝕜 (n := n) (K := K) (E := E)
      (F := F)).isUniformInducing
    rw [isUniformInducing_iff_uniformSpace] at h ⊢
    rw [← h, Pi.uniformSpace_eq, Pi.uniformSpace_eq, UniformSpace.comap_iInf,
      UniformSpace.comap_iInf]
    refine iInf_congr fun i ↦ ?_
    rw [← UniformSpace.comap_comap, ← UniformSpace.comap_comap, ContinuousLinearMap.coe_pi',
      ContinuousLinearMap.coe_pi']
    exact TauCeti.uniformSpace_comap_eq_of_dist_eq fun f g ↦
      dist_restrictStructureMapCLM 𝕜 i f g

/-- **`𝓓^{n}_{K}(E, F)` is second countable**, hence separable, for second countable `F`. -/
instance instSecondCountableTopology [SecondCountableTopology F] :
    SecondCountableTopology 𝓓^{n}_{K}(E, F) := by
  by_cases hE : FiniteDimensional ℝ E
  · exact (isUniformEmbedding_pi_restrictStructureMapCLM ℝ).isInducing.secondCountableTopology
  · -- On an infinite-dimensional space, a compactly supported continuous function vanishes.
    have : Subsingleton 𝓓^{n}_{K}(E, F) := ⟨fun f g ↦ by
      have h (f : 𝓓^{n}_{K}(E, F)) : (f : E → F) = 0 :=
        (f.hasCompactSupport.eq_zero_or_finiteDimensional ℝ f.continuous).resolve_right hE
      exact ext fun x ↦ (congrFun (h f) x).trans (congrFun (h g) x).symm⟩
    infer_instance

end ContDiffMapSupportedIn
