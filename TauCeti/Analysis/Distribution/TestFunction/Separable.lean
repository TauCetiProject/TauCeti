/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import TauCeti.Topology.MetricSpace.Pseudo.Constructions

/-!
# Second countability of the spaces of functions supported in a compact set

For a compact set `K` in a finite-dimensional real normed space `E` and a finite-dimensional real
normed space `F`, the space `𝓓^{n}_{K}(E, F)` of `C^n` functions `E → F` supported in `K` is second
countable (`ContDiffMapSupportedIn.instSecondCountableTopology`), hence separable. Together with
completeness (`ContDiffMapSupportedIn.instCompleteSpace`) this makes it a separable Fréchet space.
Separability is what gives a countable dense family of smooth functions supported in `K`, from
which separable Banach spaces of smooth perturbations are built by weighted series
(`TauCeti.Analysis.Distribution.TestFunction.SynthesisCarrier`).

The topology of `𝓓^{n}_{K}(E, F)` is the coarsest one making each derivative
`f ↦ D^i f ∈ E →ᵇ (E [×i]→L[ℝ] F)` continuous. The space of all bounded continuous functions on `E`
is not separable, but `D^i f` vanishes off `K`, so its sup norm over `E` is its sup norm over `K`.
Hence the same topology is induced by the restrictions `D^i f|_K ∈ C(K, E [×i]→L[ℝ] F)`
(`ContDiffMapSupportedIn.dist_restrictStructureMap`), and `f ↦ (D^i f|_K)ᵢ` embeds
`𝓓^{n}_{K}(E, F)` into the countable product `Π i, C(K, E [×i]→L[ℝ] F)`. Each factor is second
countable because `K` is a compact metric space and `E [×i]→L[ℝ] F` is finite-dimensional.

The finite-dimensionality of `F` is used only through the second countability of the spaces
`E [×i]→L[ℝ] F` of multilinear maps.

## Main results

* `ContDiffMapSupportedIn.isInducing_restrictStructureMap`: the restricted derivatives embed
  `𝓓^{n}_{K}(E, F)` topologically into `Π i, C(K, E [×i]→L[ℝ] F)`.
* `ContDiffMapSupportedIn.instSecondCountableTopology`: `𝓓^{n}_{K}(E, F)` is second countable.

## References

* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Academic Press, 1967,
  Chapter 13 (the spaces `C^m_c(K)` of functions supported in a compact set).
-/

public section

open TopologicalSpace Topology Set
open scoped Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {n : ℕ∞} {K : Compacts E}

variable (n) in
/-- The `i`-th derivative of `f ∈ 𝓓^{n}_{K}(E, F)`, restricted to `K`, as a continuous map on `K`.
It is the derivative given by `ContDiffMapSupportedIn.structureMapLM` (zero when `n < i`), read on
`K`, outside of which it vanishes. -/
noncomputable def restrictStructureMap (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    C(K, E [×i]→L[ℝ] F) :=
  (structureMapLM ℝ n i f).toContinuousMap.restrict K

/-- The restricted derivative at a point of `K` is the structure map at that point. -/
theorem restrictStructureMap_apply_eq (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) (x : K) :
    restrictStructureMap n i f x = structureMapLM ℝ n i f x :=
  (rfl)

@[simp]
theorem restrictStructureMap_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) (x : K) :
    restrictStructureMap n i f x = if i ≤ n then iteratedFDeriv ℝ i f x else 0 := by
  rw [restrictStructureMap_apply_eq, structureMapLM_apply]
  split_ifs <;> simp

/-- The structure maps vanish off `K`. -/
theorem structureMapLM_apply_eq_zero_of_notMem (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) {x : E}
    (hx : x ∉ K) : structureMapLM ℝ n i f x = 0 := by
  rw [structureMapLM_apply]
  split_ifs
  · exact f.iteratedFDeriv_zero_on_compl hx
  · simp

/-- Restricting a derivative to `K` does not change sup distances, since derivatives vanish off
`K`. -/
theorem dist_restrictStructureMap (i : ℕ) (f g : 𝓓^{n}_{K}(E, F)) :
    dist (restrictStructureMap n i f) (restrictStructureMap n i g) =
      dist (structureMapLM ℝ n i f) (structureMapLM ℝ n i g) := by
  refine le_antisymm ((ContinuousMap.dist_le dist_nonneg).2 fun x ↦ ?_) ?_
  · rw [restrictStructureMap_apply_eq, restrictStructureMap_apply_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist (x : E)
  refine (BoundedContinuousFunction.dist_le dist_nonneg).2 fun x ↦ ?_
  by_cases hx : x ∈ K
  · rw [← restrictStructureMap_apply_eq i f ⟨x, hx⟩, ← restrictStructureMap_apply_eq i g ⟨x, hx⟩]
    exact ContinuousMap.dist_apply_le_dist (f := restrictStructureMap n i f)
      (g := restrictStructureMap n i g) ⟨x, hx⟩
  · rw [structureMapLM_apply_eq_zero_of_notMem i f hx,
      structureMapLM_apply_eq_zero_of_notMem i g hx, dist_self]
    exact dist_nonneg

/-- The derivatives restricted to `K` embed `𝓓^{n}_{K}(E, F)` topologically into the product
`Π i, C(K, E [×i]→L[ℝ] F)`. -/
theorem isInducing_restrictStructureMap :
    IsInducing fun (f : 𝓓^{n}_{K}(E, F)) (i : ℕ) ↦ restrictStructureMap n i f := by
  have h : (topologicalSpace : TopologicalSpace 𝓓^{n}_{K}(E, F)) =
      ⨅ i : ℕ, induced (restrictStructureMap n i) inferInstance :=
    iInf_congr fun i ↦ PseudoMetricSpace.induced_topology_eq_of_dist_eq fun f g ↦
      (dist_restrictStructureMap i f g).symm
  -- `inducing_iInf_to_pi` is stated for the infimum topology, which is the topology of
  -- `𝓓^{n}_{K}(E, F)` by `h`.
  convert inducing_iInf_to_pi fun i : ℕ ↦ restrictStructureMap (K := K) (F := F) n i

/-- **`𝓓^{n}_{K}(E, F)` is second countable**, hence separable, for finite-dimensional `E` and
`F`. -/
instance instSecondCountableTopology [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] :
    SecondCountableTopology 𝓓^{n}_{K}(E, F) := by
  have (i : ℕ) : FiniteDimensional ℝ (E [×i]→L[ℝ] F) :=
    Module.Finite.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  exact isInducing_restrictStructureMap.secondCountableTopology

end ContDiffMapSupportedIn
