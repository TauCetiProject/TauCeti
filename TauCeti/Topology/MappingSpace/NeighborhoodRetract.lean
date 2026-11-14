/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Subspace
public import TauCeti.Topology.Algebra.Module.LocallyContractible
public import TauCeti.Topology.CompactOpen

/-!
# Mapping spaces into neighbourhood retracts of vector spaces

Let `E` be a real topological vector space and let `X` be a *neighbourhood retract* of `E`: there
are a continuous map `i : X → E` with values in an open set `U` and a map `r : E → X`, continuous
on `U`, with `r ∘ i = id`. A smooth manifold is locally of this kind: an open neighbourhood of any
compact subset embeds in a Euclidean space, and a tubular neighbourhood of the image retracts onto
it.

For a compact space `K`, the mapping space `C(K, E)` with the compact-open topology is again a real
topological vector space, so it is strongly locally contractible, and so is its open subset of the
maps with values in `U`, which is `C(K, U)`
(`ContinuousMap.stronglyLocallyContractibleSpace_of_isOpen`). Postcomposition with `i` and with
`r` exhibits `C(K, X)` as a retract of `C(K, U)`. Hence `C(K, X)` is locally path-connected
(`ContinuousMap.locallyPathConnectedSpace_of_leftInverse`) and semilocally simply connected
(`ContinuousMap.semilocallySimplyConnectedSpace_of_leftInverse`): these are the hypotheses under
which the connected covering spaces of the path components of `C(K, X)` are classified by
subgroups of their fundamental groups. Compactness of `K` is what makes `C(K, U)` open in
`C(K, E)`.

The case of manifolds, and in particular of free loop spaces of manifolds, is in
`TauCeti.Geometry.Manifold.MappingSpace`.

## References

* R. S. Palais, *Homotopy theory of infinite dimensional manifolds*, Topology 5 (1966), 1–16,
  for mapping spaces from a compact space into absolute neighbourhood retracts.
-/

public section

open Function Set Topology TauCeti

namespace ContinuousMap

variable {K X E : Type*} [TopologicalSpace K] [TopologicalSpace X] [TopologicalSpace E] {U : Set E}

/-- A neighbourhood retract `X` of `E` gives a retraction of `C(K, U)` onto `C(K, X)`, by
postcomposition. -/
private theorem exists_leftInverse_postcomp {i : X → E} {r : E → X} (hi : Continuous i)
    (hiU : ∀ x, i x ∈ U) (hr : ContinuousOn r U) (hri : LeftInverse r i) :
    ∃ (s : C(K, X) → C(K, U)) (ρ : C(K, U) → C(K, X)),
      LeftInverse ρ s ∧ Continuous ρ ∧ Continuous s :=
  let i' : C(X, U) := ⟨fun x ↦ ⟨i x, hiU x⟩, hi.subtype_mk hiU⟩
  let r' : C(U, X) := ⟨U.domRestrict r, hr.domRestrict⟩
  ⟨i'.comp, r'.comp, fun f ↦ ext fun k ↦ hri (f k), continuous_postcomp r', continuous_postcomp i'⟩

variable [CompactSpace K] [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

variable (K) in
/-- For an open subset `U` of a real topological vector space `E` and a compact space `K`, the
mapping space `C(K, U)` is strongly locally contractible: it is an open subset of the real
topological vector space `C(K, E)`. -/
theorem stronglyLocallyContractibleSpace_of_isOpen (hU : IsOpen U) :
    StronglyLocallyContractibleSpace C(K, U) :=
  (isOpenEmbedding_postcomp ⟨Subtype.val, continuous_subtype_val⟩
    hU.isOpenEmbedding_subtypeVal).stronglyLocallyContractibleSpace

variable (K) in
/-- **Mapping spaces into a neighbourhood retract are locally path-connected.** If `X` is a
retract, through `i : X → E` and `r : E → X`, of an open subset `U` of a real topological vector
space `E`, then `C(K, X)` is locally path-connected for every compact space `K`. -/
theorem locallyPathConnectedSpace_of_leftInverse {i : X → E} {r : E → X} (hi : Continuous i)
    (hU : IsOpen U) (hiU : ∀ x, i x ∈ U) (hr : ContinuousOn r U) (hri : LeftInverse r i) :
    LocallyPathConnectedSpace C(K, X) :=
  have := stronglyLocallyContractibleSpace_of_isOpen K hU
  let ⟨_, _, hρs, hρ, hs⟩ := exists_leftInverse_postcomp (K := K) hi hiU hr hri
  hρs.locallyPathConnectedSpace hρ hs

variable (K) in
/-- **Mapping spaces into a neighbourhood retract are semilocally simply connected.** If `X` is a
retract, through `i : X → E` and `r : E → X`, of an open subset `U` of a real topological vector
space `E`, then `C(K, X)` is semilocally simply connected for every compact space `K`. -/
theorem semilocallySimplyConnectedSpace_of_leftInverse {i : X → E} {r : E → X}
    (hi : Continuous i) (hU : IsOpen U) (hiU : ∀ x, i x ∈ U) (hr : ContinuousOn r U)
    (hri : LeftInverse r i) : SemilocallySimplyConnectedSpace C(K, X) :=
  have := stronglyLocallyContractibleSpace_of_isOpen K hU
  let ⟨_, _, hρs, hρ, hs⟩ := exists_leftInverse_postcomp (K := K) hi hiU hr hri
  hρs.semilocallySimplyConnectedSpace hρ hs

end ContinuousMap
