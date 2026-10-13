/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# Precomposition with a surjection from a compact space

If `q : A → B` is a continuous surjection from a compact space `A` to a Hausdorff space `B`, then
precomposition with `q` embeds the space `C(B, X)` of continuous maps, with the compact-open
topology, in `C(A, X)`. The reason is that the preimage of a compact subset of `B` under `q` is
closed, hence compact, so every subbasic compact-open condition on `B` is the pullback of a
subbasic compact-open condition on `A`.

Combined with the fact that a continuous surjection from a compact space to a Hausdorff space is a
quotient map, this identifies mapping spaces out of a quotient such as `I^n / ∂I^n ≅ S^n` with
subspaces of mapping spaces out of the cube.

## Main declarations

* `ContinuousMap.isInducing_precomp`: precomposition with a continuous surjection `q : A → B`
  from a compact space to a Hausdorff space is inducing, on the compact-open topologies.
* `ContinuousMap.isEmbedding_precomp`: the same, as an embedding.
-/

public section

open Set Topology

namespace ContinuousMap

variable {A B X : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]

/-- Precomposition with a continuous surjection `q` from a compact space is inducing for the
compact-open topologies. -/
theorem isInducing_precomp [CompactSpace A] [T2Space B] (q : C(A, B)) (hq : Function.Surjective q) :
    IsInducing (fun f : C(B, X) => f.comp q) := by
  refine ⟨le_antisymm (continuous_iff_le_induced.mp (continuous_precomp q)) ?_⟩
  refine le_generateFrom ?_
  rintro _ ⟨K, hK, U, hU, rfl⟩
  have hpre : IsOpen {g : C(A, X) | MapsTo g (q ⁻¹' K) U} :=
    isOpen_setOfPred_mapsTo ((hK.isClosed.preimage q.continuous).isCompact) hU
  refine ⟨_, hpre, ?_⟩
  ext f
  constructor
  · intro h b hb
    obtain ⟨a, rfl⟩ := hq b
    exact h hb
  · intro h a ha
    exact h ha

/-- Precomposition with a continuous surjection `q` from a compact space is an embedding. -/
theorem isEmbedding_precomp [CompactSpace A] [T2Space B] (q : C(A, B))
    (hq : Function.Surjective q) :
    IsEmbedding (fun f : C(B, X) => f.comp q) :=
  ⟨isInducing_precomp q hq, fun _ _ h => (cancel_right hq).1 h⟩

end ContinuousMap
