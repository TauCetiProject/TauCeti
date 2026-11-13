/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
public import TauCeti.Topology.FiberBundle.Proper
public import TauCeti.Analysis.InnerProductSpace.Unitary

import TauCeti.Topology.Maps.IsEmpty

/-!
# Compact orthonormal frames over compact sets

The projection of the orthonormal frame bundle is proper when its frame domain is
finite-dimensional and the vector bundle has continuous fiber norm. Consequently its preimage
of every compact set is compact, by `IsProperMap.isCompact_preimage`. No dimension-matching
hypothesis is needed: when a frame exists it identifies the model fiber with the frame domain,
and otherwise the frame bundle is empty. This gives a compact parameter space for uniform
estimates in rescaled normal coordinates over compact sets of centers and all frames.

## References

* [frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public noncomputable section

open Bundle

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V]

namespace TauCeti.OrthonormalFrameBundle

variable {B F : Type*} {E : B → Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace B] [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [TauCeti.ContinuousFiberNorm F E]
  [FiniteDimensional 𝕜 V]

/-- For a finite-dimensional frame domain, the orthonormal-frame projection of a vector
bundle with continuous fiber norm is proper. -/
theorem isProperMap_proj :
    IsProperMap (proj : OrthonormalFrameBundle 𝕜 F E V → B) := by
  cases isEmpty_or_nonempty (OrthonormalFrameBundle 𝕜 F E V) with
  | inl h =>
    exact Topology.IsClosedEmbedding.isProperMap (.of_isEmpty _)
  | inr h =>
    obtain ⟨⟨x, φ⟩⟩ := h
    let e := trivializationAt F E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
    let L : V ≃ₗ[𝕜] F := φ.toLinearEquiv.trans (e.continuousLinearEquivAt 𝕜 x hx).toLinearEquiv
    have : FiniteDimensional 𝕜 F := L.finiteDimensional
    have : ProperSpace V := FiniteDimensional.proper_rclike 𝕜 V
    apply TauCeti.isProperMap_of_forall_exists_trivialization
      (F := unitary (V →L[𝕜] V))
    intro y
    obtain ⟨t, hyt, -⟩ := exists_trivialization (E := E) L.finrank_eq y
    exact ⟨t, hyt⟩

end TauCeti.OrthonormalFrameBundle
