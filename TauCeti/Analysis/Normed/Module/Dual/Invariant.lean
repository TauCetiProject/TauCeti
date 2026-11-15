/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import TauCeti.Analysis.LocallyConvex.WeakDual.Annihilator
public import TauCeti.Analysis.Normed.Module.Annihilator

/-!
# Invariant subspaces of adjoints

The adjoint of a continuous linear operator `T : E →L[𝕜] E` is precomposition
`ContinuousLinearMap.precomp 𝕜 T` on the continuous dual. Annihilators are Mathlib's
`Submodule.orthogonalBilin` for the canonical pairing `topDualPairing`: for `S ≤ E`,
`S.orthogonalBilin (topDualPairing 𝕜 E).flip` is the annihilator `Sᗮ` of `S` in the dual, and for
`G ≤ StrongDual 𝕜 E`, `G.orthogonalBilin (topDualPairing 𝕜 E)` is the preannihilator `G_⊥` of
`G` in `E`. Invariance under an operator is Mathlib's `Module.End.invtSubmodule`.

The annihilator of a `T`-invariant subspace is `T*`-invariant, and the preannihilator of a
`T*`-invariant subspace of the dual is `T`-invariant. Over `ℝ` or `ℂ` the double-annihilator
theorems turn these into correspondences: a norm-closed subspace `S` is `T`-invariant exactly when
`Sᗮ` is `T*`-invariant, and a weak-star closed subspace `G` of the dual is `T*`-invariant exactly
when `G_⊥` is `T`-invariant. Applied to the operators of a bounded module action and to their
adjoints, the dual action, this identifies the closed submodules of a Banach module with the
weak-star closed submodules of its dual module.

## Main results

* `ContinuousLinearMap.orthogonalBilin_topDualPairing_flip_mem_invtSubmodule_precomp`: the
  annihilator of a `T`-invariant subspace is `T*`-invariant.
* `ContinuousLinearMap.orthogonalBilin_topDualPairing_mem_invtSubmodule`: the preannihilator of a
  `T*`-invariant subspace is `T`-invariant.
* `ContinuousLinearMap.orthogonalBilin_topDualPairing_flip_mem_invtSubmodule_precomp_iff`: a
  closed subspace is `T`-invariant iff its annihilator is `T*`-invariant.
* `ContinuousLinearMap.orthogonalBilin_topDualPairing_mem_invtSubmodule_iff`: a weak-star closed
  subspace of the dual is `T*`-invariant iff its preannihilator is `T`-invariant.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §§2.6 and 3.1.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.6, dual modules.
-/

public section

namespace ContinuousLinearMap

open Module.End

variable {𝕜 E : Type*}

section Algebraic

variable [NormedField 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

/-- The annihilator of a `T`-invariant subspace is invariant under the adjoint of `T`. -/
theorem orthogonalBilin_topDualPairing_flip_mem_invtSubmodule_precomp {T : E →L[𝕜] E}
    {S : Submodule 𝕜 E} (hS : S ∈ invtSubmodule T.toLinearMap) :
    S.orthogonalBilin (topDualPairing 𝕜 E).flip ∈
      invtSubmodule (precomp 𝕜 T : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E).toLinearMap := by
  rw [mem_invtSubmodule_iff_forall_mem_of_mem] at hS ⊢
  intro φ hφ
  simp only [Submodule.mem_orthogonalBilin, LinearMap.flip_apply, topDualPairing_apply] at hφ ⊢
  intro x hx
  simpa using hφ (T x) (hS x hx)

/-- The preannihilator of a subspace of the dual invariant under the adjoint of `T` is
`T`-invariant. -/
theorem orthogonalBilin_topDualPairing_mem_invtSubmodule {T : E →L[𝕜] E}
    {G : Submodule 𝕜 (StrongDual 𝕜 E)}
    (hG : G ∈ invtSubmodule (precomp 𝕜 T : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E).toLinearMap) :
    G.orthogonalBilin (topDualPairing 𝕜 E) ∈ invtSubmodule T.toLinearMap := by
  rw [mem_invtSubmodule_iff_forall_mem_of_mem] at hG ⊢
  intro x hx
  simp only [Submodule.mem_orthogonalBilin, topDualPairing_apply] at hx ⊢
  intro φ hφ
  simpa using hx _ (hG φ hφ)

end Algebraic

section Closed

variable [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A norm-closed subspace is `T`-invariant exactly when its annihilator is invariant under the
adjoint of `T`. -/
theorem orthogonalBilin_topDualPairing_flip_mem_invtSubmodule_precomp_iff (T : E →L[𝕜] E)
    {S : Submodule 𝕜 E} (hS : IsClosed (S : Set E)) :
    S.orthogonalBilin (topDualPairing 𝕜 E).flip ∈
        invtSubmodule (precomp 𝕜 T : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E).toLinearMap ↔
      S ∈ invtSubmodule T.toLinearMap := by
  refine ⟨fun h ↦ ?_, orthogonalBilin_topDualPairing_flip_mem_invtSubmodule_precomp⟩
  have := orthogonalBilin_topDualPairing_mem_invtSubmodule h
  rwa [Submodule.orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure,
    hS.submodule_topologicalClosure_eq] at this

end Closed

section WeakStarClosed

variable [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

/-- A weak-star closed subspace of the dual is invariant under the adjoint of `T` exactly when
its preannihilator is `T`-invariant. -/
theorem orthogonalBilin_topDualPairing_mem_invtSubmodule_iff (T : E →L[𝕜] E)
    {G : Submodule 𝕜 (StrongDual 𝕜 E)}
    (hG : IsClosed (G.map StrongDual.toWeakDual.toLinearMap : Set (WeakDual 𝕜 E))) :
    G.orthogonalBilin (topDualPairing 𝕜 E) ∈ invtSubmodule T.toLinearMap ↔
      G ∈ invtSubmodule (precomp 𝕜 T : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E).toLinearMap := by
  refine ⟨fun h ↦ ?_, orthogonalBilin_topDualPairing_mem_invtSubmodule⟩
  -- By the weak-star double-annihilator theorem, `G` is the annihilator of its preannihilator.
  have hGG : (G.orthogonalBilin (topDualPairing 𝕜 E)).orthogonalBilin
      (topDualPairing 𝕜 E).flip = G := by
    apply Submodule.map_injective_of_injective (f := StrongDual.toWeakDual.toLinearMap)
      StrongDual.toWeakDual.injective
    rw [Submodule.map_orthogonalBilin_flip_orthogonalBilin_eq_topologicalClosure,
      hG.submodule_topologicalClosure_eq]
  rw [← hGG]
  exact orthogonalBilin_topDualPairing_flip_mem_invtSubmodule_precomp h

end WeakStarClosed

end ContinuousLinearMap
