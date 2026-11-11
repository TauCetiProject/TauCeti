/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Inverse
import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic

/-!
# The inverse of an injective symmetric operator is self-adjoint

Let `S` be an injective bounded symmetric operator on a Hilbert space `E`. Its inverse
`A = S⁻¹`, the partial linear map with domain the range of `S`
(`LinearPMap.inverse` applied to `S` on the full domain), is self-adjoint
(`ContinuousLinearMap.isSelfAdjoint_inverse_toPMap_top`). The range of `S` is dense, its
orthogonal complement being the kernel of `S`, so `A` is densely defined. It is symmetric because
`S` is. Its adjoint is no larger than `A`: if `⟪A† y, S a⟫ = ⟪y, a⟫` for every `a`, then
`S (A† y) = y` by symmetry of `S`, so `y` lies in the range of `S` and `A y = A† y`.

This is how the self-adjoint realization of an elliptic operator under a boundary condition is
obtained from its bounded symmetric solution operator.

## Main results

* `ContinuousLinearMap.isSelfAdjoint_inverse_toPMap_top`: the inverse of an injective bounded
  symmetric operator on a Hilbert space is self-adjoint.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Chapter VIII.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Chapter 3.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open LinearPMap
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {S : E →L[𝕜] E}

/-- **The inverse of an injective symmetric operator is self-adjoint.** For an injective bounded
symmetric operator `S` on a Hilbert space, the partial linear map `S⁻¹`, with domain the range of
`S`, is self-adjoint. -/
theorem isSelfAdjoint_inverse_toPMap_top [CompleteSpace E]
    (hsymm : (S : E →ₗ[𝕜] E).IsSymmetric) (hS : Function.Injective S) :
    IsSelfAdjoint ((S : E →ₗ[𝕜] E).toPMap ⊤).inverse := by
  set A := ((S : E →ₗ[𝕜] E).toPMap ⊤).inverse with hA
  have hdense : Dense (A.domain : Set E) := by
    rw [hA, domain_inverse_toPMap_top, LinearMap.coe_range, ContinuousLinearMap.coe_coe]
    exact hsymm.denseRange_of_injective hS
  -- Every point of the domain is `S a`, and `A (S a) = a`.
  have hdom (x : A.domain) : S (A x) = x :=
    (inverse_toPMap_top_apply_eq_iff hS x (A x)).1 rfl
  have hformal : A.IsFormalAdjoint A := fun x y ↦ by
    conv_lhs => rw [← hdom y]
    conv_rhs => rw [← hdom x]
    exact (hsymm (A x) (A y)).symm
  rw [isSelfAdjoint_def]
  refine le_antisymm (le_of_le_graph fun p hp ↦ ?_) (hformal.le_adjoint hdense)
  -- A point `(y, A† y)` of the graph of `A†` satisfies `S (A† y) = y`, by symmetry of `S`.
  obtain ⟨y, h1, h2⟩ := (mem_graph_iff _).1 hp
  rw [mem_graph_inverse_toPMap_top_iff hS, ← h1, ← h2]
  refine ext_inner_right 𝕜 fun a ↦ ?_
  have h := adjoint_isFormalAdjoint hdense y ⟨S a, apply_mem_domain_inverse_toPMap_top a⟩
  rw [← ContinuousLinearMap.coe_coe, hsymm, ContinuousLinearMap.coe_coe, h,
    inverse_toPMap_top_apply hS]

end ContinuousLinearMap
