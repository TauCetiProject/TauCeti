/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Inverse

/-!
# The inverse of an injective bounded self-adjoint operator

Let `T` be an injective bounded self-adjoint operator on a Hilbert space `H`. Its inverse
`A = ((T : H →ₗ[𝕜] H).toPMap ⊤).inverse`, defined on the range of `T` by `T (A x) = x`, is a
self-adjoint unbounded operator (`ContinuousLinearMap.isSelfAdjoint_inverse_toPMap_top`). This is
how self-adjoint realizations of elliptic operators are obtained from the solution operators of
their boundary value problems, for instance the Dirichlet realization of `-Δ` as the inverse of
the Dirichlet solution operator.

The range of `T` is dense, since its orthogonal complement is the kernel of `T† = T`. On it `A` is
symmetric: for `x = T a` and `y = T b`, `⟪A x, y⟫ = ⟪a, T b⟫ = ⟪T a, b⟫ = ⟪x, A y⟫`. Conversely, if
`y` lies in the domain of the adjoint `A†` and `w = A† y`, then `⟪T w, z⟫ = ⟪w, T z⟫ = ⟪y, z⟫` for
every `z`, so `y = T w` lies in the domain of `A`.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Chapter VIII.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace LinearPMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **The inverse of an injective bounded self-adjoint operator is self-adjoint.** -/
theorem isSelfAdjoint_inverse_toPMap_top (T : H →L[𝕜] H) (hT : IsSelfAdjoint T)
    (hinj : Function.Injective T) : IsSelfAdjoint ((T : H →ₗ[𝕜] H).toPMap ⊤).inverse := by
  have hsymm := hT.isSymmetric
  -- The domain `range T` is dense: a vector orthogonal to it lies in `ker T† = ker T = 0`.
  have hdense : Dense (((T : H →ₗ[𝕜] H).toPMap ⊤).inverse.domain : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro y hy
    refine hinj (ext_inner_right 𝕜 fun z => ?_)
    rw [map_zero, inner_zero_left, ← coe_coe, hsymm, coe_coe]
    exact Submodule.inner_left_of_mem_orthogonal (apply_mem_domain_inverse_toPMap_top T z) hy
  have hformal : ((T : H →ₗ[𝕜] H).toPMap ⊤).inverse.IsFormalAdjoint
      ((T : H →ₗ[𝕜] H).toPMap ⊤).inverse := by
    rintro ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨x, rfl⟩ := (mem_domain_inverse_toPMap_top_iff T).1 hx
    obtain ⟨y, rfl⟩ := (mem_domain_inverse_toPMap_top_iff T).1 hy
    rw [inverse_toPMap_top_apply T hinj, inverse_toPMap_top_apply T hinj]
    exact (hsymm x y).symm
  have hle := hformal.le_adjoint hdense
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  -- `y = T (A† y)`, tested against every `z`.
  have hkey (z : H) : ⟪((T : H →ₗ[𝕜] H).toPMap ⊤).inverse† ⟨y, hy⟩, T z⟫_𝕜 = ⟪y, z⟫_𝕜 := by
    have h := LinearPMap.adjoint_isFormalAdjoint hdense ⟨y, hy⟩
      ⟨T z, apply_mem_domain_inverse_toPMap_top T z⟩
    rwa [inverse_toPMap_top_apply T hinj] at h
  refine (mem_domain_inverse_toPMap_top_iff T).2
    ⟨((T : H →ₗ[𝕜] H).toPMap ⊤).inverse† ⟨y, hy⟩, ext_inner_right 𝕜 fun z => ?_⟩
  rw [← coe_coe, hsymm, coe_coe, hkey]

end ContinuousLinearMap
