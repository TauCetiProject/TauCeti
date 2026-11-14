/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel

/-!
# Orthonormal frames over a point of the sphere

An orthonormal `(k + 1)`-frame `(p, u₁, …, u_k)` of a real inner product space `E` is a point `p`
of the unit sphere together with an orthonormal `k`-frame `(u₁, …, u_k)` of the orthogonal
complement `p^⊥`, the tangent space of the sphere at `p`. So the Stiefel manifold `V_{k+1}(E)`
(`TauCeti.stiefel E (k + 1)`) is the space of orthonormal tangent `k`-frames of the unit sphere,
and its fibre over `p` under the projection to the first vector is the Stiefel manifold `V_k(p^⊥)`
of orthonormal `k`-frames of `p^⊥`. This file provides the inclusion of that fibre. For `k = 2`
it identifies the orthonormal triples `(p, u, v)` over `p` with the two-frames of `p^⊥`.

## Main declarations

* `TauCeti.stiefelFrameIncl`: the inclusion `V_k(p^⊥) → V_{k+1}(E)`, `u ↦ (p, u)`.
* `TauCeti.range_stiefelFrameIncl`: its range is the fibre over `p` of the projection to the
  first vector.
* `TauCeti.isClosedEmbedding_stiefelFrameIncl`: it is a closed embedding.
* `TauCeti.contMDiff_stiefelFrameIncl`: it is smooth.
-/

public section

open Metric Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)
  (k : ℕ)

/-- The inclusion `V_k(p^⊥) → V_{k+1}(E)`, `u ↦ (p, u)`, of the `k`-frames of the tangent space
at `p` as the fibre over `p` of the projection to the first vector. -/
def stiefelFrameIncl : C(stiefel (ℝ ∙ (p : E))ᗮ k, stiefel E (k + 1)) where
  toFun x := ⟨Matrix.vecCons (p : E) fun i => ((x : Fin k → (ℝ ∙ (p : E))ᗮ) i : E),
    mem_stiefel_iff.2 <| orthonormal_vecCons_iff.2
      ⟨norm_eq_of_mem_sphere p,
        fun i => Submodule.mem_orthogonal_singleton_iff_inner_right.1 (x.1 i).2,
        (mem_stiefel_iff.1 x.2).comp_linearIsometry (ℝ ∙ (p : E))ᗮ.subtypeₗᵢ⟩⟩
  continuous_toFun := Continuous.subtype_mk (continuous_const.matrixVecCons (continuous_pi fun i =>
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val))) _

variable {p k}

@[simp]
theorem coe_stiefelFrameIncl (x : stiefel (ℝ ∙ (p : E))ᗮ k) :
    ((stiefelFrameIncl p k x : stiefel E (k + 1)) : Fin (k + 1) → E) =
      Matrix.vecCons (p : E) fun i => ((x : Fin k → (ℝ ∙ (p : E))ᗮ) i : E) :=
  (rfl)

@[simp]
theorem stiefelProj_zero_stiefelFrameIncl (x : stiefel (ℝ ∙ (p : E))ᗮ k) :
    stiefelProj E (k + 1) 0 (stiefelFrameIncl p k x) = p :=
  Subtype.ext (by simp)

variable (p k)

/-- The frames of `p^⊥` are exactly the fibre over `p` of the projection `V_{k+1}(E) → Sⁿ` to the
first vector. -/
theorem range_stiefelFrameIncl :
    Set.range (stiefelFrameIncl p k) = stiefelProj E (k + 1) 0 ⁻¹' {p} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun x => by simp) fun y hy => ?_
  have hy0 : (y : Fin (k + 1) → E) 0 = p :=
    (coe_stiefelProj 0 y).symm.trans (congrArg Subtype.val hy)
  have hon := mem_stiefel_iff.1 y.2
  rw [← Matrix.cons_head_tail (y : Fin (k + 1) → E)] at hon
  have hmem (i : Fin k) : Matrix.vecTail (y : Fin (k + 1) → E) i ∈ (ℝ ∙ (p : E))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.2
      (hy0 ▸ (orthonormal_vecCons_iff.1 hon).2.1 i)
  refine ⟨⟨_, mem_stiefel_iff.2 ((orthonormal_vecCons_iff.1 hon).2.2.codRestrict _ hmem)⟩, ?_⟩
  refine Subtype.ext (funext (Fin.cases ?_ fun i => ?_))
  · rw [coe_stiefelFrameIncl, Matrix.cons_val_zero, hy0]
  · rw [coe_stiefelFrameIncl, Matrix.cons_val_succ]
    rfl

/-- The inclusion `V_k(p^⊥) → V_{k+1}(E)` is a closed embedding. -/
theorem isClosedEmbedding_stiefelFrameIncl : IsClosedEmbedding (stiefelFrameIncl p k) where
  toIsEmbedding := by
    refine IsEmbedding.subtypeVal.of_comp_iff.1 ?_
    have hcons : IsEmbedding (Matrix.vecCons (p : E) : (Fin k → E) → Fin (k + 1) → E) :=
      Function.LeftInverse.isEmbedding (f := Matrix.vecTail) (fun w => Matrix.tail_cons _ _)
        (continuous_pi fun i => continuous_apply i.succ) (by fun_prop)
    exact hcons.comp ((IsEmbedding.piMap fun _ => IsEmbedding.subtypeVal).comp
      IsEmbedding.subtypeVal)
  isClosed_range := by
    rw [range_stiefelFrameIncl]
    exact isClosed_singleton.preimage (continuous_stiefelProj 0)

/-- The inclusion `V_k(p^⊥) → V_{k+1}(E)` is injective. -/
theorem stiefelFrameIncl_injective : Function.Injective (stiefelFrameIncl p k) :=
  (isClosedEmbedding_stiefelFrameIncl p k).injective

/-- The inclusion `V_k(p^⊥) → V_{k+1}(E)` is smooth. -/
theorem contMDiff_stiefelFrameIncl [FiniteDimensional ℝ E] {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Fin (k * Module.finrank ℝ (ℝ ∙ (p : E))ᗮ - (k + 1).choose 2) → ℝ)
      𝓘(ℝ, Fin ((k + 1) * Module.finrank ℝ E - (k + 1 + 1).choose 2) → ℝ) r
      (stiefelFrameIncl p k) := by
  have hcons : ContDiff ℝ r fun w : Fin k → (ℝ ∙ (p : E))ᗮ =>
      (Matrix.vecCons (p : E) fun i => (w i : E) : Fin (k + 1) → E) := by
    refine contDiff_pi.2 (Fin.cases ?_ fun i => ?_)
    · simpa using contDiff_const
    · simp only [Matrix.cons_val_succ]
      exact (ℝ ∙ (p : E))ᗮ.subtypeL.contDiff.comp (contDiff_apply ℝ _ i)
  exact ContMDiff.codRestrict_stiefel (hcons.contMDiff.comp (contMDiff_coe_stiefel _ _))
    fun x => (stiefelFrameIncl p k x).2

end TauCeti
