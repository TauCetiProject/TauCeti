/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The inner product as a continuous sesquilinear map

Forgetting the continuity of the inner product `innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜` gives the
sesquilinear map `innerₛₗ 𝕜` (`ContinuousLinearMap.toLinearMap₁₂_innerSL`); over `ℝ` this is the
bilinear form `innerₗ E`, which is defined as `innerₛₗ ℝ`. Together with the conversion rules
of `TauCeti/Topology/Algebra/Module/Spaces/ContinuousLinearMap.lean`, this turns metric lowerings
`innerSL ℝ ∘L T` into the bilinear forms `innerₗ E ∘ₗ T`, to which the algebraic API of bilinear
forms applies.

An operator `T` whose matrix coefficients satisfy `‖⟪η, T ξ⟫‖ ≤ C ‖ξ‖ ‖η‖` has norm at most `C`
(`ContinuousLinearMap.opNorm_le_of_norm_inner_le`). An operator `D` with
`⟪D f, g⟫ = ⟪H (T f), T g⟫ + ⟪w, S f g⟫` has norm at most `‖T‖² ‖H‖ + ‖S‖ ‖w‖`
(`ContinuousLinearMap.opNorm_le_of_forall_inner_eq`); this is the pointwise bound for the Hessian
of a composition `u ∘ Φ`, with `T = DΦ` and `S = D²Φ`.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

/-- Forgetting continuity of the inner product gives the sesquilinear map `innerₛₗ 𝕜`. -/
@[simp]
theorem toLinearMap₁₂_innerSL {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    toLinearMap₁₂ (innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜) = innerₛₗ 𝕜 :=
  LinearMap.ext₂ fun _ _ ↦ by
    rw [toLinearMap₁₂_apply_apply_apply, innerSL_apply_apply, innerₛₗ_apply_apply]

/-- An operator whose matrix coefficients satisfy `‖⟪η, T ξ⟫‖ ≤ C ‖ξ‖ ‖η‖` has norm at most `C`.
This is `ContinuousLinearMap.opNorm_le_of_re_inner_le` with the bound on all vectors. -/
theorem opNorm_le_of_norm_inner_le {𝕜 G G' : Type*} [RCLike 𝕜] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [NormedAddCommGroup G'] [InnerProductSpace 𝕜 G']
    {T : G →L[𝕜] G'} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ξ η, ‖⟪η, T ξ⟫_𝕜‖ ≤ C * ‖ξ‖ * ‖η‖) : ‖T‖ ≤ C :=
  opNorm_le_of_re_inner_le hC fun ξ η hξ hη ↦ by
    rw [← inner_conj_symm, RCLike.conj_re]
    simpa [hξ, hη] using (RCLike.re_le_norm _).trans (h ξ η)

/-- If `⟪D f, g⟫ = ⟪H (T f), T g⟫ + ⟪w, S f g⟫` for all `f` and `g`, with `‖T‖ ≤ L` and
`‖S‖ ≤ M`, then `‖D‖ ≤ L² ‖H‖ + M ‖w‖`. For `D` the Hessian of `u ∘ Φ`, `H` and `w` the Hessian
and gradient of `u`, `T = DΦ` and `S = D²Φ`, this is the pointwise bound for the Hessian under a
change of variables. -/
theorem opNorm_le_of_forall_inner_eq {E F G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] {D : E →L[ℝ] E} {H : F →L[ℝ] F} {T : E →L[ℝ] F}
    {S : E →L[ℝ] E →L[ℝ] G} {w : G} {L M : ℝ}
    (hD : ∀ f g : E, ⟪D f, g⟫_ℝ = ⟪H (T f), T g⟫_ℝ + ⟪w, S f g⟫_ℝ) (hT : ‖T‖ ≤ L)
    (hS : ‖S‖ ≤ M) :
    ‖D‖ ≤ L ^ 2 * ‖H‖ + M * ‖w‖ := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hT
  have hM : 0 ≤ M := (norm_nonneg S).trans hS
  refine opNorm_le_of_re_inner_le (by positivity) fun f g hf hg => ?_
  rw [RCLike.re_to_real, hD f g]
  have hTv (v : E) (hv : ‖v‖ = 1) : ‖T v‖ ≤ L :=
    (T.le_opNorm v).trans (by rw [hv, mul_one]; exact hT)
  have h1 : ⟪H (T f), T g⟫_ℝ ≤ L ^ 2 * ‖H‖ :=
    calc _ ≤ ‖H (T f)‖ * ‖T g‖ := real_inner_le_norm _ _
      _ ≤ (‖H‖ * L) * L := by
        gcongr
        · exact (H.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hTv f hf) (norm_nonneg _))
        · exact hTv g hg
      _ = L ^ 2 * ‖H‖ := by ring
  have h2 : ⟪w, S f g⟫_ℝ ≤ M * ‖w‖ :=
    calc _ ≤ ‖w‖ * ‖S f g‖ := real_inner_le_norm _ _
      _ ≤ ‖w‖ * M := by
        gcongr
        refine (S.le_opNorm₂ f g).trans ?_
        rw [hf, hg, mul_one, mul_one]
        exact hS
      _ = M * ‖w‖ := mul_comm _ _
  linarith

end ContinuousLinearMap
