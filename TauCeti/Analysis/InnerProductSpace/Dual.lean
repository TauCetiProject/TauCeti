/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The Riesz isomorphism and `innerSL`

On a Hilbert space `E`, the Riesz isomorphism `InnerProductSpace.toDual 𝕜 E` is the map
`innerSL 𝕜 : E →L⋆[𝕜] StrongDual 𝕜 E`, upgraded to a conjugate-linear isometric equivalence. So its
inverse undoes `innerSL` on either side.

## Main results

* `InnerProductSpace.toDual_symm_innerSL`: `(toDual 𝕜 E).symm (innerSL 𝕜 w) = w`.
* `InnerProductSpace.innerSL_toDual_symm`: `innerSL 𝕜 ((toDual 𝕜 E).symm q) = q`.
* `InnerProductSpace.apply_toDual_symm_eq_conj`: `β(α♯) = conj (α(β♯))`, writing `α♯` for
  `(toDual 𝕜 E).symm α`.
* `InnerProductSpace.apply_toDual_symm_self`: `q(q♯) = ‖q‖²`.
* `InnerProductSpace.toDualSymmL`: over `ℝ`, the inverse Riesz map `q ↦ q♯` as a continuous
  linear map.
* `InnerProductSpace.isInvertible_of_apply_apply_eq_mul_inner`: over `ℝ`, a bilinear form that is
  a nonzero multiple of the inner product is invertible as a map to the dual.
-/

public section

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The inverse Riesz isomorphism sends the functional `innerSL 𝕜 w = ⟪w, ·⟫` back to `w`. -/
@[simp]
theorem toDual_symm_innerSL (w : E) : (toDual 𝕜 E).symm (innerSL 𝕜 w) = w :=
  (toDual 𝕜 E).symm_apply_eq.2 (by ext; simp)

/-- The functional `⟪(toDual 𝕜 E).symm q, ·⟫` represented by the inverse Riesz isomorphism is
`q`. -/
@[simp]
theorem innerSL_toDual_symm (q : StrongDual 𝕜 E) : innerSL 𝕜 ((toDual 𝕜 E).symm q) = q := by
  ext v; simp [toDual_symm_apply]

/-- Evaluating functionals at each other's Riesz representatives is conjugate-symmetric:
`β(α♯) = conj (α(β♯))`. Over `ℝ` this says `β(α♯) = α(β♯)`. -/
theorem apply_toDual_symm_eq_conj (α β : StrongDual 𝕜 E) :
    β ((toDual 𝕜 E).symm α) = starRingEnd 𝕜 (α ((toDual 𝕜 E).symm β)) := by
  rw [← toDual_symm_apply (y := β), ← toDual_symm_apply (y := α), inner_conj_symm]

/-- A functional evaluated at its own Riesz representative is its squared norm. -/
theorem apply_toDual_symm_self (q : StrongDual 𝕜 E) :
    q ((toDual 𝕜 E).symm q) = (‖q‖ : 𝕜) ^ 2 := by
  rw [← toDual_symm_apply, inner_self_eq_norm_sq_to_K, LinearIsometryEquiv.norm_map]

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- On a real Hilbert space the inverse Riesz isomorphism `q ↦ q♯ = (toDual ℝ F).symm q` is
linear; this is it as a continuous linear map. -/
noncomputable def toDualSymmL : StrongDual ℝ F →L[ℝ] F :=
  (toDual ℝ F).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem toDualSymmL_apply (q : StrongDual ℝ F) : toDualSymmL q = (toDual ℝ F).symm q :=
  (rfl)

/-- On a real Hilbert space, a bounded bilinear form `B(b, a) = c ⟪b, a⟫` with `c ≠ 0`, viewed as
a map to the dual, is invertible: it is `c` times the Riesz isomorphism. -/
theorem isInvertible_of_apply_apply_eq_mul_inner {c : ℝ} (hc : c ≠ 0)
    {B : F →L[ℝ] StrongDual ℝ F} (hB : ∀ b a, B b a = c * inner ℝ b a) : B.IsInvertible := by
  let e : F ≃L[ℝ] StrongDual ℝ F := (toDual ℝ F).toContinuousLinearEquiv
  refine ⟨(Units.mk0 c hc) • e,
    ContinuousLinearMap.ext fun b ↦ ContinuousLinearMap.ext fun a ↦ ?_⟩
  simpa [e] using (hB b a).symm

end Real

end InnerProductSpace
