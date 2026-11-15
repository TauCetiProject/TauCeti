/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Orthogonality of product orthonormal bases for a quadratic form

Let `V ⊕ W` be the `L²` product `WithLp 2 (V × W)` of two inner product spaces, with a quadratic
form `Q` satisfying `Q (v, w) = Q₁ v + Q₂ w`. If orthonormal bases `b₁` of `V` and `b₂` of `W`
are orthogonal for the polar forms of `Q₁` and `Q₂`, then the product orthonormal basis
`b₁.prod b₂` of `V ⊕ W` is orthogonal for the polar form of `Q`. This is the `WithLp` form of
`QuadraticMap.isOrthoᵢ_associated_prod`.

## Main results

* `OrthonormalBasis.isOrthoᵢ_associated_prod`: the product of orthogonal orthonormal bases is
  orthogonal for `Q`.
* `QuadraticMap.apply_prod_eq_add_of_neg_norm_sq`: when `Q₁`, `Q₂`, and `Q` on `WithLp 2 (V × W)`
  are each minus the squared norm, `Q` splits additively as `Q₁ x.1 + Q₂ x.2`.
-/

public section

namespace OrthonormalBasis

variable {𝕜 V W ι₁ ι₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [Fintype ι₁] [Fintype ι₂]
  {Q₁ : QuadraticForm 𝕜 V} {Q₂ : QuadraticForm 𝕜 W} {Q : QuadraticForm 𝕜 (WithLp 2 (V × W))}

/-- If `Q (v, w) = Q₁ v + Q₂ w` and the orthonormal bases `b₁` of `V` and `b₂` of `W` are
orthogonal for the polar forms of `Q₁` and `Q₂`, then the product orthonormal basis `b₁.prod b₂`
of `WithLp 2 (V × W)` is orthogonal for the polar form of `Q`. -/
theorem isOrthoᵢ_associated_prod (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    {b₁ : OrthonormalBasis ι₁ 𝕜 V} (hb₁ : (QuadraticMap.associated Q₁).IsOrthoᵢ b₁.toBasis)
    {b₂ : OrthonormalBasis ι₂ 𝕜 W} (hb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis) :
    (QuadraticMap.associated Q).IsOrthoᵢ (b₁.prod b₂).toBasis := by
  have hcomp : Q = (Q₁.prod Q₂).comp (WithLp.linearEquiv 2 𝕜 (V × W)).toLinearMap :=
    QuadraticMap.ext fun x ↦ by simp [hQ]
  have h := QuadraticMap.isOrthoᵢ_associated_prod hb₁ hb₂
  rw [LinearMap.isOrthoᵢ_def] at h ⊢
  intro i j hij
  simp only [OrthonormalBasis.coe_toBasis, hcomp, QuadraticMap.associated_comp,
    LinearMap.compl₁₂_apply]
  rcases i with i | i <;> rcases j with j | j
  · simpa using h _ _ hij
  · simp
  · simp
  · simpa using h _ _ hij

end OrthonormalBasis

namespace QuadraticMap

/-- When `Q₁`, `Q₂`, and `Q` on `WithLp 2 (V × W)` are each minus the squared norm, `Q` splits
additively as `Q₁ x.1 + Q₂ x.2`. -/
theorem apply_prod_eq_add_of_neg_norm_sq {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
    (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (hQ : ∀ x, Q x = -‖x‖ ^ 2) (x : WithLp 2 (V × W)) :
    Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2 := by
  rw [hQ, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_fst, WithLp.ofLp_snd]
  ring

end QuadraticMap
