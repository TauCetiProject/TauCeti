/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
import TauCeti.Data.Fin.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Orthonormal frames of products

A product frame `((v₁, 0), …, (v_k, 0), (0, w₁), …, (0, w_l))` of the `L²` product
`WithLp 2 (V × W)` is orthonormal exactly when `v` and `w` are.

Let `V ⊕ W` be the `L²` product `WithLp 2 (V × W)` of two inner product spaces, with a quadratic
form `Q` satisfying `Q (v, w) = Q₁ v + Q₂ w`. If orthonormal bases `b₁` of `V` and `b₂` of `W`
are orthogonal for the polar forms of `Q₁` and `Q₂`, then the product orthonormal basis
`b₁.prod b₂` of `V ⊕ W` is orthogonal for the polar form of `Q`. This is the `WithLp` form of
`QuadraticMap.isOrthoᵢ_associated_prod`.

## Main results

* `TauCeti.orthonormal_append_toLp_iff`: orthonormality of a product frame.
* `OrthonormalBasis.isOrthoᵢ_associated_prod`: the product of orthogonal orthonormal bases is
  orthogonal for `Q`.
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

namespace TauCeti

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] {k l : ℕ}

/-- A product frame `((v₁, 0), …, (v_k, 0), (0, w₁), …, (0, w_l))` of `V ⊕ W` is orthonormal
exactly when `v` and `w` are. -/
theorem orthonormal_append_toLp_iff {v : Fin k → V} {w : Fin l → W} :
    Orthonormal 𝕜 (Fin.append (fun i ↦ WithLp.toLp 2 (v i, (0 : W)))
      (fun j ↦ WithLp.toLp 2 ((0 : V), w j))) ↔ Orthonormal 𝕜 v ∧ Orthonormal 𝕜 w := by
  classical
  simp [orthonormal_iff_ite, Fin.forall_fin_add, forall_and,
    (Fin.castAdd_injective _ _).eq_iff, (Fin.natAdd_injective _ _).eq_iff]

end TauCeti
