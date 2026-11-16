/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.Orientation.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Orthogonality and orientation of product orthonormal bases

Let `V ⊕ W` be the `L²` product `WithLp 2 (V × W)` of two inner product spaces, with a quadratic
form `Q` satisfying `Q (v, w) = Q₁ v + Q₂ w`. If orthonormal bases `b₁` of `V` and `b₂` of `W`
are orthogonal for the polar forms of `Q₁` and `Q₂`, then the product orthonormal basis
`b₁.prod b₂` of `V ⊕ W` is orthogonal for the polar form of `Q`. This is the `WithLp` form of
`QuadraticMap.isOrthoᵢ_associated_prod`.

Over `ℝ`, the orientation of the reindexed product orthonormal basis
`(b₁.prod b₂).reindex finSumFinEquiv` equals the canonical product orientation `Orientation.prod`
of `b₁` and `b₂` transported along `(WithLp.linearEquiv 2 ℝ (V × W)).symm`.

## Main results

* `OrthonormalBasis.isOrthoᵢ_associated_prod`: the product of orthogonal orthonormal bases is
  orthogonal for `Q`.
* `OrthonormalBasis.orientation_reindex_prod`: the orientation of the reindexed `L²` product of two
  real orthonormal bases is `Orientation.prod` transported along
  `(WithLp.linearEquiv 2 ℝ (V × W)).symm`.
-/

public section

namespace OrthonormalBasis

section Ortho

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

end Ortho

/-- The orientation of the reindexed `L²` product of two orthonormal bases is the canonical
`Orientation.prod` of their orientations transported along
`(WithLp.linearEquiv 2 ℝ (V × W)).symm`. -/
theorem orientation_reindex_prod {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] {n m : ℕ} (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (b₂ : OrthonormalBasis (Fin m) ℝ W) (hn : Module.finrank ℝ V = n)
    (hm : Module.finrank ℝ W = m) :
    ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation =
      (Orientation.prod b₁.toBasis.orientation b₂.toBasis.orientation hn hm).map (Fin (n + m))
        (WithLp.linearEquiv 2 ℝ (V × W)).symm := by
  rw [Orientation.prod_basis_orientation, ← Module.Basis.orientation_map]
  congr 1
  refine Module.Basis.eq_of_apply_eq (Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_)) <;>
    simp [Module.Basis.prod_apply]

end OrthonormalBasis
