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
`QuadraticMap.isOrthoᵢ_associated_prod`. For real inner product spaces of dimensions `n` and `m`,
reindexing `b₁.prod b₂` along `finSumFinEquiv` carries the product orientation `Orientation.prod`
transported along `(WithLp.linearEquiv 2 ℝ (V × W)).symm`.

## Main results

* `OrthonormalBasis.isOrthoᵢ_associated_prod`: the product of orthogonal orthonormal bases is
  orthogonal for `Q`.
* `OrthonormalBasis.orientation_reindex_prod`: the ordered `L²` product of two real orthonormal
  bases has the orientation transported from `Orientation.prod`.
-/

public section

namespace OrthonormalBasis

section QuadraticForm

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

end QuadraticForm

section Orientation

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] {n m : ℕ}

/-- The ordered `L²` product of two real orthonormal bases has the orientation transported from
`Orientation.prod` along `(WithLp.linearEquiv 2 ℝ (V × W)).symm`. -/
theorem orientation_reindex_prod (b₁ : OrthonormalBasis (Fin n) ℝ V)
    (b₂ : OrthonormalBasis (Fin m) ℝ W) (hn : Module.finrank ℝ V = n)
    (hm : Module.finrank ℝ W = m) :
    ((b₁.prod b₂).reindex finSumFinEquiv).toBasis.orientation =
      (b₁.toBasis.orientation.prod b₂.toBasis.orientation hn hm).map (Fin (n + m))
        (WithLp.linearEquiv 2 ℝ (V × W)).symm := by
  have hbasis : ((b₁.prod b₂).reindex finSumFinEquiv).toBasis =
      ((b₁.toBasis.prod b₂.toBasis).reindex finSumFinEquiv).map
        (WithLp.linearEquiv 2 ℝ (V × W)).symm := by
    refine Module.Basis.eq_of_apply_eq fun k ↦ ?_
    rcases h : finSumFinEquiv.symm k with i | j <;>
      simp [Module.Basis.prod_apply, h]
  rw [hbasis, Module.Basis.orientation_map, Orientation.prod_basis_orientation]

end Orientation

end OrthonormalBasis
