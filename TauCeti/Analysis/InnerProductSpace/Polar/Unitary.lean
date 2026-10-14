/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
public import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot
import TauCeti.Analysis.SpecialFunctions.Sqrt

/-!
# Unitary polar decomposition and near-isometries in finite dimension

Let `A : E →ₗ[𝕜] F` be a linear map between finite-dimensional real or complex inner product
spaces of the same dimension, with modulus `|A| = √(A† A)` (`LinearMap.operatorAbs`). The vectors
`|A| x` and `A x` have the same Gram data, so Gram rigidity provides a linear isometric equivalence
`U : E ≃ₗᵢ F` with `A = U |A|`. In particular every endomorphism of a finite-dimensional inner
product space is a unitary times its modulus.

A map `M` is a near-isometry with defect `δ` when `|‖M x‖² - ‖x‖²| ≤ δ ‖x‖²` for all `x`. Then
every eigenvalue `μ` of `M† M` satisfies `|μ - 1| ≤ δ`, so `|√μ - 1| ≤ δ` and the modulus is within
`δ` of the identity: `‖|M| x - x‖ ≤ δ ‖x‖`. Consequently every isometric polar factor `U` of `M` is
within `δ` of `M` itself, `‖M x - U x‖ ≤ δ ‖x‖`. Combined with the unitary polar decomposition,
this says that a square near-isometry is pointwise `δ`-close to a linear isometric equivalence.
No smallness assumption on `δ` is needed.

## Main declarations

* `LinearMap.exists_linearIsometryEquiv_comp_operatorAbs_eq`: `A = U |A|` for a linear isometric
  equivalence `U`, when the source and target have the same dimension.
* `LinearMap.norm_operatorAbs_apply_sub_le`: the modulus of a near-isometry with defect `δ` is
  within `δ` of the identity.
* `LinearMap.norm_apply_sub_le_of_comp_operatorAbs_eq`: a near-isometry with defect `δ` is within
  `δ` of each of its isometric polar factors.
* `LinearMap.exists_linearIsometryEquiv_comp_operatorAbs_eq_and_norm_apply_sub_le`: a
  near-isometry between spaces of the same dimension is `U |M|` for a linear isometric
  equivalence `U` within `δ` of it.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 7.3.1.
* N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008,
  §8.1 (approximation properties of the polar factor).
-/

public section

open Module Module.End
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Unitary polar decomposition.** A linear map between finite-dimensional inner product spaces
of the same dimension is a linear isometric equivalence composed with its modulus. For an
endomorphism, take `h := rfl`. -/
theorem exists_linearIsometryEquiv_comp_operatorAbs_eq (A : E →ₗ[𝕜] F)
    (h : finrank 𝕜 E = finrank 𝕜 F) :
    ∃ U : E ≃ₗᵢ[𝕜] F, (U : E →ₗ[𝕜] F) ∘ₗ A.operatorAbs = A := by
  let e₀ : E ≃ₗᵢ[𝕜] F :=
    (stdOrthonormalBasis 𝕜 E).repr.trans
      ((stdOrthonormalBasis 𝕜 F).reindex (finCongr h.symm)).repr.symm
  have hinner (x y : E) :
      ⟪e₀ (A.operatorAbs x), e₀ (A.operatorAbs y)⟫_𝕜 = ⟪A x, A y⟫_𝕜 := by
    rw [LinearIsometryEquiv.inner_map_map, ← A.isSymmetric_operatorAbs, ← comp_apply,
      operatorAbs_sq, comp_apply, adjoint_inner_left]
  obtain ⟨e, he⟩ := TauCeti.exists_linearIsometryEquiv_of_inner_eq hinner
  exact ⟨e₀.trans e, LinearMap.ext fun x ↦ he x⟩

/-- **Near-isometry square-root estimate.** If `|‖M x‖² - ‖x‖²| ≤ δ ‖x‖²` for every `x`, then the
modulus `|M| = √(M† M)` satisfies `‖|M| x - x‖ ≤ δ ‖x‖` for every `x`. -/
theorem norm_operatorAbs_apply_sub_le (M : E →ₗ[𝕜] F) {δ : ℝ}
    (hM : ∀ x, |‖M x‖ ^ 2 - ‖x‖ ^ 2| ≤ δ * ‖x‖ ^ 2) (x : E) :
    ‖M.operatorAbs x - x‖ ≤ δ * ‖x‖ := by
  let hT := (isPositive_adjoint_comp_self M).isSymmetric
  have hsub : M.operatorAbs - 1 = hT.cfc (fun μ ↦ √μ - 1) := by
    rw [(isPositive_adjoint_comp_self M).sqrt_unique M.isPositive_operatorAbs M.operatorAbs_sq]
    refine (hT.eq_cfc_iff _).mpr fun μ v hv ↦ ?_
    rw [sub_apply, IsPositive.sqrt_apply_of_apply_eq_smul _ hv, one_apply, RCLike.ofReal_sub,
      RCLike.ofReal_one, sub_smul, one_smul]
  have hx : M.operatorAbs x - x = (M.operatorAbs - 1) x := by simp
  rw [hx, hsub]
  refine hT.norm_cfc_apply_le _ (fun μ hμ ↦ ?_) x
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hnorm : ‖M v‖ ^ 2 = μ * ‖v‖ ^ 2 := by
    have h := congrArg (fun y ↦ RCLike.re ⟪y, v⟫_𝕜) hv.apply_eq_smul
    simpa [adjoint_inner_left, inner_smul_left, ← norm_sq_eq_re_inner] using h
  have hv0 : 0 < ‖v‖ ^ 2 := by
    have := hv.2
    positivity
  have hμ1 : |μ - 1| ≤ δ := by
    have := hM v
    rw [hnorm, ← sub_one_mul, abs_mul, abs_of_pos hv0] at this
    exact le_of_mul_le_mul_right this hv0
  exact Real.abs_sqrt_sub_one_le_abs_sub_one.trans hμ1

/-- **Near-isometry polar-factor bound.** If `|‖M x‖² - ‖x‖²| ≤ δ ‖x‖²` for every `x` and
`U` is a linear isometry with `U |M| = M`, then `‖M x - U x‖ ≤ δ ‖x‖` for every `x`. -/
theorem norm_apply_sub_le_of_comp_operatorAbs_eq (M : E →ₗ[𝕜] F) {δ : ℝ}
    (hM : ∀ x, |‖M x‖ ^ 2 - ‖x‖ ^ 2| ≤ δ * ‖x‖ ^ 2) {U : E →ₗᵢ[𝕜] F}
    (hU : U.toLinearMap ∘ₗ M.operatorAbs = M) (x : E) :
    ‖M x - U x‖ ≤ δ * ‖x‖ := by
  rw [← hU, comp_apply, LinearIsometry.coe_toLinearMap, ← map_sub, LinearIsometry.norm_map]
  exact M.norm_operatorAbs_apply_sub_le hM x

/-- **Near-isometry factorization.** A near-isometry with defect `δ` between finite-dimensional
inner product spaces of the same dimension factors as `M = U |M|` through a linear isometric
equivalence `U` that is pointwise within `δ` of `M`. -/
theorem exists_linearIsometryEquiv_comp_operatorAbs_eq_and_norm_apply_sub_le (M : E →ₗ[𝕜] F)
    (h : finrank 𝕜 E = finrank 𝕜 F) {δ : ℝ}
    (hM : ∀ x, |‖M x‖ ^ 2 - ‖x‖ ^ 2| ≤ δ * ‖x‖ ^ 2) :
    ∃ U : E ≃ₗᵢ[𝕜] F, (U : E →ₗ[𝕜] F) ∘ₗ M.operatorAbs = M ∧
      ∀ x, ‖M x - U x‖ ≤ δ * ‖x‖ := by
  obtain ⟨U, hU⟩ := M.exists_linearIsometryEquiv_comp_operatorAbs_eq h
  exact ⟨U, hU, M.norm_apply_sub_le_of_comp_operatorAbs_eq hM (U := U.toLinearIsometry) hU⟩

end LinearMap
