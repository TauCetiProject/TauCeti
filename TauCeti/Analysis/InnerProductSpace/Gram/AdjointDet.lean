/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant of `f^* ∘ f` and Gram determinants

For a linear map `f : U →ₗ[𝕜] V` between finite-dimensional inner product spaces over `𝕜`
(`RCLike 𝕜`), the determinant of the self-adjoint endomorphism `f^* ∘ f` equals the Gram
determinant `(Matrix.gram 𝕜 (f ∘ b)).det` of any orthonormal basis `b` of `U`, and hence
equals `(f.normDet ^ 2 : 𝕜)`. In particular, `det (f^* ∘ f) ≠ 0` if and only if `f` is
injective.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026
Anthropic, PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`, specifically
`New.TwistedLattice.volume_ne_zero` and the `det (Θ^* ∘ Θ)` identification in
`grh/src/New/Reduction/Lattices/TwistedLattice.lean` (§1.3 (h)), generalized from `ℂ` to
any `[RCLike 𝕜]`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 U V ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- For a linear map `f : U →ₗ[𝕜] V` between finite-dimensional inner product spaces and any
orthonormal basis `b` of `U`, `det (f^* ∘ f)` equals the Gram determinant of `f ∘ b`. -/
theorem det_adjoint_comp_eq_det_gram_orthonormalBasis (f : U →ₗ[𝕜] V)
    (b : OrthonormalBasis ι 𝕜 U) :
    LinearMap.det (LinearMap.adjoint f ∘ₗ f) = (Matrix.gram 𝕜 (f ∘ b)).det := by
  rw [← LinearMap.det_toMatrix b.toBasis]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply,
    LinearMap.adjoint_inner_right, Matrix.gram_apply]

/-- For a linear map `f : U →ₗ[𝕜] V` between finite-dimensional inner product spaces,
`det (f^* ∘ f)` equals the squared norm determinant `(f.normDet ^ 2 : 𝕜)`. -/
theorem det_adjoint_comp_eq_normDet_sq (f : U →ₗ[𝕜] V) :
    LinearMap.det (LinearMap.adjoint f ∘ₗ f) = (↑(f.normDet ^ 2) : 𝕜) := by
  let b := stdOrthonormalBasis 𝕜 U
  rw [det_adjoint_comp_eq_det_gram_orthonormalBasis f b, f.normDet_sq_eq_det_gram b]
  rfl

/-- For a linear map `f : U →ₗ[𝕜] V` between finite-dimensional inner product spaces,
`det (f^* ∘ f) ≠ 0` if and only if `f` is injective. -/
theorem det_adjoint_comp_ne_zero_iff_injective (f : U →ₗ[𝕜] V) :
    LinearMap.det (LinearMap.adjoint f ∘ₗ f) ≠ 0 ↔ Function.Injective f := by
  let b := stdOrthonormalBasis 𝕜 U
  rw [det_adjoint_comp_eq_det_gram_orthonormalBasis f b,
    Matrix.det_gram_ne_zero_iff_linearIndependent]
  constructor
  · intro hli
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h0 : ∑ i, b.repr x i • f (b i) = 0 := by
      calc ∑ i, b.repr x i • f (b i) = f (∑ i, b.repr x i • b i) := by simp [map_sum, map_smul]
        _ = f x := by rw [b.sum_repr]
        _ = 0 := hx
    have hcoeff := Fintype.linearIndependent_iff.mp hli (fun i ↦ b.repr x i) h0
    rw [← b.sum_repr x]
    simp [hcoeff]
  · intro hinj
    exact b.toBasis.linearIndependent.map_injOn f hinj.injOn

end TauCeti
