/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT 5.6 High, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.RangeProjection
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Sylvester.Basic

/-!
# The Rayleigh–Ritz procedure: compressions and Ritz residuals

Let `A` be an operator on a Hilbert space `E`. A *trial map* is an operator `X : F → E` from a
second Hilbert space; when `X` is an isometry it identifies `F` with the trial subspace
`Z = range X`. The *compression* of `A` along `X` is the operator `X† A X` on `F`; for an isometry
it is `A` cut down to `Z`, read in the coordinates of `F`. For a model operator `M` on `F`, the
*residual* of the trial map is `A X - X M`, the Sylvester operator `A.sylvester M X`; it measures
how far `Z` is from being invariant under `A`, with `M` as the proposed action of `A` on `Z`. The
*Ritz residual* is the residual for the compression, `M = X† A X`.

For an isometric trial map this file shows that the Ritz residual is `P_{Zᗮ} A X`, that it is the
projection onto `Zᗮ` of every residual, and that the residuals split orthogonally as
`A X - X M = (A X - X X† A X) + X (X† A X - M)`. Consequently the compression is the best model:
the Ritz residual is smallest among all residuals in every unitarily invariant seminorm, and in
the Frobenius seminorm the squared residual exceeds the squared Ritz residual by exactly
`‖X† A X - M‖_F²`.

The residual form of the Davis–Kahan `sin Θ` theorem,
`TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_le_map_sylvester_apply`, has the
Ritz residual as its residual when `M` is the compression; the angles between the trial subspace
and a second subspace are read off the trial map by
`Submodule.principalSines_range_eq_singularValues` and its companions.

## Main results

* `ContinuousLinearMap.sylvester_compression`: the Ritz residual `A X - X X† A X` of an isometric
  trial map is `P_{Zᗮ} A X`.
* `ContinuousLinearMap.adjoint_comp_sylvester_compression`: the Ritz residual is orthogonal to the
  trial subspace, `X† (A X - X X† A X) = 0`.
* `ContinuousLinearMap.starProjection_orthogonal_range_comp_sylvester`: the Ritz residual is the
  projection onto `Zᗮ` of every residual `A X - X M`.
* `TauCeti.UnitarilyInvariantSeminorm.map_sylvester_compression_le_map_sylvester`: the Ritz
  residual minimizes every unitarily invariant seminorm of the residual.
* `sq_frobenius_sylvester_eq_sq_frobenius_sylvester_compression_add`, in the namespace
  `TauCeti.UnitarilyInvariantSeminorm`: the Pythagoras identity
  `‖A X - X M‖_F² = ‖A X - X X† A X‖_F² + ‖X† A X - M‖_F²`.

## References

* B. N. Parlett, *The Symmetric Eigenvalue Problem*, Classics in Applied Mathematics 20, SIAM
  (1998), Chapter 11.
* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
-/

public section

noncomputable section

open Module
open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace ContinuousLinearMap

/-! ### Ritz residuals -/

section Residual

variable (A : E →L[𝕜] E) {X : F →L[𝕜] E}

/-- Every residual is the Ritz residual plus the trial map applied to the model error:
`A X - X M = (A X - X X† A X) + X (X† A X - M)`. -/
theorem sylvester_eq_sylvester_compression_add (X : F →L[𝕜] E) (M : F →L[𝕜] F) :
    A.sylvester M X = A.sylvester (A.compression X) X + X ∘L (A.compression X - M) := by
  simp only [sylvester_apply, comp_sub]
  abel

/-- **Galerkin orthogonality.** The Ritz residual of an isometric trial map is orthogonal to the
trial subspace: `X† (A X - X X† A X) = 0`. -/
theorem adjoint_comp_sylvester_compression (hX : Isometry X) :
    adjoint X ∘L A.sylvester (A.compression X) X = 0 := by
  have h := (isometry_iff_adjoint_comp_self X).1 hX
  ext x
  have hx := congr($h (adjoint X (A (X x))))
  simp only [comp_apply] at hx
  simp [compression_def, hx]

/-- The Ritz residual of an isometric trial map `X` is `P_{Zᗮ} A X`, where `Z = range X`. -/
theorem sylvester_compression (hX : Isometry X) [X.range.HasOrthogonalProjection] :
    A.sylvester (A.compression X) X = X.rangeᗮ.starProjection ∘L A ∘L X := by
  have h := comp_adjoint_eq_starProjection_range hX
  ext x
  have hx := congr($h (A (X x)))
  simp only [comp_apply] at hx
  simp [compression_def, hx]

/-- The Ritz residual of an isometric trial map `X` is the projection onto `(range X)ᗮ` of every
residual `A X - X M`. -/
theorem starProjection_orthogonal_range_comp_sylvester (hX : Isometry X)
    [X.range.HasOrthogonalProjection] (M : F →L[𝕜] F) :
    X.rangeᗮ.starProjection ∘L A.sylvester M X = A.sylvester (A.compression X) X := by
  rw [sylvester_compression A hX]
  ext x
  simp

end Residual

end ContinuousLinearMap

/-! ### Minimality of the Ritz residual -/

namespace TauCeti.UnitarilyInvariantSeminorm

open ContinuousLinearMap

variable {A : E →L[𝕜] E} {X : F →L[𝕜] E}

/-- **Pythagoras for residuals.** For an isometric trial map `X` and every model `M`, the
residuals split orthogonally in the Frobenius seminorm:
`‖A X - X M‖_F² = ‖A X - X X† A X‖_F² + ‖X† A X - M‖_F²`. -/
theorem sq_frobenius_sylvester_eq_sq_frobenius_sylvester_compression_add [FiniteDimensional 𝕜 F]
    (hX : Isometry X) (M : F →L[𝕜] F) :
    frobenius 𝕜 F E (A.sylvester M X) ^ 2 =
      frobenius 𝕜 F E (A.sylvester (A.compression X) X) ^ 2 +
        frobenius 𝕜 F F (A.compression X - M) ^ 2 := by
  let b := stdOrthonormalBasis 𝕜 F
  simp only [sq_frobenius_apply b, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- The `i`-th column splits as `R bᵢ + X (D bᵢ)` with `R bᵢ ⟂ range X` and `‖X (D bᵢ)‖ = ‖D bᵢ‖`.
  have horth : ⟪A.sylvester (A.compression X) X (b i), X ((A.compression X - M) (b i))⟫_𝕜 = 0 := by
    rw [← adjoint_inner_left, ← comp_apply, adjoint_comp_sylvester_compression A hX, zero_apply,
      inner_zero_left]
  simp only [coe_coe, LinearMap.sub_apply, ← sub_apply]
  rw [sylvester_eq_sylvester_compression_add A X M, add_apply, comp_apply, sq, sq, sq,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth,
    AddMonoidHomClass.isometry_iff_norm _ |>.1 hX]

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- **Minimality of the Ritz residual.** For an isometric trial map `X`, the compression
`X† A X` is the best model operator: the Ritz residual is smallest among all residuals
`A X - X M` in every unitarily invariant seminorm. -/
theorem map_sylvester_compression_le_map_sylvester (N : UnitarilyInvariantSeminorm 𝕜 F E)
    (hX : Isometry X) (M : F →L[𝕜] F) :
    N (A.sylvester (A.compression X) X) ≤ N (A.sylvester M X) := by
  rw [← starProjection_orthogonal_range_comp_sylvester A hX M]
  exact N.map_starProjection_comp_le _ _

end TauCeti.UnitarilyInvariantSeminorm

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The Ritz residual of a finite-dimensional isometric trial map is orthogonal to the trial
space: `X† (A X - X (X† A X)) = 0`.

This is the linear-map form of `ContinuousLinearMap.adjoint_comp_sylvester_compression`.
The corresponding DKPS statement is in
`ForTauCeti/Analysis/InnerProductSpace/Residual/Ritz.lean` (Jon Crall and GPT 5.6 High;
Kitware, Apache-2.0); the proof here uses the accepted continuous-map theorem. -/
theorem adjoint_comp_ritzResidual_eq_zero (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) : X.toLinearMap.adjoint ∘ₗ (A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ
      (X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap)) = 0 := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  have h := ContinuousLinearMap.adjoint_comp_sylvester_compression
    A.toContinuousLinearMap (X := X.toContinuousLinearMap) X.isometry
  simpa only [ContinuousLinearMap.compression_def, ContinuousLinearMap.sylvester_apply,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_sub,
    ← ContinuousLinearMap.adjoint_toLinearMap, LinearIsometry.toLinearMap_toContinuousLinearMap,
    LinearMap.coe_toContinuousLinearMap, ContinuousLinearMap.toLinearMap_zero] using congrArg
      ContinuousLinearMap.toLinearMap h

end LinearMap
