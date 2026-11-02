/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Acute

/-!
# Directed tangent representatives for subspaces

For subspaces `Z` and `U` of a finite-dimensional real or complex inner product space,
`Submodule.sinThetaEmbedding Z U` is the orthogonal projection onto `Uᗮ` restricted to `Z`.
This sine embedding and its singular-value identity are defined in `PrincipalAngle.lean`.

In the right singular basis of this sine embedding, `Submodule.tanThetaMap Z U`
scales the `i`-th basis vector by `tan (arcsin (S.singularValues i))`, then includes the
result into the ambient space. The formula uses a right singular basis, which need
not be unique; the singular-value identity below does not depend on that choice.

When the directed gap from `Z` to `U` is less than `1`, the representative has precisely
the principal tangents from `Z` to `U` as its singular values, including the zero tail.
No equality between the dimensions of `Z` and `U` is required. This is the tangent
representative used in Davis--Kahan tangent-angle estimates.

## Main results

* `Submodule.tanThetaMap`: a directed tangent representative built from the sine embedding.
* `Submodule.tanThetaMap_apply_rightSingularBasis`: the diagonal action on the
  right singular basis of the sine embedding.
* `Submodule.singularValues_tanThetaMap`: the singular values of the tangent
  representative are the principal tangents on the pole-free locus.

## Reference

C. Davis, W. Kahan, *The rotation of eigenvectors by a perturbation. III*,
SIAM J. Numer. Anal. **7** (1970), 1--46.
-/

public section

noncomputable section

namespace Submodule

open Module

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  (Z U : Submodule 𝕜 E) [Z.HasOrthogonalProjection] [U.HasOrthogonalProjection]

/-- A directed tangent representative in a right singular basis of the sine embedding.
On the `i`-th right singular vector of `S = Z.sinThetaEmbedding U`, it multiplies by
`tan (arcsin (S.singularValues i))` and then includes the vector in `E`.
The formula uses a right singular basis; its singular values are intrinsic. -/
def tanThetaMap : Z →ₗ[𝕜] E :=
  let S : Z →ₗ[𝕜] E := Z.sinThetaEmbedding U
  let e := S.rightSingularBasis
  Z.subtypeₗᵢ.toLinearMap ∘ₗ
    Matrix.toLin e.toBasis e.toBasis
      (Matrix.diagonal fun i ↦
        (Real.tan (Real.arcsin (S.singularValues i)) : 𝕜))

omit [Z.HasOrthogonalProjection] in
/-- The tangent representative is inclusion after a diagonal operator in the right
singular basis of the directed sine embedding. -/
theorem tanThetaMap_def :
    Z.tanThetaMap U =
      Z.subtypeₗᵢ.toLinearMap ∘ₗ
        Matrix.toLin
          ((Z.sinThetaEmbedding U : Z →ₗ[𝕜] E).rightSingularBasis).toBasis
          ((Z.sinThetaEmbedding U : Z →ₗ[𝕜] E).rightSingularBasis).toBasis
          (Matrix.diagonal fun i ↦
            (Real.tan (Real.arcsin
              ((Z.sinThetaEmbedding U : Z →ₗ[𝕜] E).singularValues i)) : 𝕜)) := (rfl)

omit [Z.HasOrthogonalProjection] in
/-- The tangent representative scales each right singular vector of the directed sine
embedding by the tangent of its corresponding principal angle. -/
theorem tanThetaMap_apply_rightSingularBasis (i : Fin (finrank 𝕜 Z)) :
    Z.tanThetaMap U
        ((Z.sinThetaEmbedding U : Z →ₗ[𝕜] E).rightSingularBasis i) =
      (Real.tan (Real.arcsin
        ((Z.sinThetaEmbedding U : Z →ₗ[𝕜] E).singularValues i)) : 𝕜) •
        (((Z.sinThetaEmbedding U : Z →ₗ[𝕜] E).rightSingularBasis i) : E) := by
  simp only [tanThetaMap, LinearMap.comp_apply,
    Matrix.toLin_diagonal_apply_self, subtypeₗᵢ_toLinearMap, map_smul]
  simp only [Submodule.subtype_apply]

/-- When the directed projection gap is less than one, the directed tangent
representative has the directed principal tangents as its singular values,
including the zero tail. No rank equality is required. -/
theorem singularValues_tanThetaMap (hgap : Z.directedProjectionGap U < 1) :
    (Z.tanThetaMap U).singularValues = Z.principalTangents U := by
  let S : Z →ₗ[𝕜] E := Z.sinThetaEmbedding U
  let e := S.rightSingularBasis
  let d : Fin (finrank 𝕜 Z) → 𝕜 :=
    fun i ↦ (Real.tan (Real.arcsin (S.singularValues i)) : 𝕜)
  let D : Z →ₗ[𝕜] Z :=
    Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)
  have hS : S.singularValues = Z.principalSines U :=
    Z.singularValues_sinThetaEmbedding U
  have hval (i : Fin (finrank 𝕜 Z)) :
      Real.tan (Real.arcsin (S.singularValues i)) = Z.principalTangents U i := by
    rw [hS, principalTangents_apply, principalAngles_apply]
  have hnorm (i : Fin (finrank 𝕜 Z)) :
      ‖d i‖ = Z.principalTangents U i := by
    simp only [d, hval]
    exact RCLike.norm_of_nonneg (Z.principalTangents_nonneg U i)
  have hAngles : ∀ i, Z.principalAngles U i < Real.pi / 2 :=
    (Z.forall_principalAngles_lt_pi_div_two_iff_directedProjectionGap_lt_one U).2 hgap
  have hanti : Antitone fun i ↦ ‖d i‖ := by
    intro i j hij
    simp only [hnorm]
    exact Z.principalTangents_antitone U hAngles hij
  have hD : D.singularValues = Z.principalTangents U := by
    ext i
    rcases lt_or_ge i (finrank 𝕜 Z) with hi | hi
    · calc
        D.singularValues i = ‖d ⟨i, hi⟩‖ :=
          Matrix.singularValues_toLin_diagonal e d (Equiv.refl _) hanti ⟨i, hi⟩
        _ = Z.principalTangents U i := hnorm _
    · rw [D.singularValues_of_finrank_le hi, principalTangents_of_finrank_le Z U hi]
  -- Expose the isometric inclusion composed with the diagonal operator `D`.
  unfold tanThetaMap
  exact (LinearMap.singularValues_linearIsometry_comp Z.subtypeₗᵢ D).trans hD

end Submodule
