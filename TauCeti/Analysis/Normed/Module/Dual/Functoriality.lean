/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Functoriality of the continuous dual

Precomposition by a bounded linear map is its Banach-space adjoint. This file records the
contravariant identity and composition laws, proves that taking the adjoint preserves the
operator norm over `ℝ` or `ℂ`, and packages this operation as a linear isometry between operator
spaces. It also proves the naturality of the canonical map into the bidual.

These are the standard functorial properties of the continuous dual; see Rudin,
*Functional Analysis*, Chapter 4.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*}

section Algebraic

variable [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The adjoint of the identity map is the identity map on the continuous dual. -/
@[simp]
theorem precomp_id :
    ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.id 𝕜 E) =
      ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E) := by
  ext f x
  rfl

/-- Taking adjoints reverses composition. -/
@[simp]
theorem precomp_comp (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    ContinuousLinearMap.precomp 𝕜 (S.comp T) =
      (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).comp
        (ContinuousLinearMap.precomp 𝕜 S : StrongDual 𝕜 G →L[𝕜] StrongDual 𝕜 F) := by
  ext f x
  rfl

end Algebraic

section NormBound

variable [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The operator norm of the adjoint is at most the operator norm of the original map. -/
theorem norm_precomp_le (T : E →L[𝕜] F) :
    ‖(ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)‖ ≤ ‖T‖ := by
  let A : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E := ContinuousLinearMap.precomp 𝕜 T
  have hA : ‖A‖ ≤ ‖T‖ := A.opNorm_le_bound (norm_nonneg T) fun f ↦ by
    simpa only [A, ContinuousLinearMap.precomp_apply, mul_comm] using
      ContinuousLinearMap.opNorm_comp_le f T
  simpa only [A] using hA

end NormBound

section Norm

variable [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Taking the adjoint preserves the operator norm. -/
@[simp]
theorem norm_precomp (T : E →L[𝕜] F) :
    ‖(ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)‖ = ‖T‖ := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E := ContinuousLinearMap.precomp 𝕜 T
  have hle : ‖T‖ ≤ ‖A‖ := T.opNorm_le_bound A.opNorm_nonneg fun x ↦ by
    refine NormedSpace.norm_le_dual_bound 𝕜 (T x)
      (mul_nonneg A.opNorm_nonneg (norm_nonneg x)) fun f ↦ ?_
    calc
      ‖f (T x)‖ = ‖(A f) x‖ := rfl
      _ ≤ ‖A f‖ * ‖x‖ := (A f).le_opNorm x
      _ ≤ (‖A‖ * ‖f‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (A.le_opNorm f) (norm_nonneg x)
      _ = (‖A‖ * ‖x‖) * ‖f‖ := by ring
  exact le_antisymm (norm_precomp_le T) (by simpa only [A] using hle)

/-- Taking the adjoint preserves the nonnegative operator norm. -/
@[simp]
theorem nnnorm_precomp (T : E →L[𝕜] F) :
    ‖(ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)‖₊ = ‖T‖₊ := by
  ext
  exact norm_precomp T

/-- Taking adjoints, bundled as a linear isometry between spaces of bounded operators. -/
def precompLinearIsometry :
    (E →L[𝕜] F) →ₗᵢ[𝕜] (StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) where
  toFun T := ContinuousLinearMap.precomp 𝕜 T
  map_add' T S := by
    ext f x
    simp
  map_smul' c T := by
    ext f x
    simp
  norm_map' T := norm_precomp T

/-- The operator-space isometry for adjoints evaluates to precomposition. -/
@[simp]
theorem precompLinearIsometry_apply (T : E →L[𝕜] F) :
    precompLinearIsometry (𝕜 := 𝕜) (E := E) (F := F) T =
      ContinuousLinearMap.precomp 𝕜 T := (rfl)

end Norm

section Bidual

variable [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Pointwise naturality of the canonical map into the bidual. -/
@[simp]
theorem precomp_precomp_inclusionInDoubleDual (T : E →L[𝕜] F) (x : E) :
    (NormedSpace.inclusionInDoubleDual 𝕜 E x).comp (ContinuousLinearMap.precomp 𝕜 T) =
      NormedSpace.inclusionInDoubleDual 𝕜 F (T x) := by
  ext f
  rfl

/-- The canonical map into the bidual is natural under bounded linear maps. -/
theorem precomp_precomp_comp_inclusionInDoubleDual (T : E →L[𝕜] F) :
    (ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 T)).comp
        (NormedSpace.inclusionInDoubleDual 𝕜 E) =
      (NormedSpace.inclusionInDoubleDual 𝕜 F).comp T := by
  ext x f
  rfl

end Bidual

end ContinuousLinearMap
