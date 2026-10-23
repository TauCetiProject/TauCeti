/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Functoriality of the continuous dual

Precomposition by a continuous linear map acts contravariantly on continuous duals. This file
records the identity and composition laws for modules with arbitrary topologies. For normed
spaces, it proves that taking the adjoint preserves the operator norm over `ℝ` or `ℂ`, packages
this operation as a linear isometry between operator spaces, and proves the naturality of the
canonical map into the bidual.

For normed spaces over `ℝ` or `ℂ`, the adjoint of `T : E →L[𝕜] F`, with its arguments exchanged,
is the composition of `T` with Mathlib's canonical bidual isometry
`NormedSpace.inclusionInDoubleDualLi`.

These are the standard functorial properties of the continuous dual; see Rudin,
*Functional Analysis*, Chapter 4.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*}

section Algebraic

variable [NormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
  [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

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
  refine opNorm_le_bound _ (norm_nonneg T) fun f ↦ ?_
  simpa only [precomp_apply, mul_comm] using opNorm_comp_le f T

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
  have h : (ContinuousLinearMap.precomp 𝕜 T).flip =
      (NormedSpace.inclusionInDoubleDualLi (E := F) 𝕜).toContinuousLinearMap.comp T := by
    ext x f
    simp only [flip_apply, precomp_apply, comp_apply]
    -- The bidual isometry has inclusionInDoubleDual as its underlying continuous linear map.
    exact (NormedSpace.dual_def 𝕜 F (T x) f).symm
  rw [← opNorm_flip, h]
  exact LinearIsometry.norm_toContinuousLinearMap_comp _

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
