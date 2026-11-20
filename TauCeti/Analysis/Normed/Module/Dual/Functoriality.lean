/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Functoriality of the continuous dual

Precomposition by a continuous linear map `T : E →L[𝕜] F` gives its adjoint
`ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E`. The identity and
composition laws, and the bound `‖T*‖ ≤ ‖T‖`, hold for precomposition into any target and are
recorded in `TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Precomp` and
`TauCeti.Analysis.Normed.Operator.Basic`. For normed spaces, this file proves that taking the
adjoint preserves the operator norm over `ℝ` or `ℂ`, packages this operation as a linear isometry
between operator spaces, and proves the naturality of the canonical map into the bidual.

For normed spaces over `ℝ` or `ℂ`, the adjoint of `T : E →L[𝕜] F`, with its arguments exchanged,
is the composition of `T` with Mathlib's canonical bidual isometry
`NormedSpace.inclusionInDoubleDualLi`.

These are the standard functorial properties of the continuous dual; see Rudin,
*Functional Analysis*, Chapter 4.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

section Norm

variable [IsRCLikeNormedField 𝕜]

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
    ‖(ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)‖₊ = ‖T‖₊ :=
  NNReal.eq (norm_precomp T)

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

/-- The bidual adjoint `T**` is continuous between the weak-star topologies of the biduals. -/
theorem continuous_toWeakDual_precomp_precomp (T : E →L[𝕜] F) :
    Continuous fun Φ : WeakDual 𝕜 (StrongDual 𝕜 E) ↦ StrongDual.toWeakDual
      (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) (WeakDual.toStrongDual Φ)) :=
  WeakDual.continuous_of_continuous_eval fun f ↦ WeakDual.eval_continuous (f.comp T)

/-- On the canonical image of `E` in the weak-star bidual, the bidual adjoint `T**` acts as `T`. -/
theorem toWeakDual_precomp_precomp_inclusionInDoubleDualWeak (T : E →L[𝕜] F) (x : E) :
    StrongDual.toWeakDual (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)
        (WeakDual.toStrongDual (NormedSpace.inclusionInDoubleDualWeak 𝕜 E (toWeakSpace 𝕜 E x)))) =
      NormedSpace.inclusionInDoubleDualWeak 𝕜 F (toWeakSpace 𝕜 F (T x)) := by
  simp [NormedSpace.inclusionInDoubleDualWeak_apply]

end Bidual

end ContinuousLinearMap
