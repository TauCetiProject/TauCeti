/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Normed.Module.HahnBanach
public import TauCeti.Analysis.Normed.Module.TensorProduct.Completion

/-!
# Isometric embeddings of injective tensor products

The injective tensor norm is independent of the ambient spaces: linear isometric embeddings
in both factors induce a linear isometric embedding of their injective tensor products.
The same holds for the completed injective tensor products, without completeness assumptions
on the factors. These embeddings allow injective tensors of subspaces to be viewed inside the
tensor product of the ambient spaces.

The underlying bounded map is the existing `InjectiveTensor.mapL`; its norm preservation follows
from Hahn–Banach extension of functionals on the left factor. On completions we use Mathlib's
`LinearIsometry.completion`.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §3.1.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable {𝕜 E E' F F' : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Linear isometries in both factors preserve the injective tensor seminorm. -/
theorem injectiveSeminorm_map_linearIsometry (f : E →ₗᵢ[𝕜] E') (g : F →ₗᵢ[𝕜] F')
    (u : E ⊗[𝕜] F) :
    injectiveSeminorm 𝕜 E' F' (map f.toLinearMap g.toLinearMap u) =
      injectiveSeminorm 𝕜 E F u := by
  apply le_antisymm
  · calc
      injectiveSeminorm 𝕜 E' F' (map f.toLinearMap g.toLinearMap u) ≤
          ‖f.toContinuousLinearMap‖ * ‖g.toContinuousLinearMap‖ *
            injectiveSeminorm 𝕜 E F u :=
        injectiveSeminorm_map_le f.toContinuousLinearMap g.toContinuousLinearMap u
      _ ≤ 1 * 1 * injectiveSeminorm 𝕜 E F u := by
        gcongr
        · exact f.norm_toContinuousLinearMap_le
        · exact g.norm_toContinuousLinearMap_le
      _ = injectiveSeminorm 𝕜 E F u := by simp
  · rw [injectiveSeminorm_apply]
    refine ContinuousLinearMap.opNorm_le_bound _ (apply_nonneg _ _) fun φ ↦ ?_
    obtain ⟨ψ, hψ, hnorm⟩ := f.exists_extension_norm_eq φ
    have heval : contractStrongDual 𝕜 E' F' (map f.toLinearMap g.toLinearMap u) ψ =
        g (contractStrongDual 𝕜 E F u φ) := by
      simpa [ContinuousLinearMap.precomp_apply, hψ] using
        congrArg (fun T ↦ T ψ)
          (contractStrongDual_map f.toContinuousLinearMap g.toContinuousLinearMap u)
    calc
      ‖contractStrongDual 𝕜 E F u φ‖ =
          ‖contractStrongDual 𝕜 E' F' (map f.toLinearMap g.toLinearMap u) ψ‖ := by
        rw [heval, g.norm_map]
      _ ≤ injectiveSeminorm 𝕜 E' F' (map f.toLinearMap g.toLinearMap u) * ‖ψ‖ :=
        norm_contractStrongDual_apply_le _ ψ
      _ = injectiveSeminorm 𝕜 E' F' (map f.toLinearMap g.toLinearMap u) * ‖φ‖ := by
        rw [hnorm]

end TensorProduct

namespace TauCeti

section Algebraic

variable {𝕜 E E' F F' : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']

namespace InjectiveTensor

/-- The isometric embedding of injective tensor products induced by linear isometric embeddings
of both factors. -/
noncomputable def mapIsometry (f : E →ₗᵢ[𝕜] E') (g : F →ₗᵢ[𝕜] F') :
    InjectiveTensor 𝕜 E F →ₗᵢ[𝕜] InjectiveTensor 𝕜 E' F' where
  __ := (mapL f.toContinuousLinearMap g.toContinuousLinearMap).toLinearMap
  norm_map' u := by
    simpa [norm_def] using
      TensorProduct.injectiveSeminorm_map_linearIsometry f g u.toTensorProduct

/-- Forgetting the isometry recovers the bounded tensor map. -/
@[simp]
theorem mapIsometry_toContinuousLinearMap (f : E →ₗᵢ[𝕜] E') (g : F →ₗᵢ[𝕜] F') :
    (mapIsometry f g).toContinuousLinearMap =
      mapL f.toContinuousLinearMap g.toContinuousLinearMap :=
  (rfl)

/-- The isometric tensor embedding sends pure tensors to pure tensors. -/
@[simp]
theorem mapIsometry_tmul (f : E →ₗᵢ[𝕜] E') (g : F →ₗᵢ[𝕜] F') (x : E) (y : F) :
    mapIsometry f g ⟨x ⊗ₜ y⟩ = ⟨f x ⊗ₜ g y⟩ :=
  mapL_tmul f.toContinuousLinearMap g.toContinuousLinearMap x y

end InjectiveTensor

end Algebraic

namespace CompletedInjectiveTensor

variable {𝕜 E E' F F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Isometric embeddings in both factors induce an isometric embedding of completed injective
tensor products. The factors need not be complete. -/
noncomputable def mapIsometry (f : E →ₗᵢ[𝕜] E') (g : F →ₗᵢ[𝕜] F') :
    CompletedInjectiveTensor 𝕜 E F →ₗᵢ[𝕜] CompletedInjectiveTensor 𝕜 E' F' :=
  (InjectiveTensor.mapIsometry f g).completion

/-- Forgetting the completed isometry recovers the bounded completed tensor map. -/
@[simp]
theorem mapIsometry_toContinuousLinearMap (f : E →ₗᵢ[𝕜] E') (g : F →ₗᵢ[𝕜] F') :
    (mapIsometry f g).toContinuousLinearMap =
      mapL f.toContinuousLinearMap g.toContinuousLinearMap := by
  apply continuousLinearMap_ext
  intro x y
  simp [mapIsometry]

/-- On the dense algebraic tensor product the completed embedding is the algebraic embedding. -/
@[simp]
theorem mapIsometry_coe (f : E →ₗᵢ[𝕜] E') (g : F →ₗᵢ[𝕜] F') (u : InjectiveTensor 𝕜 E F) :
    mapIsometry f g u = InjectiveTensor.mapIsometry f g u :=
  LinearIsometry.completion_apply_coe _ u

end CompletedInjectiveTensor

end TauCeti
