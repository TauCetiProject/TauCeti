/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Unitarily invariant seminorms and orthogonal projections

For arbitrary linear maps `H : E → F`, orthogonal projections `P_U` on `E`
and `P_V` on `F`, the checkerboard operator `H P_U - P_V H` has seminorm at most
that of `H`.
The bound holds for every unitarily invariant seminorm, without spectral-gap
assumptions. Two subspace reflections yield the sharp constant one.

The sine-angle operator `|P_U - P_V|` and the projector difference have the
same singular values and hence the same unitarily invariant seminorm.

## Main results

* `TauCeti.UnitarilyInvariantSeminorm.map_sinAngleOperator_eq_map_sub_starProjection`:
  their unitarily invariant seminorms agree.
* `TauCeti.UnitarilyInvariantSeminorm.map_comp_starProjection_sub_starProjection_comp_le`:
  `N (H P_U - P_V H) ≤ N H`.

## Provenance

Factored from the symmetric two-orientation proof adapted from
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean`
in the AIQ-Kitware DKPS formalization (Apache-2.0; Jon Crall, GPT-6).
-/

public section

open Module
open scoped InnerProductSpace

namespace TauCeti.UnitarilyInvariantSeminorm

variable {K E F : Type*} [RCLike K] [NormedAddCommGroup E]
  [InnerProductSpace K E] [NormedAddCommGroup F] [InnerProductSpace K F]

/-- The sine-angle operator and the projector difference have the same value
in every unitarily invariant seminorm, without spectral-gap assumptions. -/
@[simp]
theorem map_sinAngleOperator_eq_map_sub_starProjection
    [FiniteDimensional K E] [CompleteSpace E]
    (N : UnitarilyInvariantSeminorm K E E)
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    N ((U.sinAngleOperator V : E →L[K] E) : E →ₗ[K] E) =
      N (((U.starProjection - V.starProjection : E →L[K] E) : E →ₗ[K] E)) :=
  N.map_eq_of_singularValues_eq
    (Submodule.singularValues_sinAngleOperator_eq_sub_starProjection U V)

/-- **Checkerboard contraction.** For any `H`, the off-diagonal difference
`H P_U - P_V H` has no larger unitarily invariant seminorm than `H`.
No symmetry, invariance or spectral-gap hypotheses on `H` are needed. -/
theorem map_comp_starProjection_sub_starProjection_comp_le
    (N : UnitarilyInvariantSeminorm K E F)
    (U : Submodule K E) (V : Submodule K F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (H : E →ₗ[K] F) :
    N (H ∘ₗ (U.starProjection : E →ₗ[K] E) -
      (V.starProjection : F →ₗ[K] F) ∘ₗ H) ≤ N H := by
  let JU : E ≃ₗᵢ[K] E := U.reflection
  let JV : F ≃ₗᵢ[K] F := V.reflection
  -- Two reflections turn the checkerboard into a difference of isometric multiples.
  have hdouble :
      (2 : K) • (H ∘ₗ (U.starProjection : E →ₗ[K] E) -
          (V.starProjection : F →ₗ[K] F) ∘ₗ H) =
        H ∘ₗ (JU : E →ₗ[K] E) - (JV : F →ₗ[K] F) ∘ₗ H := by
    ext x
    simp [JU, JV, Submodule.reflection_apply, LinearMap.comp_apply]
    module
  have hscaled :
      2 * N (H ∘ₗ (U.starProjection : E →ₗ[K] E) -
          (V.starProjection : F →ₗ[K] F) ∘ₗ H) ≤ 2 * N H := by
    calc
      _ = N ((2 : K) • (H ∘ₗ (U.starProjection : E →ₗ[K] E) -
          (V.starProjection : F →ₗ[K] F) ∘ₗ H)) := by
        simp only [map_smul_eq_mul, RCLike.norm_ofNat]
      _ = N (H ∘ₗ (JU : E →ₗ[K] E) - (JV : F →ₗ[K] F) ∘ₗ H) := by
        rw [hdouble]
      _ ≤ N (H ∘ₗ (JU : E →ₗ[K] E)) + N (-((JV : F →ₗ[K] F) ∘ₗ H)) := by
        simpa [sub_eq_add_neg] using
          map_add_le_add N (H ∘ₗ (JU : E →ₗ[K] E))
            (-((JV : F →ₗ[K] F) ∘ₗ H))
      _ = N H + N H := by
        rw [map_neg_eq_map N, N.map_comp_linearIsometryEquiv JU H,
          N.map_linearIsometryEquiv_comp JV H]
      _ = 2 * N H := by ring
  exact le_of_mul_le_mul_left hscaled (by norm_num : (0 : ℝ) < 2)

end TauCeti.UnitarilyInvariantSeminorm
