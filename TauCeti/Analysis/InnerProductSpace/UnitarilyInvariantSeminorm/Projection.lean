/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.BlockSum
public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator
public import TauCeti.Analysis.InnerProductSpace.Projection.Block
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
assumptions. It is proved with two subspace reflections in `FanDominance.lean`, which also derives
from it that composing with an orthogonal projection does not increase the seminorm.

The sine-angle operator `|P_U - P_V|` and the projector difference have the
same singular values and hence the same unitarily invariant seminorm.

## Main results

* `TauCeti.UnitarilyInvariantSeminorm.map_sinAngleOperator_eq_map_sub_starProjection`:
  their unitarily invariant seminorms agree.
* `TauCeti.UnitarilyInvariantSeminorm.mul_map_sub_starProjection_le_map_comp_sub_comp`:
  block-sum majorization turns two directed Ky Fan bounds into a checkerboard estimate.

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

/-- Block-sum majorization turns the two directed Ky Fan bounds into the checkerboard estimate:
`delta * N (P_U - P_V) ≤ N ((B - A) P_U - P_V (B - A))`. -/
theorem mul_map_sub_starProjection_le_map_comp_sub_comp [FiniteDimensional K E]
    (N : UnitarilyInvariantSeminorm K E E)
    {A B : E →L[K] E}
    (hAB : ((A - B : E →L[K] E) : E →ₗ[K] E).IsSymmetric)
    {U V : Submodule K E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {delta : ℝ} (hdelta : 0 ≤ delta)
    (hkyUV : ∀ k : Nat,
      (((delta : ℝ) : K) • (Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype)).kyFanSum k ≤
        (Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ
          (((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ U.subtype)).kyFanSum k)
    (hkyVU : ∀ k : Nat,
      (((delta : ℝ) : K) •
          (-(LinearMap.adjoint (Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ V.subtype)))).kyFanSum
          k ≤
        (LinearMap.adjoint (Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ
          (((A - B : E →L[K] E) : E →ₗ[K] E) ∘ₗ V.subtype))).kyFanSum k) :
    delta * N (((U.starProjection - V.starProjection : E →L[K] E) : E →ₗ[K] E)) ≤
      N ((((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ
          (U.starProjection : E →ₗ[K] E)) -
        ((V.starProjection : E →ₗ[K] E) ∘ₗ
          ((B - A : E →L[K] E) : E →ₗ[K] E))) := by
  -- Orthogonal decompositions put both directed bounds on the diagonal of
  -- a block operator; block-sum majorization preserves constant one.
  let EU : E ≃ₗᵢ[K] WithLp 2 (U × Uᗮ) := U.orthogonalDecomposition
  let EV : E ≃ₗᵢ[K] WithLp 2 (Vᗮ × V) :=
    V.orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdComm 2 K V Vᗮ)
  let NB : UnitarilyInvariantSeminorm K
      (WithLp 2 (U × Uᗮ)) (WithLp 2 (Vᗮ × V)) :=
    (UnitarilyInvariantSeminorm.arrowCongr EU EV) N
  let Xblock : WithLp 2 (U × Uᗮ) →ₗ[K] WithLp 2 (Vᗮ × V) :=
    ((Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype).prodMap
      (-(LinearMap.adjoint (Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ V.subtype)))).withLpMap 2
  let Cblock : WithLp 2 (U × Uᗮ) →ₗ[K] WithLp 2 (Vᗮ × V) :=
    ((Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ
        (((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ U.subtype)).prodMap
      (LinearMap.adjoint (Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ
        (((A - B : E →L[K] E) : E →ₗ[K] E) ∘ₗ V.subtype)))).withLpMap 2
  have hsmul :
      (((delta : ℝ) : K) • Xblock) =
        ((((delta : ℝ) : K) • (Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype)).prodMap
          (((delta : ℝ) : K) •
            (-(LinearMap.adjoint (Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ
              V.subtype))))).withLpMap 2 := by
    ext x
    apply WithLp.ofLp_injective 2
    simp [Xblock, WithLp.map, LinearMap.prodMap_apply]
  have hblock : delta * NB Xblock ≤ NB Cblock := by
    have h := NB.map_prodMap_withLpMap_le hkyUV hkyVU
    rw [← hsmul, map_smul_eq_mul, RCLike.norm_ofReal,
      abs_of_nonneg hdelta] at h
    exact h
  -- Lift the block estimate back to the ambient space through the isometries.
  have hNB_apply (T : WithLp 2 (U × Uᗮ) →ₗ[K] WithLp 2 (Vᗮ × V)) :
      NB T = N ((EV.symm : WithLp 2 (Vᗮ × V) →ₗ[K] E) ∘ₗ T ∘ₗ
        (EU : E →ₗ[K] WithLp 2 (U × Uᗮ))) := by
    simp only [NB, UnitarilyInvariantSeminorm.arrowCongr_apply]
  rw [hNB_apply, hNB_apply, Submodule.lift_crossBlocks_eq_starProjection_sub,
    Submodule.lift_residualBlocks_eq_comp_sub _ hAB] at hblock
  simpa only [ContinuousLinearMap.toLinearMap_sub] using hblock

end TauCeti.UnitarilyInvariantSeminorm
