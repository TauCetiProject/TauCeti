/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Finite
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius.Basic

import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Isometry

/-!
# Frobenius seminorm of the polar factor

The squared Frobenius seminorm of the canonical polar factor equals the rank of the map.
Adding a block from the kernel to the orthogonal complement of the range increases this
squared seminorm by the squared Frobenius seminorm of the block.
-/

public section

open LinearMap Module

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The squared Frobenius seminorm of the polar factor is the rank of the original map. -/
theorem _root_.LinearMap.sq_frobenius_polarFactor (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F A.polarFactor ^ 2 = finrank 𝕜 (LinearMap.range A) := by
  let U := A.polarFactor
  let b := stdOrthonormalBasis 𝕜 E
  have h := U.trace_adjoint_comp_self_eq_sum_norm_apply_sq b
  rw [← sq_frobenius_apply b] at h
  have hproj := A.isPartialIsometry_polarFactor.isStarProjection_adjoint_comp_self
  have htr := ((isProj_range_iff_isIdempotentElem _).mpr hproj.isIdempotentElem).trace
  rw [U.range_adjoint_comp_self, U.finrank_range_adjoint, A.range_polarFactor] at htr
  rw [htr] at h
  exact_mod_cast h.symm

/-- The squared Frobenius seminorm of the polar factor plus an orthogonal kernel block is the
rank of the original map plus the squared Frobenius seminorm of that block. -/
theorem _root_.LinearMap.sq_frobenius_polarFactor_add_ker (A : E →ₗ[𝕜] F)
    (T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ) :
    frobenius 𝕜 E F (A.polarFactor + (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
      A.ker.orthogonalProjectionOnto.toLinearMap) ^ 2 =
      finrank 𝕜 (LinearMap.range A) + frobenius 𝕜 A.ker (LinearMap.range A)ᗮ T ^ 2 := by
  let := FiniteDimensional.completeSpace 𝕜 E
  let := FiniteDimensional.completeSpace 𝕜 A.ker
  let B : E →ₗ[𝕜] F := (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
    A.ker.orthogonalProjectionOnto.toLinearMap
  have horth := A.polarFactor.adjoint_comp_normalPart_eq_zero B
  rw [normalPart_polarFactor_subtype_comp A T] at horth
  have hB : frobenius 𝕜 E F B ^ 2 = frobenius 𝕜 A.ker (LinearMap.range A)ᗮ T ^ 2 := by
    have hproj (x : A.ker) :
        ‖(ContinuousLinearMap.adjoint A.ker.orthogonalProjectionOnto) x‖ = ‖x‖ := by
      rw [A.ker.adjoint_orthogonalProjectionOnto]
      rfl
    have h := ContinuousLinearMap.hilbertSchmidtEnergy_isometry_comp_coisometry
      (LinearMap.range A)ᗮ.subtypeL (fun _ ↦ rfl) T.toContinuousLinearMap
      A.ker.orthogonalProjectionOnto hproj
      (stdOrthonormalBasis 𝕜 E).toHilbertBasis (stdOrthonormalBasis 𝕜 A.ker).toHilbertBasis
    simp only [ContinuousLinearMap.hilbertSchmidtEnergy_eq_ofReal_sq_frobenius,
      ContinuousLinearMap.toLinearMap_comp, Submodule.toLinearMap_subtypeL,
      LinearMap.coe_toContinuousLinearMap] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp h
  calc
    _ = frobenius 𝕜 E F (A.polarFactor + B) ^ 2 := (rfl)
    _ = frobenius 𝕜 E F A.polarFactor ^ 2 + frobenius 𝕜 E F B ^ 2 :=
      sq_frobenius_add_of_re_trace_adjoint_comp_eq_zero (by rw [horth, map_zero, map_zero])
    _ = _ := by rw [A.sq_frobenius_polarFactor, hB]

end TauCeti.UnitarilyInvariantSeminorm
