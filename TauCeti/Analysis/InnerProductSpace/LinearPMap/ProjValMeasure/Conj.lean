/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Basic
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Conj
import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Conj

/-!
# Unitary conjugation of the spectral measure of a self-adjoint operator

Conjugating a self-adjoint partial linear map `A` by a linear isometric equivalence
`U : H ≃ₗᵢ[ℂ] H'` conjugates its spectral projection-valued measure:
`(A.conj U).spectralPVM (hA.conj U) = (A.spectralPVM hA).conj U` (`LinearPMap.spectralPVM_conj`),
and hence conjugates its spectral projections (`LinearPMap.spectralPVM_proj_conj`) and bounded
spectral integrals (`LinearPMap.spectralPVM_integral_conj`).
-/

public section

noncomputable section

open TauCeti
open scoped InnerProductSpace

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {A : H →ₗ.[ℂ] H}

/-- Unitary conjugation transports the spectral projection-valued measure of a self-adjoint
partial operator. -/
@[simp]
theorem spectralPVM_conj (hA : IsSelfAdjoint A) (U : H ≃ₗᵢ[ℂ] H') :
    (A.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')).spectralPVM (hA.conj U) =
      (A.spectralPVM hA).conj U := by
  symm
  refine ((hA.conj U).eq_spectralPVM_iff _).2 fun z hz ξ ↦ ?_
  have hzA : z ∈ A.resolventSet := hA.mem_resolventSet_of_im_ne_zero hz.ne'
  have hinner : ⟪ξ, (A.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')).resolvent z ξ⟫_ℂ =
      ⟪U.symm ξ, A.resolvent z (U.symm ξ)⟫_ℂ := by
    rw [resolvent_conj (U : H ≃L[ℂ] H') hzA, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
    simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
      ← LinearIsometryEquiv.toContinuousLinearEquiv_symm, U.apply_symm_apply] using
      U.inner_map_map (U.symm ξ) (A.resolvent z (U.symm ξ))
  rw [ProjValMeasure.conj_diag]
  exact hinner.trans (hA.inner_resolvent_apply_eq_integral hzA (U.symm ξ))

/-- Unitary conjugation transports the spectral projections of a self-adjoint partial operator. -/
theorem spectralPVM_proj_conj (hA : IsSelfAdjoint A) (U : H ≃ₗᵢ[ℂ] H')
    (B : Set ℝ) (hB : MeasurableSet B) :
    ((A.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')).spectralPVM (hA.conj U)).proj B hB =
      U.conjStarAlgEquiv ((A.spectralPVM hA).proj B hB) := by
  rw [spectralPVM_conj, ProjValMeasure.conj_proj]

/-- Unitary conjugation commutes with bounded spectral integrals of a self-adjoint partial
operator. -/
theorem spectralPVM_integral_conj (hA : IsSelfAdjoint A) (U : H ≃ₗᵢ[ℂ] H')
    (g : BoundedBorelFunction ℝ) :
    ((A.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')).spectralPVM (hA.conj U)).integral g =
      U.conjStarAlgEquiv ((A.spectralPVM hA).integral g) := by
  rw [spectralPVM_conj, ProjValMeasure.integral_conj]

end LinearPMap
