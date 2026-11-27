/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Finite
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm

import TauCeti.Analysis.CStarAlgebra.Basic

/-!
# Operator norms of polar factors and their extensions

The canonical polar factor is a contraction and has operator norm one for a nonzero map.
All contractions factoring a map through its modulus are obtained by extending the polar
factor with a contraction from the kernel to the orthogonal complement of the range.
-/

public section

open TauCeti.UnitarilyInvariantSeminorm

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The canonical polar factor is a contraction. -/
theorem opNorm_polarFactor_le_one (A : E →ₗ[𝕜] F) :
    opNorm 𝕜 E F A.polarFactor ≤ 1 := by
  let := FiniteDimensional.completeSpace 𝕜 E
  let := FiniteDimensional.completeSpace 𝕜 F
  rw [opNorm_apply, A.toContinuousLinearMap_polarFactor]
  exact ContinuousLinearMap.norm_factorThru_le zero_le_one fun x ↦ by simp

/-- The polar factor of a nonzero map has operator norm one. -/
theorem opNorm_polarFactor_of_ne_zero {A : E →ₗ[𝕜] F} (hA : A ≠ 0) :
    opNorm 𝕜 E F A.polarFactor = 1 := by
  let := FiniteDimensional.completeSpace 𝕜 E
  have hproj := A.isPartialIsometry_polarFactor.isStarProjection_adjoint_comp_self
  have hn : adjoint A.polarFactor ∘ₗ A.polarFactor ≠ 0 := by
    intro h
    have hU : A.polarFactor = 0 := by
      simpa only [h, comp_zero] using A.isPartialIsometry_polarFactor.comp_adjoint_comp.symm
    exact hA (by simpa only [hU, zero_comp] using A.polarFactor_comp_operatorAbs.symm)
  have h := (LinearMap.isStarProjection_toContinuousLinearMap_iff.mpr hproj).norm_eq_one
    (fun he ↦ hn (LinearMap.toContinuousLinearMap.injective (by simpa using he)))
  rw [← opNorm_apply, opNorm_apply_adjoint_comp_self] at h
  refine le_antisymm A.opNorm_polarFactor_le_one (le_of_sq_le_sq ?_ (apply_nonneg _ _))
  simpa only [one_pow] using h.ge

/-- A contraction factoring `A` through its modulus maps the kernel of `A` into
the orthogonal complement of its range. -/
theorem mapsTo_ker_orthogonal_range_of_comp_operatorAbs_eq (A : E →ₗ[𝕜] F)
    {D : E →ₗ[𝕜] F} (hD : opNorm 𝕜 E F D ≤ 1) (h : D ∘ₗ A.operatorAbs = A) :
    Set.MapsTo D A.ker (LinearMap.range A)ᗮ := by
  let := FiniteDimensional.completeSpace 𝕜 E
  let := FiniteDimensional.completeSpace 𝕜 F
  have hDadj : opNorm 𝕜 F E (adjoint D) ≤ 1 := by
    rw [opNorm_apply, adjoint_toContinuousLinearMap, LinearIsometryEquiv.norm_map, ← opNorm_apply]
    exact hD
  simp only [opNorm_apply, ContinuousLinearMap.opNorm_le_iff zero_le_one, one_mul,
    LinearMap.coe_toContinuousLinearMap'] at hDadj
  intro x hx
  refine (Submodule.mem_orthogonal _ _).mpr ?_
  rintro _ ⟨y, rfl⟩
  have hy : D (A.operatorAbs y) = A y := LinearMap.congr_fun h y
  have hnorm : ‖D (A.operatorAbs y)‖ = ‖A.operatorAbs y‖ := by
    rw [hy, norm_operatorAbs_apply]
  -- The adjoint composition fixes every vector on which the contraction preserves the norm.
  have hgram : adjoint D (D (A.operatorAbs y)) = A.operatorAbs y := by
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜)
    · rw [← hnorm]
      exact hDadj _
    · rw [adjoint_inner_left, inner_self_eq_norm_sq, hnorm]
  rw [← hy, ← adjoint_inner_left, hgram]
  exact Submodule.inner_left_of_mem_orthogonal hx (A.range_operatorAbs ▸ mem_range_self _ y)

/-- A contraction factoring `A` through its modulus is the sum of the polar factor
and a contraction from the kernel to the orthogonal complement of the range,
extended by zero on the orthogonal complement of the kernel. -/
theorem exists_contraction_on_ker_of_comp_operatorAbs_eq (A : E →ₗ[𝕜] F)
    {D : E →ₗ[𝕜] F} (hD : opNorm 𝕜 E F D ≤ 1) (h : D ∘ₗ A.operatorAbs = A) :
    ∃ T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ, opNorm 𝕜 A.ker (LinearMap.range A)ᗮ T ≤ 1 ∧
      D = A.polarFactor + (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
        A.ker.orthogonalProjectionOnto.toLinearMap := by
  have hmaps := A.mapsTo_ker_orthogonal_range_of_comp_operatorAbs_eq hD h
  let T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ :=
    (D ∘ₗ A.ker.subtype).codRestrict _ fun x ↦ hmaps x.property
  have hT (x : A.ker) : (T x : F) = D x := rfl
  simp only [opNorm_apply, ContinuousLinearMap.opNorm_le_iff zero_le_one, one_mul,
    LinearMap.coe_toContinuousLinearMap'] at hD ⊢
  refine ⟨T, fun x ↦ ?_, ?_⟩
  · rw [← Submodule.norm_coe, hT]
    exact hD x
  · ext x
    obtain ⟨u, hu, v, hv, rfl⟩ := A.ker.exists_add_mem_mem_orthogonal x
    have hvD := (A.comp_operatorAbs_eq_iff_eqOn_polarFactor D).mp h hv
    have hprojV : A.ker.orthogonalProjectionOnto v = 0 :=
      A.ker.orthogonalProjectionOnto_eq_zero_iff.mpr hv
    have hprojU : A.ker.orthogonalProjectionOnto u = ⟨u, hu⟩ :=
      A.ker.orthogonalProjectionOnto_mem_subspace_eq_self ⟨u, hu⟩
    simp [A.polarFactor_apply_of_mem_ker hu, hprojU, hprojV, hT, hvD, add_comm]

/-- Adding an orthogonal kernel block of operator norm at most one to the polar factor
gives a contraction. -/
theorem opNorm_le_one_polarFactor_add_ker (A : E →ₗ[𝕜] F)
    {T : A.ker →ₗ[𝕜] (LinearMap.range A)ᗮ} (hT : opNorm 𝕜 A.ker (LinearMap.range A)ᗮ T ≤ 1) :
    opNorm 𝕜 E F (A.polarFactor + (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
      A.ker.orthogonalProjectionOnto.toLinearMap) ≤ 1 := by
  let B : E →ₗ[𝕜] F := (LinearMap.range A)ᗮ.subtype ∘ₗ T ∘ₗ
    A.ker.orthogonalProjectionOnto.toLinearMap
  have hB : opNorm 𝕜 E F B ≤ 1 := by
    simp only [opNorm_apply, ContinuousLinearMap.opNorm_le_iff zero_le_one, one_mul,
      LinearMap.coe_toContinuousLinearMap'] at hT ⊢
    intro x
    have hnorm : ‖B x‖ = ‖T (A.ker.orthogonalProjectionOnto x)‖ := (rfl)
    rw [hnorm]
    exact (hT _).trans (A.ker.norm_orthogonalProjectionOnto_apply_le x)
  have h₁ := A.polarFactor.adjoint_comp_normalPart_eq_zero B
  have h₂ := A.polarFactor.comp_adjoint_normalPart_eq_zero B
  -- The normal-part projection identifies the two vanishing cross terms.
  rw [normalPart_polarFactor_subtype_comp A T] at h₁ h₂
  calc
    _ = opNorm 𝕜 E F (A.polarFactor + B) := (rfl)
    _ = max (opNorm 𝕜 E F A.polarFactor) (opNorm 𝕜 E F B) :=
      opNorm_add_eq_max_of_twoSidedOrthogonal h₁ h₂
    _ ≤ 1 := max_le A.opNorm_polarFactor_le_one hB

end LinearMap
