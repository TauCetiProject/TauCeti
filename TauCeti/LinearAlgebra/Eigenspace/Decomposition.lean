/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

import TauCeti.LinearAlgebra.LinearMap.EqOn

/-!
# Decomposition into generalized eigenspaces

An injective endomorphism has no generalized eigenvectors with eigenvalue `0`. Over an
algebraically closed field, the generalized eigenspaces of an endomorphism of a finite-dimensional
vector space form an internal direct sum, combining Mathlib's
`Module.End.independent_maxGenEigenspace` and `Module.End.iSup_maxGenEigenspace_eq_top`, so an
endomorphism may be defined by prescribing a scalar on each of them.

## Main results

* `Module.End.maxGenEigenspace_zero_eq_bot_of_injective`: an injective endomorphism has no
  generalized eigenvectors with eigenvalue `0`.
* `Module.End.isInternal_maxGenEigenspace`: the generalized eigenspaces form an internal direct
  sum.
* `Module.End.scalarOn`: the endomorphism acting on the generalized `μ`-eigenspace of `F` by a
  scalar `s μ`, with `Module.End.scalarOn_apply`, `Module.End.scalarOn_mul` and
  `Module.End.commute_scalarOn`.
-/

public section

namespace Module.End

open Function

/-- An injective endomorphism has no generalized eigenvectors with eigenvalue `0`. -/
theorem maxGenEigenspace_zero_eq_bot_of_injective {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {F : End R M} (hF : Injective F) : F.maxGenEigenspace 0 = ⊥ := by
  refine eq_bot_iff.mpr fun v hv ↦ ?_
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace F 0 v).mp hv
  rw [zero_smul, sub_zero] at hk
  have hinj : Injective ⇑(F ^ k) := by
    rw [FunLike.coe_pow_eq_iterate]
    exact hF.iterate k
  exact (Submodule.mem_bot R).mpr ((injective_iff_map_eq_zero _).mp hinj v hk)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [IsAlgClosed K]
  [FiniteDimensional K V]

/-- The generalized eigenspaces of an endomorphism of a finite-dimensional vector space over an
algebraically closed field form an internal direct sum. -/
theorem isInternal_maxGenEigenspace [DecidableEq K] (F : End K V) :
    DirectSum.IsInternal fun μ ↦ F.maxGenEigenspace μ :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top F.independent_maxGenEigenspace
    (iSup_maxGenEigenspace_eq_top F)

open scoped Classical in
/-- The endomorphism of a finite-dimensional vector space over an algebraically closed field acting
on the generalized `μ`-eigenspace of `F` by the scalar `s μ`. -/
noncomputable def scalarOn (F : End K V) (s : K → K) : End K V :=
  DirectSum.toModule K K V (fun μ ↦ s μ • (F.maxGenEigenspace μ).subtype) ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun μ ↦ F.maxGenEigenspace μ)
      (isInternal_maxGenEigenspace F)).symm.toLinearMap

/-- `scalarOn F s` acts on the generalized `μ`-eigenspace of `F` by `s μ`. -/
theorem scalarOn_apply (F : End K V) (s : K → K) {μ : K} {v : V}
    (hv : v ∈ F.maxGenEigenspace μ) : scalarOn F s v = s μ • v := by
  classical
  have h : (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun μ ↦ F.maxGenEigenspace μ)
      (isInternal_maxGenEigenspace F)).symm v =
      DirectSum.lof K K (fun μ ↦ F.maxGenEigenspace μ) μ ⟨v, hv⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DirectSum.coeLinearMap_lof _ μ ⟨v, hv⟩).symm
  simp only [scalarOn, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [h, DirectSum.toModule_lof, LinearMap.smul_apply, Submodule.subtype_apply]

/-- Acting by `1` on every generalized eigenspace gives the identity. -/
@[simp]
theorem scalarOn_one (F : End K V) : scalarOn F 1 = 1 :=
  LinearMap.ext_of_iSup_eq_top (iSup_maxGenEigenspace_eq_top F) fun μ v hv ↦ by
    rw [scalarOn_apply F 1 hv, Pi.one_apply, one_smul, one_apply_eq_self]

/-- `scalarOn F` is multiplicative in the scalars. -/
theorem scalarOn_mul (F : End K V) (s t : K → K) :
    scalarOn F (s * t) = scalarOn F s * scalarOn F t :=
  LinearMap.ext_of_iSup_eq_top (iSup_maxGenEigenspace_eq_top F) fun μ v hv ↦ by
    rw [mul_apply_eq_comp, scalarOn_apply F t hv, scalarOn_apply F s (Submodule.smul_mem _ _ hv),
      scalarOn_apply F _ hv, smul_smul, Pi.mul_apply]

/-- `scalarOn F s` commutes with every endomorphism commuting with `F`. -/
theorem commute_scalarOn {F T : End K V} (hT : Commute F T) (s : K → K) :
    Commute (scalarOn F s) T :=
  (commute_iff_eq _ _).mpr <|
    LinearMap.ext_of_iSup_eq_top (iSup_maxGenEigenspace_eq_top F) fun μ v hv ↦ by
      rw [mul_apply_eq_comp, mul_apply_eq_comp, scalarOn_apply F s hv,
        scalarOn_apply F s (mapsTo_maxGenEigenspace_of_comm hT μ hv), map_smul]

end Module.End
