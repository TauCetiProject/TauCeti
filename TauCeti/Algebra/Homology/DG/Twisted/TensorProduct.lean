/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.LeftModule
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Pi

/-!
# The twisted complex as a tensor product

The twisted complex `ℳ ⊗ ⟨P⟩` of `TauCeti.Algebra.Homology.DG.Twisted.Complex` is the module
`P → M` with the twisted differential.  This file identifies it with the balanced tensor product
`M ⊗_A K_m` of the differential graded right module `(ℳ, dM)` with the complex
`K_m = (P → A, twistedDifferential m 𝒜 dA)` of free left modules of
`TauCeti.Algebra.Homology.DG.Twisted.LeftModule`, carrying the tensor differential
`d (α ⊗ k) = dM α ⊗ k + (-1) ^ |α| α ⊗ d k` of
`TauCeti.Algebra.Homology.DG.Module.TensorProduct.Differential`.

The identification is `TauCeti.BalancedTensorProduct.piRight`, `α ⊗ g ↦ fun y ↦ α · g y`.  It
intertwines the two differentials (`piRight_differential`) and carries the total degree of the
tensor product onto the total grading of `P → M` (`map_grading_piece_eq_twistedTotalGrading`).
So the twisted differential is the tensor differential of `ℳ` with `K_m`, read through the
identification `M ⊗_A (P → A) ≅ (P → M)`: this is the sense in which the twisted complex of a
right module is `𝓕 ⊗_A K_m`.

## Main results

* `TauCeti.BalancedTensorProduct.piRight_differential`: `piRight` intertwines the tensor
  differential of `ℳ ⊗_A K_m` with the twisted differential on `P → M`, for any matrix `m` for
  which `K_m` is a differential graded left module; for a twisting cocycle `m`, apply it to
  `m.isDGLeftModule_twistedDifferential`.
* `TauCeti.BalancedTensorProduct.piRight_mem_twistedTotalGrading`,
  `TauCeti.BalancedTensorProduct.piRight_symm_mem_grading`,
  `TauCeti.BalancedTensorProduct.map_grading_piece_eq_twistedTotalGrading`: `piRight` carries the
  degree-`n` piece of the tensor product onto the total-degree-`n` piece of `P → M`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {P : Type uP} {ind : P → ℤ}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

namespace BalancedTensorProduct

variable [Fintype P] {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M}
  (m : P → P → A) in
/-- **The twisted differential is the tensor differential of `ℳ` with `K_m`**: under
`α ⊗ g ↦ fun y ↦ α · g y`, the differential of the balanced tensor product of the right module
`(ℳ, dM)` with the complex `K_m = (P → A, twistedDifferential m 𝒜 dA)` of free left modules is the
twisted differential of `m` on `P → M`. -/
@[simp]
theorem piRight_differential (hM : IsDGRightModule hA ℳ dM)
    (hK : IsDGLeftModule hA (twistedTotalGrading 𝒜 ind) (twistedDifferential m 𝒜 dA))
    (z : BalancedTensorProduct R A M (P → A)) :
    piRight R A M P (differential hM hK z) = twistedDifferential m ℳ dM (piRight R A M P z) := by
  classical
  -- Both sides are linear in `z`, and `α ⊗ g = Σ_x (α · g x) ⊗ e_x`; compare on `β ⊗ e_x`.
  suffices key : ∀ (β : M) (x : P),
      piRight R A M P (differential hM hK (tmul R A β (Pi.single x 1))) =
        twistedDifferential m ℳ dM (piRight R A M P (tmul R A β (Pi.single x 1))) by
    induction z using induction_on with
    | ht α g =>
      rw [← (piRight R A M P).symm_apply_apply (tmul R A α g), piRight_symm_apply, piRight_tmul]
      simp only [map_sum, key]
    | ha z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  intro β x
  -- The differential of the generator `e_x` of `K_m` is `Σ_y m x y • e_y`.
  have hK_single : twistedDifferential m 𝒜 dA (Pi.single x 1) = ∑ y, Pi.single y (m x y) := by
    rw [twistedDifferential_single m dA x (SetLike.one_mem_graded 𝒜), hA.map_one_eq_zero,
      Pi.single_zero, zero_add]
    simp only [Int.negOnePow_zero, one_smul, op_smul_eq_mul, one_mul]
  rw [differential_tmul, hK_single, map_add, piRight_tmul_single, piRight_tmul_single]
  simp_rw [← mk_apply, map_sum, mk_apply]
  funext z
  -- On both sides, only the `z`-th, respectively the `x`-th, term of the sum survives.
  have h₁ : (∑ y, piRight R A M P (tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 β)
        (Pi.single y (m x y)))) z =
      op (m x z) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 β := by
    simp only [piRight_tmul, Finset.sum_apply]
    rw [Finset.sum_eq_single z (fun y _ hy ↦ by rw [Pi.single_eq_of_ne hy.symm, op_zero, zero_smul])
      (fun h ↦ (h (Finset.mem_univ z)).elim), Pi.single_eq_same]
  have h₂ : ∑ y, op (m y z) •
        (InternalGrading.ofDecomposition ℳ).koszulTwist 1 ((Pi.single x β : P → M) y) =
      op (m x z) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 β := by
    rw [Finset.sum_eq_single x (fun y _ hy ↦ by rw [Pi.single_eq_of_ne hy, map_zero, smul_zero])
      (fun h ↦ (h (Finset.mem_univ x)).elim), Pi.single_eq_same]
  rw [Pi.add_apply, h₁, twistedDifferential_apply, h₂]
  congr 1
  by_cases hz : z = x
  · subst hz
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hz, Pi.single_eq_of_ne hz, map_zero]

section Grading

attribute [local instance] tensorGradedRight tensorGradedLeft

variable [Fintype P]

/-- The total-degree grading of `M ⊗_A K_m`, with `K_m` graded by `twistedTotalGrading 𝒜 ind`. -/
local notation "twistedGrading" => grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
  (InternalGrading.ofDecomposition (twistedTotalGrading 𝒜 ind))

local notation "coefficientGrading" => grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
  (InternalGrading.ofDecomposition (rowFiniteTotalGrading 𝒜 ind))

-- This is the finite-support/function change of coordinates used in `piRight`.
-- Its pure-tensor formulas use `erw` to reduce the identity in the equivariance proofs.
local notation "finiteTensorEquiv" =>
  congr (LinearEquiv.refl R M) (Finsupp.linearEquivFunOnFinite R A P)
    (by intros; rfl) (by intros; rfl)

/-- `piRight` carries a tensor of total degree `n` to a function of total degree `n`. -/
theorem piRight_mem_twistedTotalGrading {n : ℤ} {z : BalancedTensorProduct R A M (P → A)}
    (hz : z ∈ (twistedGrading).piece n) :
    piRight R A M P z ∈ twistedTotalGrading ℳ ind n := by
  have hz' : (finiteTensorEquiv).symm z ∈ (coefficientGrading).piece n := by
    simpa only [add_zero, LinearEquiv.coe_coe] using
      map_mem_of_tmul (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
        (InternalGrading.ofDecomposition (twistedTotalGrading 𝒜 ind))
        (coefficientGrading).piece (finiteTensorEquiv).symm.toLinearMap 0
        (fun hα hg ↦ by
          erw [congr_symm_tmul]
          simpa only [add_zero, LinearEquiv.refl_symm, LinearEquiv.refl_apply] using
            tmul_mem_grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
              (InternalGrading.ofDecomposition (rowFiniteTotalGrading 𝒜 ind)) hα
              (by simpa only [InternalGrading.ofDecomposition_piece,
                mem_rowFiniteTotalGrading_iff, mem_twistedTotalGrading_iff,
                Finsupp.linearEquivFunOnFinite_symm_apply] using hg)) hz
  simpa only [piRight_eq_finsuppScalarRight, LinearEquiv.trans_apply,
    Finsupp.linearEquivFunOnFinite_apply] using
    (mem_rowFiniteTotalGrading_iff_twistedTotalGrading ℳ ind n _).mp
      (finsuppScalarRight_mem_rowFiniteTotalGrading hz')

/-- The inverse of `piRight` carries a function of total degree `n` to a tensor of total
degree `n`. -/
theorem piRight_symm_mem_grading {n : ℤ} {f : P → M} (hf : f ∈ twistedTotalGrading ℳ ind n) :
    (piRight R A M P).symm f ∈ (twistedGrading).piece n := by
  have hf' : (Finsupp.linearEquivFunOnFinite R M P).symm f ∈
      rowFiniteTotalGrading ℳ ind n := by
    simpa only [mem_rowFiniteTotalGrading_iff, mem_twistedTotalGrading_iff,
      Finsupp.linearEquivFunOnFinite_symm_apply] using hf
  have hz := finsuppScalarRight_symm_mem_grading (𝒜 := 𝒜) hf'
  have h := map_mem_of_tmul (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
    (InternalGrading.ofDecomposition (rowFiniteTotalGrading 𝒜 ind))
    (twistedGrading).piece (finiteTensorEquiv).toLinearMap 0
    (fun hα hg ↦ by
      erw [congr_tmul]
      simpa only [add_zero, LinearEquiv.refl_apply] using
        tmul_mem_grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
          (InternalGrading.ofDecomposition (twistedTotalGrading 𝒜 ind)) hα
          (by simpa only [InternalGrading.ofDecomposition_piece,
            mem_rowFiniteTotalGrading_iff, mem_twistedTotalGrading_iff,
            Finsupp.linearEquivFunOnFinite_apply] using hg)) hz
  simpa only [add_zero, piRight_eq_finsuppScalarRight, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.coe_coe] using h

/-- **`piRight` carries the total degree of `M ⊗_A K_m` onto the total grading of `P → M`.** -/
theorem map_grading_piece_eq_twistedTotalGrading (n : ℤ) :
    ((twistedGrading).piece n).map (piRight R A M P).toLinearMap =
      twistedTotalGrading ℳ ind n := by
  ext f
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact piRight_mem_twistedTotalGrading hz
  · intro hf
    exact ⟨_, piRight_symm_mem_grading hf, (piRight R A M P).apply_symm_apply f⟩

end Grading

end BalancedTensorProduct

end TauCeti
