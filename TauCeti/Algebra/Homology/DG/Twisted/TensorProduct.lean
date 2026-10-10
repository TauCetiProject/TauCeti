/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.LeftModule
public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Complex
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
  which `K_m` is a differential graded left module; `TauCeti.TwistingCocycle.piRight_differential`
  is the case of a twisting cocycle.
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
  {P : Type uP} [Fintype P] [DecidableEq P] {ind : P → ℤ}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {dM : M →ₗ[R] M} (m : P → P → A)

namespace BalancedTensorProduct

/-- **The twisted differential is the tensor differential of `ℳ` with `K_m`**: under
`α ⊗ g ↦ fun y ↦ α · g y`, the differential of the balanced tensor product of the right module
`(ℳ, dM)` with the complex `K_m = (P → A, twistedDifferential m 𝒜 dA)` of free left modules is the
twisted differential of `m` on `P → M`. -/
theorem piRight_differential (hM : IsDGRightModule hA ℳ dM)
    (hK : IsDGLeftModule hA (twistedTotalGrading 𝒜 ind) (twistedDifferential m 𝒜 dA))
    (z : BalancedTensorProduct R A M (P → A)) :
    piRight R A M P (differential hM hK z) = twistedDifferential m ℳ dM (piRight R A M P z) := by
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

-- Use the characteristic piece equation, since `ofDecomposition` is opaque across modules.
local instance : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (InternalGrading.ofDecomposition ℳ).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

omit [Fintype P] [DecidableEq P] in
local instance [Finite P] : SetLike.GradedSMul 𝒜
    (InternalGrading.ofDecomposition (twistedTotalGrading 𝒜 ind)).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- The total-degree grading of `M ⊗_A K_m`, with `K_m` graded by `twistedTotalGrading 𝒜 ind`. -/
local notation "twistedGrading" => grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
  (InternalGrading.ofDecomposition (twistedTotalGrading 𝒜 ind))

omit m in
/-- `piRight` carries a tensor of total degree `n` to a function of total degree `n`. -/
theorem piRight_mem_twistedTotalGrading {n : ℤ} {z : BalancedTensorProduct R A M (P → A)}
    (hz : z ∈ (twistedGrading).piece n) :
    piRight R A M P z ∈ twistedTotalGrading ℳ ind n := by
  rw [grading_piece_eq_iSup (𝒜 := 𝒜)] at hz
  refine (iSup_le fun q ↦ Submodule.map₂_le.mpr fun β hβ g hg ↦ ?_ :
    _ ≤ (twistedTotalGrading ℳ ind n).comap (piRight R A M P).toLinearMap) hz
  rw [InternalGrading.ofDecomposition_piece] at hβ hg
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, mk_apply, piRight_tmul,
    mem_twistedTotalGrading_iff]
  intro y
  rw [mem_twistedTotalGrading_iff] at hg
  have hop : op (g y) ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece (n - q + ind y) :=
    ((InternalGrading.ofDecomposition 𝒜).op_mem_opposite_piece_iff _ _).2
      (by simpa only [InternalGrading.ofDecomposition_piece] using hg y)
  have := SetLike.GradedSMul.smul_mem hop hβ
  rwa [vadd_eq_add, show n - q + ind y + q = n + ind y by ring] at this

omit m in
/-- The inverse of `piRight` carries a function of total degree `n` to a tensor of total
degree `n`. -/
theorem piRight_symm_mem_grading {n : ℤ} {f : P → M} (hf : f ∈ twistedTotalGrading ℳ ind n) :
    (piRight R A M P).symm f ∈ (twistedGrading).piece n := by
  rw [piRight_symm_apply]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  rw [mem_twistedTotalGrading_iff] at hf
  have hsingle : (Pi.single x (1 : A) : P → A) ∈ twistedTotalGrading 𝒜 ind (-ind x) := by
    rw [mem_twistedTotalGrading_iff]
    intro y
    by_cases hy : y = x
    · subst hy
      rw [Pi.single_eq_same, neg_add_cancel]
      exact SetLike.one_mem_graded 𝒜
    · rw [Pi.single_eq_of_ne hy]
      exact zero_mem _
  have := tmul_mem_grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
    (InternalGrading.ofDecomposition (twistedTotalGrading 𝒜 ind))
    (by simpa only [InternalGrading.ofDecomposition_piece] using hf x)
    (by simpa only [InternalGrading.ofDecomposition_piece] using hsingle)
  simpa only [add_neg_cancel_right] using this

omit m in
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

namespace TwistingCocycle

/-- **The twisted complex of a twisting cocycle is the tensor product `ℳ ⊗_A K_m`**: under
`α ⊗ g ↦ fun y ↦ α · g y`, the tensor differential of the right module `(ℳ, dM)` with the complex
`K_m` of free left modules is the twisted differential. -/
theorem piRight_differential (m : TwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hA ℳ dM)
    (z : BalancedTensorProduct R A M (P → A)) :
    BalancedTensorProduct.piRight R A M P
        (BalancedTensorProduct.differential hM m.isDGLeftModule_twistedDifferential z) =
      twistedDifferential m.m ℳ dM (BalancedTensorProduct.piRight R A M P z) :=
  BalancedTensorProduct.piRight_differential m.m hM m.isDGLeftModule_twistedDifferential z

end TwistingCocycle

end TauCeti
