/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Module.Equiv.Pi

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Polynomial

/-!
# Determinants of continuous linear maps: relative determinants and the cofactor contraction

For continuous linear equivalences `T U : M ≃L[R] N` and a continuous linear map `S : M →L[R] N`,
the determinants on `M` of `T⁻¹ ∘ U`, `U⁻¹ ∘ S` and `T⁻¹ ∘ S` satisfy
`det (T⁻¹ ∘ U) * det (U⁻¹ ∘ S) = det (T⁻¹ ∘ S)`, and for endomorphisms `A` of `M` and `B` of `N`,
`det (T⁻¹ ∘ B ∘ S ∘ A) = det B * det (T⁻¹ ∘ S) * det A`. These relative determinants compare the
volumes of the images of a fixed body under maps into `N` without choosing a volume on `N`.

For a continuous linear automorphism `L` of `ι → R`, write `(L⁻¹)ⱼᵢ = L.symm (Pi.single i 1) j`
for the `(j, i)` entry of the matrix of `L⁻¹`, so that `det L • L⁻¹` is the cofactor (adjugate)
matrix of `L`. Contracting a family of continuous linear maps `F' i` precomposed with `L` against
this matrix and taking the trace recovers `det L` times the trace of `F'`:

`∑ j, (det L • ∑ i, (L⁻¹)ⱼᵢ • F' i ∘ L) (Pi.single j 1) = det L • ∑ i, F' i (Pi.single i 1)`,

because `∑ j, (L⁻¹)ⱼᵢ • L (Pi.single j 1) = L (L⁻¹ (Pi.single i 1)) = Pi.single i 1`. With `F' i`
the derivative of the `i`-th component of a flux field, this is the pointwise Piola identity of
the affine cofactor pullback, `ContinuousLinearEquiv.sum_fderiv_affineFluxPullback`.

## Main declarations

* `ContinuousLinearMap.det_id`, `ContinuousLinearMap.det_smul`: the determinant of the identity
  and of a scalar multiple.
* `ContinuousLinearMap.exists_le_norm_det_id_sub_smul`: over `ℝ` or `ℂ`, the second-order lower
  bound `1 - δ re (trace H) - P δ² ≤ ‖det (1 - δ H)‖` for `0 ≤ δ ≤ 1`.
* `ContinuousLinearEquiv.det_symm_comp_mul_det_symm_comp`: relative determinants multiply.
* `ContinuousLinearEquiv.det_symm_comp_comp_comp`: composing with endomorphisms on either side
  multiplies the relative determinant by their determinants.
* `ContinuousLinearEquiv.sum_cofactor_comp_apply_single`: the cofactor contraction identity.
-/

public section

namespace ContinuousLinearMap

variable {R M : Type*} [CommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

/-- The identity has determinant one. -/
@[simp]
theorem det_id : (ContinuousLinearMap.id R M).det = 1 :=
  LinearMap.det_id

/-- Multiplying a map by a scalar `c` multiplies its determinant by `c ^ finrank R M`. -/
@[simp]
theorem det_smul [ContinuousConstSMul R M] [Module.Free R M] (c : R) (f : M →L[R] M) :
    (c • f).det = c ^ Module.finrank R M * f.det :=
  LinearMap.det_smul c (f : M →ₗ[R] M)

section RCLike

open RCLike Set

variable {𝕜 E : Type*} [RCLike 𝕜] [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] [FiniteDimensional 𝕜 E]

/-- A second-order lower bound for `‖det (1 - δ H)‖` on `0 ≤ δ ≤ 1`, from the expansion
`det (1 + r M) = 1 + r trace M + O(r²)` of `Matrix.det_one_add_smul`. -/
theorem exists_le_norm_det_id_sub_smul (H : E →L[𝕜] E) :
    ∃ P : ℝ, ∀ δ ∈ Icc (0 : ℝ) 1,
      1 - δ * re (LinearMap.trace 𝕜 E H) - P * δ ^ 2 ≤
        ‖(ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H).det‖ := by
  classical
  let b := Module.finBasis 𝕜 E
  set M := LinearMap.toMatrix b b (H : E →ₗ[𝕜] E)
  set q := (Matrix.det (1 + (Polynomial.X : Polynomial 𝕜) • M.map Polynomial.C)).divX.divX
  obtain ⟨P, hP⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 0)).exists_bound_of_continuousOn
    ((q.continuous.comp RCLike.continuous_ofReal).continuousOn)
  refine ⟨P, fun δ hδ ↦ ?_⟩
  have hM : LinearMap.toMatrix b b
      ((ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H : E →L[𝕜] E) : E →ₗ[𝕜] E) =
        1 + (-(δ : 𝕜)) • M := by
    simp [M, sub_eq_add_neg]
  have hdet : (ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H).det =
      1 + LinearMap.trace 𝕜 E H * (-(δ : 𝕜)) + q.eval (-(δ : 𝕜)) * ((δ ^ 2 : ℝ) : 𝕜) := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, hM, Matrix.det_one_add_smul,
      LinearMap.trace_eq_matrix_trace 𝕜 b]
    push_cast
    ring
  have hq : ‖q.eval (-(δ : 𝕜))‖ ≤ P := by
    have := hP (-δ) ⟨neg_le_neg hδ.2, neg_nonpos.2 hδ.1⟩
    simpa only [Function.comp_apply, ofReal_neg] using this
  have hre : -(P * δ ^ 2) ≤ re (q.eval (-(δ : 𝕜)) * ((δ ^ 2 : ℝ) : 𝕜)) := by
    rw [mul_comm (q.eval _), re_ofReal_mul]
    nlinarith [abs_le.1 ((abs_re_le_norm _).trans hq), sq_nonneg δ]
  have htr : re (LinearMap.trace 𝕜 E H * (-(δ : 𝕜))) = -δ * re (LinearMap.trace 𝕜 E H) := by
    rw [mul_comm, ← ofReal_neg, re_ofReal_mul]
  calc 1 - δ * re (LinearMap.trace 𝕜 E H) - P * δ ^ 2
      ≤ re ((ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H).det) := by
        rw [hdet, AddMonoidHom.map_add re, AddMonoidHom.map_add re, htr, one_re]
        linarith
    _ ≤ ‖(ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H).det‖ := re_le_norm _

end RCLike

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section Relative

variable {R M N : Type*} [CommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [TopologicalSpace N] [AddCommGroup N] [Module R N]

/-- Determinants relative to equivalences `M ≃L[R] N` multiply: comparing `S` with `T` is
comparing `U` with `T` and then `S` with `U`. -/
theorem det_symm_comp_mul_det_symm_comp (T U : M ≃L[R] N) (S : M →L[R] N) :
    ((T.symm : N →L[R] M).comp (U : M →L[R] N)).det * ((U.symm : N →L[R] M).comp S).det =
      ((T.symm : N →L[R] M).comp S).det := by
  have h : ((T.symm : N →L[R] M).comp (U : M →L[R] N)).comp ((U.symm : N →L[R] M).comp S) =
      (T.symm : N →L[R] M).comp S := by
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc _ (U.symm : N →L[R] M),
      U.coe_comp_coe_symm, ContinuousLinearMap.id_comp]
  rw [← h]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

/-- The determinant of `S : M → N` relative to `T : M ≃L[R] N` is multiplicative under composition
with endomorphisms on either side: for `A : M →L[R] M` and `B : N →L[R] N`, the determinant of
`B ∘ S ∘ A` relative to `T` is `det B * det (T⁻¹ ∘ S) * det A`. -/
theorem det_symm_comp_comp_comp (T : M ≃L[R] N) (B : N →L[R] N) (S : M →L[R] N)
    (A : M →L[R] M) :
    ((T.symm : N →L[R] M).comp (B.comp (S.comp A))).det =
      B.det * ((T.symm : N →L[R] M).comp S).det * A.det := by
  -- Reading `B` in `M` through `T` does not change its determinant.
  have hB : ((T.symm : N →L[R] M).comp (B.comp (T : M →L[R] N))).det = B.det :=
    LinearMap.det_conj (B : N →ₗ[R] N) T.symm.toLinearEquiv
  have h : (T.symm : N →L[R] M).comp (B.comp (S.comp A)) =
      ((T.symm : N →L[R] M).comp (B.comp (T : M →L[R] N))).comp
        (((T.symm : N →L[R] M).comp S).comp A) := by
    ext v
    simp
  rw [h, ← hB]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    mul_assoc]

end Relative

variable {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]

/-- The cofactor contraction identity: the trace of the cofactor transform
`det L • ∑ i, (L⁻¹)ⱼᵢ • (F' i ∘ L)` of a family `F'` of continuous linear maps is `det L` times
the trace `∑ i, F' i (Pi.single i 1)`, as
`∑ j, (L⁻¹)ⱼᵢ • L (Pi.single j 1) = L (L⁻¹ (Pi.single i 1)) = Pi.single i 1`. -/
theorem sum_cofactor_comp_apply_single (L : (ι → R) ≃L[R] (ι → R))
    (F' : ι → (ι → R) →L[R] M) :
    ∑ j, (LinearMap.det (L : (ι → R) →ₗ[R] ι → R) •
        ∑ i, L.symm (Pi.single i 1) j • (F' i).comp (L : (ι → R) →L[R] ι → R))
          (Pi.single j 1) =
      LinearMap.det (L : (ι → R) →ₗ[R] ι → R) • ∑ i, F' i (Pi.single i 1) := by
  simp only [_root_.smul_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- Pull the coefficients through the linear map `F' i ∘ L`, then expand `L⁻¹ (Pi.single i 1)`
  -- in the standard basis.
  calc ∑ j, L.symm (Pi.single i 1) j • F' i (L (Pi.single j 1))
      _ = F' i (L (∑ j, L.symm (Pi.single i 1) j • Pi.single j 1)) := by
        simp only [map_sum, map_smul, ContinuousLinearMap.map_smul]
      _ = F' i (Pi.single i 1) := by rw [← pi_eq_sum_univ', apply_symm_apply]

end ContinuousLinearEquiv
