/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.LinearAlgebra.Matrix.Trace.Duality

/-!
# Trace duality on `CStarMatrix`

This file proves linear trace duality on `CStarMatrix`
(`CStarMatrix.existsUnique_trace_mul_eq` and `CStarMatrix.existsUnique_sum_trace_mul_eq`) and
records adjoint invariance of the trace pairing (`CStarMatrix.trace_star_mul_star` and
`CStarMatrix.norm_sum_trace_star_mul_star`).
-/

public section

namespace CStarMatrix

section TraceDuality

/-- **Trace duality on `CStarMatrix`.** Every linear functional on `CStarMatrix n n R` is
`M ↦ tr(ρ * M)` for a unique `ρ : CStarMatrix n n R`. -/
theorem existsUnique_trace_mul_eq {n R : Type*} [Fintype n] [CommSemiring R]
    (φ : CStarMatrix n n R →ₗ[R] R) :
    ∃! ρ : CStarMatrix n n R, ∀ M, φ M = Matrix.trace (ofMatrix.symm (ρ * M)) := by
  obtain ⟨ρ, hρ, huniq⟩ := (φ.comp (ofMatrixₗ (R := R)).toLinearMap).existsUnique_trace_mul_eq
  refine ⟨ofMatrix ρ, fun M => by simpa [ofMatrix_symm_mul] using hρ (ofMatrix.symm M),
    fun ρ' hρ' => ofMatrix.symm.injective <| by
      rw [Equiv.symm_apply_apply]
      exact huniq (ofMatrix.symm ρ') fun M => by simpa [ofMatrix_symm_mul] using hρ' (ofMatrix M)⟩

/-- **Trace duality on finite families of `CStarMatrix`.** Every linear functional on
`ι → CStarMatrix n n R` is `b ↦ ∑ k, tr(x k * b k)` for a unique family `x`. -/
theorem existsUnique_sum_trace_mul_eq {ι n R : Type*} [Fintype ι] [Fintype n] [CommSemiring R]
    (φ : (ι → CStarMatrix n n R) →ₗ[R] R) :
    ∃! x : ι → CStarMatrix n n R, ∀ b, φ b = ∑ k, Matrix.trace (ofMatrix.symm (x k * b k)) := by
  classical
  let emb (k : ι) := LinearMap.single R (fun _ : ι => CStarMatrix n n R) k
  choose x hx huniq using fun k => existsUnique_trace_mul_eq (φ.comp (emb k))
  refine ⟨x, fun b => ?_, fun y hy => funext fun k => huniq k (y k) fun M => ?_⟩
  · conv_lhs => rw [← Finset.univ_sum_single b]
    rw [map_sum]; exact Finset.sum_congr rfl fun k _ => hx k (b k)
  · have h := hy (Pi.single k M)
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
      (fun hk => absurd (Finset.mem_univ k) hk)] at h
    simpa [emb] using h

/-- For a commutative star-semiring `A`, `tr(x⋆ * y⋆) = (tr(x * y))⋆` on `CStarMatrix n n A`. -/
theorem trace_star_mul_star {n A : Type*} [Fintype n] [CommSemiring A] [StarRing A]
    (x y : CStarMatrix n n A) :
    Matrix.trace (ofMatrix.symm (star x * star y)) =
      star (Matrix.trace (ofMatrix.symm (x * y))) := by
  rw [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_star, ← Matrix.conjTranspose_mul,
    Matrix.trace_conjTranspose, Matrix.trace_mul_comm, ofMatrix_symm_mul]

/-- Adjoint invariance of the trace-pairing norm for finite families in `CStarMatrix n n A`. -/
theorem norm_sum_trace_star_mul_star {ι n A : Type*} [Fintype ι] [Fintype n] [NormedCommRing A]
    [StarRing A] [NormedStarGroup A] (x y : ι → CStarMatrix n n A) :
    ‖∑ k, Matrix.trace (ofMatrix.symm (star (x k) * star (y k)))‖ =
      ‖∑ k, Matrix.trace (ofMatrix.symm (x k * y k))‖ := by
  simp_rw [trace_star_mul_star, ← star_sum, norm_star]

end TraceDuality

end CStarMatrix
