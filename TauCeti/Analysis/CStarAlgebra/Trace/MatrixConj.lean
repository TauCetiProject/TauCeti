/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Trace.Matrix

/-!
# Invariance of the matrix amplification of a trace under scalar unitaries

For a C⋆-algebra `B`, a scalar matrix `u ∈ M_n(ℂ)` acts on `M_n(B) = CStarMatrix n n B` by
conjugation, `(u x u⋆)ᵢⱼ = Σₖ Σₗ uᵢₖ ū_{jl} xₖₗ`; for nonunital `B` the scalar matrices are not
elements of `M_n(B)`, so this is the compression `CStarMatrix.compress u u x` by the rows of `u`.

For a trace `τ` on `B` (`TauCeti.IsTrace`) and a unitary `u`, the matrix amplification
`τ_n(x) = Σᵢ τ(xᵢᵢ)` (`TauCeti.matrixTrace`) satisfies `τ_n(u x u⋆) = τ_n(x)` for `x ∈ M_n(B)₊`
(`TauCeti.IsTrace.matrixTrace_compress_self`). Writing `x = R⋆R` and `z = R u⋆`, we have
`z⋆z = u x u⋆` and, since `u⋆u = 1`, `zz⋆ = RR⋆`; the trace identity of the trace `τ_n`
(`TauCeti.IsTrace.isTrace_matrixTrace`) then gives `τ_n(u x u⋆) = τ_n(RR⋆) = τ_n(R⋆R)`.

## Main results

* `CStarMatrix.compress_self_nonneg`: conjugation by a scalar matrix preserves positivity.
* `TauCeti.IsTrace.matrixTrace_compress_self`: `τ_n(u x u⋆) = τ_n(x)` for unitary scalar `u`.
-/

public section

open scoped ENNReal NNReal

variable {B : Type*} [NonUnitalCStarAlgebra B] {n : Type*} [Fintype n]

namespace CStarMatrix

/-- The product `R u⋆` of `R ∈ M_n(B)` with the adjoint of a scalar matrix `u`. -/
private def mulStarScalar (R : CStarMatrix n n B) (u : CStarMatrix n n ℂ) : CStarMatrix n n B :=
  ofMatrix (Matrix.of fun i j ↦ ∑ k, star (u j k) • R i k)

/-- `(R u⋆)⋆ (R u⋆) = u (R⋆R) u⋆`. -/
private theorem star_mulStarScalar_mul_self (R : CStarMatrix n n B) (u : CStarMatrix n n ℂ) :
    star (mulStarScalar R u) * mulStarScalar R u = compress u u (star R * R) := by
  ext i j
  rw [compress_apply u u]
  simp only [mulStarScalar, mul_apply, star_apply, ofMatrix_apply, Matrix.of_apply,
    star_sum, star_smul, star_star, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm,
    Finset.smul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm, Finset.sum_comm]

/-- For `u⋆u = 1`, `(R u⋆)(R u⋆)⋆ = RR⋆`. -/
private theorem mulStarScalar_mul_star_self [DecidableEq n] (R : CStarMatrix n n B)
    {u : CStarMatrix n n ℂ} (hu : star u * u = 1) :
    mulStarScalar R u * star (mulStarScalar R u) = R * star R := by
  ext i j
  have h (k l : n) : ∑ m, star (u m k) * u m l = if k = l then 1 else 0 := by
    have := congrFun (congrFun (congrArg ofMatrix.symm hu) k) l
    simpa [mul_apply, star_apply, one_apply] using this
  simp only [mulStarScalar, mul_apply, star_apply, ofMatrix_apply, Matrix.of_apply, star_sum,
    star_smul, star_star, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  -- Reorder to `Σₖ Σₗ (Σₘ ū_{mk} u_{ml}) • (R_{ik} R_{jl}⋆)` and use `u⋆u = 1`.
  rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq]
  simp

variable [PartialOrder B] [StarOrderedRing B]

/-- **Conjugation by a scalar matrix preserves positivity**: `0 ≤ x` gives `0 ≤ u x u⋆`. -/
theorem compress_self_nonneg (u : CStarMatrix n n ℂ) {x : CStarMatrix n n B} (hx : 0 ≤ x) :
    0 ≤ compress u u x := by
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  rw [← star_mulStarScalar_mul_self]
  exact star_mul_self_nonneg _

end CStarMatrix

namespace TauCeti

variable [PartialOrder B] [StarOrderedRing B] {τ : B → ℝ≥0∞} [DecidableEq n]

/-- **Invariance under scalar unitaries**: for a trace `τ`, a unitary `u ∈ M_n(ℂ)` and
`x ∈ M_n(B)₊`, `τ_n(u x u⋆) = τ_n(x)`. -/
theorem IsTrace.matrixTrace_compress_self (hτ : IsTrace τ) {u : CStarMatrix n n ℂ}
    (hu : u ∈ unitary (CStarMatrix n n ℂ)) {x : CStarMatrix n n B} (hx : 0 ≤ x) :
    matrixTrace τ n (CStarMatrix.compress u u x) = matrixTrace τ n x := by
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  rw [← CStarMatrix.star_mulStarScalar_mul_self, hτ.isTrace_matrixTrace.map_star_mul_self,
    CStarMatrix.mulStarScalar_mul_star_self R (Unitary.star_mul_self_of_mem hu),
    hτ.isTrace_matrixTrace.map_star_mul_self]

end TauCeti
