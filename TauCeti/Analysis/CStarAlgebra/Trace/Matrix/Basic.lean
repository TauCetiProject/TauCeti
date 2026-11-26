/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Trace.Basic

/-!
# Matrix amplification of traces

For a trace `τ : B → ℝ≥0∞` on a C⋆-algebra `B` (`TauCeti.IsTrace`) and a finite type `n`, the
**matrix amplification** `τ_n(x) = Σᵢ τ(xᵢᵢ)` on `M_n(B) = CStarMatrix n n B`
(`TauCeti.matrixTrace`) is again a trace (`TauCeti.IsTrace.isTrace_matrixTrace`, Thomsen [WTK],
Lemma 3.1). The diagonal entries of a positive matrix are positive, which gives
additivity and homogeneity on `M_n(B)₊`; for the trace identity, the diagonal entries of `x⋆x` and
`xx⋆` are `Σₖ xₖᵢ⋆xₖᵢ` and `Σₖ xᵢₖxᵢₖ⋆`, and summing over `i` both give
`Σᵢ,ₖ τ(xₖᵢ⋆xₖᵢ)` by the trace identity of `τ`.

The same computation identifies the square-integrable elements: `𝔫_{τ_n} = M_n(𝔫_τ)`
(`TauCeti.IsTrace.mem_sqIntegrable_matrixTrace_iff`, Thomsen [WTK], Lemma 3.1 (e)). The
amplification is faithful when `τ` is (`TauCeti.IsFaithful.matrixTrace`): a positive matrix `R⋆R`
whose diagonal entries `Σₖ Rₖᵢ⋆Rₖᵢ` vanish has `R = 0`. It is lower semicontinuous when `τ` is
(`LowerSemicontinuousOn.matrixTrace`), and it is additive over the diagonal blocks of a block
matrix (`TauCeti.matrixTrace_fromBlocks`).

## Main definitions

* `TauCeti.matrixTrace`: the amplification `τ_n(x) = Σᵢ τ(xᵢᵢ)`.

## Main results

* `TauCeti.IsTrace.isTrace_matrixTrace`: `τ_n` is a trace.
* `TauCeti.IsTrace.mem_sqIntegrable_matrixTrace_iff`: `𝔫_{τ_n} = M_n(𝔫_τ)`.
* `TauCeti.IsFaithful.matrixTrace`: `τ_n` is faithful when `τ` is.
* `LowerSemicontinuousOn.matrixTrace`: `τ_n` is lower semicontinuous when `τ` is.
* `TauCeti.matrixTrace_fromBlocks`: `τ_{n ⊕ m}([[x, b], [c, y]]) = τ_n(x) + τ_m(y)`.

## References

* Klaus Thomsen, *On weights, traces and K-theory*, arXiv:2211.03172, version of 15 March 2024:
  Lemma 3.1.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {τ : B → ℝ≥0∞} {n m : Type*} [Fintype n] [Fintype m]

variable (τ n) in
/-- The **matrix amplification** `τ_n(x) = Σᵢ τ(xᵢᵢ)` of a map `τ : B → ℝ≥0∞` to
`M_n(B) = CStarMatrix n n B`. -/
noncomputable def matrixTrace (x : CStarMatrix n n B) : ℝ≥0∞ :=
  ∑ i, τ (x i i)

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] in
/-- The value of the matrix amplification. -/
theorem matrixTrace_apply (x : CStarMatrix n n B) : matrixTrace τ n x = ∑ i, τ (x i i) :=
  (rfl)

namespace IsTrace

/-- `τ_n(x⋆x) = Σᵢ,ₖ τ(xₖᵢ⋆xₖᵢ)`. -/
theorem matrixTrace_star_mul_self (hτ : IsTrace τ) (x : CStarMatrix n n B) :
    matrixTrace τ n (star x * x) = ∑ i, ∑ k, τ (star (x k i) * x k i) := by
  simp only [matrixTrace_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply]
  exact Finset.sum_congr rfl fun i _ ↦
    hτ.map_sum_of_nonneg _ fun k _ ↦ star_mul_self_nonneg _

/-- `τ_n(xx⋆) = Σᵢ,ₖ τ(xᵢₖxᵢₖ⋆)`. -/
theorem matrixTrace_mul_star_self (hτ : IsTrace τ) (x : CStarMatrix n n B) :
    matrixTrace τ n (x * star x) = ∑ i, ∑ k, τ (x i k * star (x i k)) := by
  simp only [matrixTrace_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply]
  exact Finset.sum_congr rfl fun i _ ↦
    hτ.map_sum_of_nonneg _ fun k _ ↦ mul_star_self_nonneg _

/-- **The matrix amplification of a trace is a trace** (Thomsen [WTK], Lemma 3.1). -/
theorem isTrace_matrixTrace (hτ : IsTrace τ) : IsTrace (matrixTrace τ n) where
  map_add_of_nonneg x y hx hy := by
    simp only [matrixTrace_apply, CStarMatrix.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ hτ.map_add_of_nonneg
      (CStarMatrix.diag_nonneg_of_nonneg hx i) (CStarMatrix.diag_nonneg_of_nonneg hy i)
  map_nnreal_smul_of_nonneg c x hx := by
    simp only [matrixTrace_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      hτ.map_nnreal_smul_of_nonneg c (CStarMatrix.diag_nonneg_of_nonneg hx i)
  map_star_mul_self x := by
    rw [hτ.matrixTrace_star_mul_self, hτ.matrixTrace_mul_star_self, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦
      hτ.map_star_mul_self _

/-- **`𝔫_{τ_n} = M_n(𝔫_τ)`**: a matrix is square-integrable for the amplification exactly when
all its entries are square-integrable for `τ` (Thomsen [WTK], Lemma 3.1 (e)). -/
theorem mem_sqIntegrable_matrixTrace_iff (hτ : IsTrace τ) {x : CStarMatrix n n B} :
    x ∈ sqIntegrable (matrixTrace τ n) ↔ ∀ i j, x i j ∈ sqIntegrable τ := by
  simp only [mem_sqIntegrable, hτ.matrixTrace_star_mul_self, ENNReal.sum_lt_top,
    Finset.mem_univ, forall_const]
  exact forall_comm

end IsTrace

/-- The amplification of a map that is lower semicontinuous on `B₊` is lower semicontinuous on
`M_n(B)₊`. -/
theorem _root_.LowerSemicontinuousOn.matrixTrace (hlsc : LowerSemicontinuousOn τ {x | 0 ≤ x}) :
    LowerSemicontinuousOn (matrixTrace τ n) {x | 0 ≤ x} := by
  -- Mathlib's `CStarMatrix.ofMatrixL` is built from `continuous_id` in both directions, so
  -- `ofMatrixL.symm x i j` is definitionally `x i j`; the ascription below records this step.
  have hentry (i : n) : Continuous fun x : CStarMatrix n n B ↦ x i i :=
    CStarMatrix.ofMatrixL.symm.continuous.matrix_elem i i
  exact lowerSemicontinuousOn_sum fun i _ ↦ hlsc.comp (hentry i).continuousOn
    fun _ hx ↦ CStarMatrix.diag_nonneg_of_nonneg hx i

/-- **The amplification of a faithful trace is faithful.** -/
theorem IsFaithful.matrixTrace (hτ : IsFaithful τ) : IsFaithful (matrixTrace τ n) := by
  refine isFaithful_iff.2 fun x hx h0 ↦ ?_
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  -- Each diagonal entry `Σₖ Rₖᵢ⋆Rₖᵢ` has trace `0`, hence vanishes, hence so does each `Rₖᵢ`.
  have hdiag (i : n) : (star R * R) i i = 0 := by
    refine hτ.eq_zero (CStarMatrix.diag_nonneg_of_nonneg hx i) ?_
    rw [matrixTrace_apply] at h0
    exact (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ i)
  have hR : R = 0 := by
    ext k i
    have h := hdiag i
    rw [CStarMatrix.mul_apply] at h
    have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ ?_).1 h k (Finset.mem_univ k)
    · simpa [CStarMatrix.star_apply] using this
    · simp [CStarMatrix.star_apply]
  rw [hR, mul_zero]

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] in
/-- **Block additivity**: `τ_{n ⊕ m}([[x, b], [c, y]]) = τ_n(x) + τ_m(y)`; in particular
`τ_{n ⊕ m}(diag(x, y)) = τ_n(x) + τ_m(y)`. -/
theorem matrixTrace_fromBlocks (x : CStarMatrix n n B) (b : CStarMatrix n m B)
    (c : CStarMatrix m n B) (y : CStarMatrix m m B) :
    matrixTrace τ (n ⊕ m)
        (CStarMatrix.ofMatrix (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm x)
          (CStarMatrix.ofMatrix.symm b) (CStarMatrix.ofMatrix.symm c)
          (CStarMatrix.ofMatrix.symm y))) =
      matrixTrace τ n x + matrixTrace τ m y := by
  simp [matrixTrace_apply, Fintype.sum_sum_type, CStarMatrix.ofMatrix_apply,
    CStarMatrix.ofMatrix_symm_apply]

end TauCeti
