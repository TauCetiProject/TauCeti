/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef.Determinant

import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.Matrix.GramFactorization

/-!
# Covolume bounds for complex families in rational coordinates

A rational metric on a coordinate space lets us form a Gram determinant after applying any
field automorphism of `ℂ` to the columns. `Matrix.CovolumeLE` bounds the *squared* covolume
uniformly under these coordinate twists. Pointwise bounds on the columns give an initial
covolume bound and allow a family to be enlarged. For arithmetic applications, this bound
also controls the conjugates of the original Gram determinant, even though the field
automorphism need not commute with complex conjugation.

## References

The normalization and the conjugated-pairing argument follow `New.TwistedLattice.CovolumeLe` and
`New.TwistedLattice.CovolumeLe.norm_map_det_gram_le` in `New/Reduction/Lattices/TwistedLattice.lean`
of [grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open scoped ComplexOrder

namespace Matrix

variable {m n p : Type*} [Fintype m] [Fintype n] [DecidableEq n]
  {G : Matrix m m ℚ} {A : Matrix m n ℂ} {c : ℝ}

/-- `A.CovolumeLE G c` means that the Gram determinant of the columns of `A`, with rational
metric `G`, has norm at most `exp c` after every field automorphism of the coordinates. -/
def CovolumeLE (A : Matrix m n ℂ) (G : Matrix m m ℚ) (c : ℝ) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, ‖((A.map σ)ᴴ * G.map (algebraMap ℚ ℂ) * A.map σ).det‖ ≤ Real.exp c

/-- A covolume bound is the uniform bound on the Gram determinants of the twisted columns. -/
theorem covolumeLE_iff : A.CovolumeLE G c ↔
    ∀ σ : ℂ ≃+* ℂ, ‖((A.map σ)ᴴ * G.map (algebraMap ℚ ℂ) * A.map σ).det‖ ≤ Real.exp c :=
  (Iff.rfl)

/-- A covolume bound remains valid when the budget increases. -/
theorem CovolumeLE.mono (hA : A.CovolumeLE G c) {d : ℝ} (hcd : c ≤ d) : A.CovolumeLE G d :=
  covolumeLE_iff.mpr fun σ ↦ (covolumeLE_iff.mp hA σ).trans (Real.exp_le_exp.mpr hcd)

/-- If each twisted column has squared length at most `exp (b i)`, then the logarithmic
bound on the squared covolume is the sum of the individual budgets. -/
theorem covolumeLE_sum_of_forall_norm_diag_le
    (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef) {b : n → ℝ}
    (hA : ∀ (σ : ℂ ≃+* ℂ) i,
      ‖((A.map σ)ᴴ * G.map (algebraMap ℚ ℂ) * A.map σ) i i‖ ≤ Real.exp (b i)) :
    A.CovolumeLE G (∑ i, b i) := by
  refine covolumeLE_iff.mpr fun σ ↦ ?_
  obtain ⟨X, hX⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp
    (hG.conjTranspose_mul_mul_same (A.map σ))
  let v : n → EuclideanSpace ℂ n := fun j ↦ WithLp.toLp 2 (fun i ↦ X i j)
  have hv : gram ℂ v = (A.map σ)ᴴ * G.map (algebraMap ℚ ℂ) * A.map σ := by
    rw [hX]
    ext i j
    simp [v, gram_apply, EuclideanSpace.inner_toLp_toLp, Matrix.mul_apply, dotProduct, mul_comm]
  have hdiag (i : n) : ‖v i‖ ^ 2 ≤ Real.exp (b i) := by
    simpa only [← hv, gram_apply, inner_self_eq_norm_sq_to_K, norm_pow,
      RCLike.norm_of_nonneg (norm_nonneg _)] using hA σ i
  rw [← hv, Real.exp_sum, ← ofReal_re_det_gram v, RCLike.norm_of_nonneg (re_det_gram_nonneg v)]
  exact (re_det_gram_le_prod_norm_sq v).trans
    (Finset.prod_le_prod₀ (fun i _ ↦ sq_nonneg (‖v i‖)) (fun i _ ↦ hdiag i))

/-- Logarithmic covolume bounds add when concatenating columns in the same metric. -/
theorem CovolumeLE.fromCols [Fintype p] [DecidableEq p] {B : Matrix m p ℂ} {d : ℝ}
    (hA : A.CovolumeLE G c) (hB : B.CovolumeLE G d)
    (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef) : (fromCols A B).CovolumeLE G (c + d) := by
  refine covolumeLE_iff.mpr fun σ ↦ ?_
  rw [fromCols_map, Real.exp_add]
  exact (hG.norm_det_conjTranspose_fromCols_mul_mul_fromCols_le _ _).trans
    (mul_le_mul (covolumeLE_iff.mp hA σ) (covolumeLE_iff.mp hB σ)
      (norm_nonneg _) (Real.exp_nonneg _))

/-- The covolume bound controls every field conjugate of the original Gram determinant.
The two factors of the Gram pairing transform by `σ` and by `conj ∘ σ ∘ conj`, respectively. -/
theorem CovolumeLE.norm_map_det_conjTranspose_mul_mul_le (hA : A.CovolumeLE G c)
    (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef) (σ : ℂ ≃+* ℂ) :
    ‖σ (Aᴴ * G.map (algebraMap ℚ ℂ) * A).det‖ ≤ Real.exp c := by
  let τ : ℂ ≃+* ℂ := ((starRingAut : ℂ ≃+* ℂ).trans σ).trans starRingAut
  have hτ : Aᴴ.map σ = (A.map τ)ᴴ := by
    ext i j
    simp [τ, conjTranspose_apply]
  have hfix : (G.map (algebraMap ℚ ℂ)).map σ = G.map (algebraMap ℚ ℂ) := by
    ext i j
    simp
  have hmap : σ (Aᴴ * G.map (algebraMap ℚ ℂ) * A).det =
      ((A.map τ)ᴴ * G.map (algebraMap ℚ ℂ) * A.map σ).det := by
    simp only [σ.map_det, RingEquiv.mapMatrix_apply, Matrix.map_mul, hτ, hfix]
  rw [hmap, ← sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)]
  calc
    _ ≤ ‖((A.map τ)ᴴ * G.map (algebraMap ℚ ℂ) * A.map τ).det‖ *
        ‖((A.map σ)ᴴ * G.map (algebraMap ℚ ℂ) * A.map σ).det‖ :=
      hG.norm_det_conjTranspose_mul_mul_sq_le _ _
    _ ≤ Real.exp c * Real.exp c :=
      mul_le_mul (covolumeLE_iff.mp hA τ) (covolumeLE_iff.mp hA σ)
        (norm_nonneg _) (Real.exp_nonneg _)
    _ = (Real.exp c) ^ 2 := (sq _).symm

end Matrix
