/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Rescaling roots to make coefficients small

Over a normed algebra `R` over a nontrivially normed field `K`, rescaling the roots of a
polynomial by a small nonzero scalar makes every coefficient below the degree have norm at most
one. For a monic polynomial over a ring with a Gauss norm, this makes the rescaled polynomial
distinguished at the unit radius, which is how a root of a monic polynomial is presented by
Weierstrass division in Tate and Monsky–Washnitzer algebras.

## Main results

* `Polynomial.exists_norm_coeff_scaleRoots_le_one`: there is a nonzero `c : K` such that all
  coefficients of `P.scaleRoots (algebraMap K R c)` below the degree have norm at most one.
-/

public section

namespace Polynomial

variable {K R : Type*} [NontriviallyNormedField K] [SeminormedRing R] [NormedAlgebra K R]

/-- Rescaling the roots of a polynomial by a small nonzero scalar makes all of its coefficients
below the degree have norm at most one. -/
theorem exists_norm_coeff_scaleRoots_le_one (P : R[X]) :
    ∃ c : K, c ≠ 0 ∧ ∀ k < P.natDegree,
      ‖(P.scaleRoots (algebraMap K R c)).coeff k‖ ≤ 1 := by
  set M := 1 + ∑ k ∈ Finset.range P.natDegree, ‖P.coeff k‖
  have hM : 0 < M := by positivity
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt K (inv_pos.mpr hM)
  refine ⟨c, norm_pos_iff.mp hc0, fun k hk ↦ ?_⟩
  have hk' : ‖P.coeff k‖ ≤ M := by
    have := Finset.single_le_sum (f := fun k ↦ ‖P.coeff k‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_range.mpr hk)
    linarith
  have hc1 : ‖c‖ ≤ 1 := hc.le.trans (inv_le_one_of_one_le₀ (by
    simp only [M, le_add_iff_nonneg_right]; positivity))
  rw [coeff_scaleRoots, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, norm_smul, norm_pow]
  calc ‖c‖ ^ (P.natDegree - k) * ‖P.coeff k‖
      ≤ ‖c‖ * M :=
        mul_le_mul (pow_le_of_le_one (norm_nonneg c) hc1 (by omega)) hk' (norm_nonneg _)
          (norm_nonneg c)
    _ ≤ M⁻¹ * M := by gcongr
    _ = 1 := inv_mul_cancel₀ hM.ne'

end Polynomial
