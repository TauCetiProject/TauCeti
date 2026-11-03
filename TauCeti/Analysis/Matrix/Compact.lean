/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.Matrix.Spectrum

/-!
# Positive matrices in compact matrix groups

A positive semidefinite matrix whose natural powers have bounded real trace has all its
eigenvalues at most one, hence is at most the identity. Applied to an element and its inverse
in a compact subgroup of the general linear group, this shows that a positive matrix in that
subgroup is the identity. No invariance under unitary conjugation is required of the subgroup.

This is the trace-growth obstruction used in direct maximal-compactness proofs: after a polar
factorization puts the positive factor in a compact subgroup, that factor must disappear.
Both real and complex matrices, and the empty index type, are included.

## Main results

* `Matrix.PosSemidef.le_one_of_bddAbove_range_re_trace_pow`: bounded traces of natural powers
  force a positive semidefinite matrix to be at most the identity.
* `Matrix.PosSemidef.eq_one_of_mem_isCompact_subgroup`: the identity is the only positive
  semidefinite element of a compact subgroup of the general linear group.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Section 2.5
  (polar decomposition and compact matrix groups).
-/

public section

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- If the real traces of the natural powers of a positive semidefinite matrix are bounded
above, the matrix is at most the identity. -/
theorem PosSemidef.le_one_of_bddAbove_range_re_trace_pow {A : Matrix n n 𝕜}
    (hA : A.PosSemidef)
    (hbounded : BddAbove (Set.range fun k : ℕ ↦ RCLike.re (A ^ k).trace)) : A ≤ 1 := by
  obtain ⟨C, hC⟩ := hbounded
  have heigen (i : n) : hA.isHermitian.eigenvalues i ≤ 1 := by
    by_contra! hi
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hi
    have htrace : RCLike.re (A ^ k).trace = ∑ j, hA.isHermitian.eigenvalues j ^ k := by
      rw [hA.isHermitian.trace_pow_eq_sum_eigenvalues_pow]
      simp only [map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    have hle : hA.isHermitian.eigenvalues i ^ k ≤ RCLike.re (A ^ k).trace := by
      rw [htrace]
      exact Finset.single_le_sum (fun j _ ↦ pow_nonneg (hA.eigenvalues_nonneg j) k)
        (Finset.mem_univ i)
    exact (not_lt_of_ge (hle.trans (hC (Set.mem_range_self k)))) hk
  refine CFC.le_one (R := ℝ) (fun x hx ↦ ?_) hA.isHermitian
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact heigen i

/-- The identity is the only positive semidefinite element of a compact subgroup of `GL n 𝕜`.
In particular, this applies to a positive polar factor once it belongs to the subgroup. -/
theorem PosSemidef.eq_one_of_mem_isCompact_subgroup {A : GL n 𝕜}
    (hA : (A : Matrix n n 𝕜).PosSemidef) {K : Subgroup (GL n 𝕜)}
    (hK : IsCompact (K : Set (GL n 𝕜))) (hmem : A ∈ K) : A = 1 := by
  have hcont : Continuous fun B : GL n 𝕜 ↦ RCLike.re (B : Matrix n n 𝕜).trace := by
    exact RCLike.continuous_re.comp
      (Units.continuous_val (M := Matrix n n 𝕜)).matrix_trace
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont.continuousOn
  have hbounded (B : GL n 𝕜) (hB : B ∈ K) :
      BddAbove (Set.range fun k : ℕ ↦ RCLike.re ((B : Matrix n n 𝕜) ^ k).trace) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨k, rfl⟩
    simpa only [Units.val_pow_eq_pow_val] using hC (Set.mem_image_of_mem _ (K.pow_mem hB k))
  apply Units.ext
  refine le_antisymm (hA.le_one_of_bddAbove_range_re_trace_pow (hbounded A hmem)) ?_
  have hAinv : (↑A⁻¹ : Matrix n n 𝕜).PosSemidef := by
    rw [GeneralLinearGroup.coe_inv]
    exact hA.inv
  have hle : (↑A⁻¹ : Matrix n n 𝕜) ≤ 1 :=
    hAinv.le_one_of_bddAbove_range_re_trace_pow (hbounded A⁻¹ (K.inv_mem hmem))
  -- Conjugating `1 - A⁻¹ ≥ 0` by `√A` gives `A - 1 ≥ 0`.
  let S := CFC.sqrt (A : Matrix n n 𝕜)
  have hS : S.PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A : Matrix n n 𝕜))
  have hSsq : S * S = (A : Matrix n n 𝕜) := CFC.sqrt_mul_sqrt_self _ hA.nonneg
  have hSunit : IsUnit S := isUnit_mul_self_iff.mp (hSsq.symm ▸ A.isUnit)
  have hsandwich : S * (↑A⁻¹ : Matrix n n 𝕜) * S = 1 := by
    apply hSunit.mul_right_cancel
    calc
      (S * ↑A⁻¹ * S) * S = S * (↑A⁻¹ * (S * S)) := by noncomm_ring
      _ = 1 * S := by rw [hSsq, A.inv_mul, mul_one, one_mul]
  have hpos := (Matrix.le_iff.mp hle).conjTranspose_mul_mul_same S
  rwa [hS.isHermitian.eq, mul_sub, sub_mul, mul_one, hSsq, hsandwich,
    ← Matrix.le_iff] at hpos

end Matrix
