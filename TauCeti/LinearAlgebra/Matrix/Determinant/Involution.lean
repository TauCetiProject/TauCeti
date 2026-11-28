/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Determinants of involutive matrices

A square matrix `M` with `M * M = 1` (an involution) over a commutative ring `R` without zero
divisors has determinant `1` or `-1`. In size two, Cayley–Hamilton reads
`trace M • M = (1 + det M) • 1` for an involution, and this pins down the two cases when `2 ≠ 0`
in `R`: the involutions of determinant one are the scalars `1` and `-1`, while those of
determinant `-1` are traceless, so they have characteristic polynomial `X ^ 2 - 1`.

These facts decide the *oddness* of a rank-two Galois representation `ρ` at a complex conjugation
`c`, that is, whether `det ρ(c) = -1`. Let `f : R →+* k` be the reduction map of a coefficient
ring `R` without zero divisors in which `2 ≠ 0`, such as the ring of integers of a `p`-adic field.

* If `2 ≠ 0` in `k` (odd residue characteristic), then `1 ≠ -1` in `k`, so the determinant of
  `ρ(c)` is read off from the reduction: `ρ` is odd at `c` exactly when its reduction is.
* If `2 = 0` in `k`, the determinant of every residual involution over a ring without zero divisors
  is `1 = -1`, so residual oddness carries no information. Instead, `ρ(c) = ± 1` are the only even
  involutions and both reduce to `1`, so `ρ` is odd at `c` as soon as `ρ(c)` does not reduce to `1`.
  The converse fails: `diag(1, -1)` is odd and reduces to `1` modulo `2`.

The hypothesis that `R` has no zero divisors cannot be dropped: over `ℤ × ℤ`, the involution
`diag((1, 1), (-1, 1))` has determinant `(-1, 1) ≠ -1`, although its image under the first
projection has determinant `-1`.

## Main results

* `Matrix.det_eq_one_or_neg_one_of_mul_self_eq_one`: an involution has determinant `± 1`.
* `Matrix.det_map_eq_neg_one_iff_of_mul_self_eq_one`: if `2 ≠ 0` in `k`, an involution has
  determinant `-1` exactly when its image under `f : R →+* k` does.
* `Matrix.det_eq_neg_one_of_mul_self_eq_one_of_two_eq_zero`: if `2 = 0` in `R`, every involution
  has determinant `-1`.
* `Matrix.trace_eq_zero_of_mul_self_eq_one_of_det_eq_neg_one_fin_two`,
  `Matrix.charpoly_eq_X_sq_sub_one_iff_of_mul_self_eq_one_fin_two`: an involution in size two has
  determinant `-1` exactly when its characteristic polynomial is `X ^ 2 - 1`, and is then
  traceless.
* `Matrix.det_eq_one_iff_of_mul_self_eq_one_fin_two`,
  `Matrix.det_eq_neg_one_iff_of_mul_self_eq_one_fin_two`: if `2 ≠ 0` in `R`, an involution in size
  two has determinant one exactly when it is `± 1`.
* `Matrix.det_eq_neg_one_of_mul_self_eq_one_of_map_ne_one_fin_two`: if `2 = 0` in `k`, an
  involution in size two whose image under `f : R →+* k` is not `1` has determinant `-1`.

## References

* C. Khare, J.-P. Wintenberger, *Serre's modularity conjecture (II)*, Invent. Math. 178 (2009),
  §3.1, Proposition 3.3 and the remark after its proof.
* S.-N. Tung, *On the automorphy of 2-dimensional potentially semi-stable deformation rings of
  `G_{ℚ_p}`*, arXiv:1803.07451v4, Theorem 4.7 (1) (oddness of a lift at odd `p`).
-/

public section

open Polynomial

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- An involution over a ring without zero divisors has determinant `1` or `-1`. -/
theorem det_eq_one_or_neg_one_of_mul_self_eq_one [NoZeroDivisors R] {M : Matrix n n R}
    (hM : M * M = 1) : M.det = 1 ∨ M.det = -1 :=
  mul_self_eq_one_iff.mp <| by rw [← det_mul, hM, det_one]

/-- **Oddness of a lift in odd residue characteristic.** Let `M` be an involution over a ring
without zero divisors and `f : R →+* k` a ring homomorphism with `2 ≠ 0` in `k`. Then `M` has
determinant `-1` exactly when its image under `f` does. -/
theorem det_map_eq_neg_one_iff_of_mul_self_eq_one [NoZeroDivisors R] {k : Type*} [CommRing k]
    {M : Matrix n n R} (hM : M * M = 1) (f : R →+* k) (h2 : (2 : k) ≠ 0) :
    (M.map f).det = -1 ↔ M.det = -1 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  refine ⟨fun h ↦ (det_eq_one_or_neg_one_of_mul_self_eq_one hM).resolve_left fun h1 ↦ h2 ?_,
    fun h ↦ by rw [h, map_neg, map_one]⟩
  rw [h1, map_one, eq_comm, neg_eq_iff_add_eq_zero, one_add_one_eq_two] at h
  exact h

/-- In characteristic two, every involution over a ring without zero divisors has determinant
`-1`, which is also `1`: the condition `det M = -1` carries no information there. -/
theorem det_eq_neg_one_of_mul_self_eq_one_of_two_eq_zero [NoZeroDivisors R] {M : Matrix n n R}
    (hM : M * M = 1) (h2 : (2 : R) = 0) : M.det = -1 := by
  have h : (-1 : R) = 1 := neg_eq_iff_add_eq_zero.mpr (by rw [one_add_one_eq_two, h2])
  rcases det_eq_one_or_neg_one_of_mul_self_eq_one hM with h1 | h1 <;> rw [h1]
  exact h.symm

section FinTwo

variable {M : Matrix (Fin 2) (Fin 2) R}

/-- **Cayley–Hamilton for an involution in size two**: `trace M • M = (1 + det M) • 1`. -/
theorem trace_smul_eq_one_add_det_smul_of_mul_self_eq_one_fin_two (hM : M * M = 1) :
    M.trace • M = (1 + M.det) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  have h := sq_eq_trace_smul_sub_det_smul_one_fin_two M
  rw [sq, hM, eq_sub_iff_add_eq] at h
  rw [add_smul, one_smul, h]

/-- An involution of determinant `-1` in size two is traceless. -/
theorem trace_eq_zero_of_mul_self_eq_one_of_det_eq_neg_one_fin_two (hM : M * M = 1)
    (hdet : M.det = -1) : M.trace = 0 := by
  have h := congrArg (· * M) (trace_smul_eq_one_add_det_smul_of_mul_self_eq_one_fin_two hM)
  simp only [hdet, add_neg_cancel, zero_smul, zero_mul, smul_mul_assoc, hM] at h
  simpa using congrFun (congrFun h 0) 0

/-- An involution in size two has characteristic polynomial `X ^ 2 - 1` exactly when its
determinant is `-1`. -/
theorem charpoly_eq_X_sq_sub_one_iff_of_mul_self_eq_one_fin_two (hM : M * M = 1) :
    M.charpoly = X ^ 2 - 1 ↔ M.det = -1 := by
  refine ⟨fun h ↦ by simp [det_eq_sign_charpoly_coeff, h], fun h ↦ ?_⟩
  nontriviality R
  rw [charpoly_fin_two, trace_eq_zero_of_mul_self_eq_one_of_det_eq_neg_one_fin_two hM h, h]
  simp [sub_eq_add_neg]

/-- Over a ring without zero divisors in which `2 ≠ 0`, an involution in size two has
determinant one exactly when it is `1` or `-1`. -/
theorem det_eq_one_iff_of_mul_self_eq_one_fin_two [NoZeroDivisors R] (hM : M * M = 1)
    (h2 : (2 : R) ≠ 0) : M.det = 1 ↔ M = 1 ∨ M = -1 := by
  refine ⟨fun hdet ↦ ?_, by rintro (rfl | rfl) <;> simp [det_neg]⟩
  have h := trace_smul_eq_one_add_det_smul_of_mul_self_eq_one_fin_two hM
  rw [hdet, one_add_one_eq_two] at h
  -- Taking traces gives `trace M ^ 2 = 4`, so `trace M = ± 2` and `2 • M = ± 2 • 1`.
  have htr : M.trace * M.trace = 2 * 2 := by
    simpa [trace_smul, trace_one] using congrArg trace h
  have hcancel : ∀ N : Matrix (Fin 2) (Fin 2) R, (2 : R) • M = (2 : R) • N → M = N :=
    fun N hN ↦ smul_right_injective _ h2 hN
  rcases mul_self_eq_mul_self_iff.mp htr with ht | ht
  · exact .inl (hcancel 1 (by rw [← h, ht]))
  · exact .inr (hcancel (-1) (by rw [smul_neg, ← h, ht, neg_smul, neg_neg]))

/-- Over a ring without zero divisors in which `2 ≠ 0`, an involution in size two has
determinant `-1` exactly when it is neither `1` nor `-1`. -/
theorem det_eq_neg_one_iff_of_mul_self_eq_one_fin_two [NoZeroDivisors R] (hM : M * M = 1)
    (h2 : (2 : R) ≠ 0) : M.det = -1 ↔ M ≠ 1 ∧ M ≠ -1 := by
  have h : (-1 : R) ≠ 1 := fun h ↦ h2 <| by rwa [neg_eq_iff_add_eq_zero, one_add_one_eq_two] at h
  rw [← not_or, ← det_eq_one_iff_of_mul_self_eq_one_fin_two hM h2]
  rcases det_eq_one_or_neg_one_of_mul_self_eq_one hM with h1 | h1 <;> simp [h1, h, h.symm]

/-- **Oddness in residue characteristic two.** Let `M` be an involution in size two over a ring
without zero divisors, and `f : R →+* k` a ring homomorphism with `2 = 0` in `k`. If the image of
`M` under `f` is not `1`, then `M` has determinant `-1`. When `2 ≠ 0` in `R`, this is because the
even involutions `± 1` both map to `1`; when `2 = 0` in `R`, every involution has determinant
`-1`. -/
theorem det_eq_neg_one_of_mul_self_eq_one_of_map_ne_one_fin_two [NoZeroDivisors R] {k : Type*}
    [CommRing k] (hM : M * M = 1) (f : R →+* k) (hk : (2 : k) = 0) (h : M.map f ≠ 1) :
    M.det = -1 := by
  rcases eq_or_ne (2 : R) 0 with h2 | h2
  · exact det_eq_neg_one_of_mul_self_eq_one_of_two_eq_zero hM h2
  have hneg : (-1 : k) = 1 := neg_eq_iff_add_eq_zero.mpr (by rw [one_add_one_eq_two, hk])
  rw [det_eq_neg_one_iff_of_mul_self_eq_one_fin_two hM h2]
  refine ⟨fun h1 ↦ h ?_, fun h1 ↦ h ?_⟩ <;> rw [← RingHom.mapMatrix_apply, h1]
  · exact map_one _
  · rw [map_neg, map_one, ← neg_one_smul k, hneg, one_smul]

end FinTwo

end Matrix
