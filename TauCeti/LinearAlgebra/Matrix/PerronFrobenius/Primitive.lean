/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import TauCeti.Data.Matrix.Mul
public import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Positive

/-!
# The Perron–Frobenius theorem for primitive matrices

A square real matrix `A` is primitive (`Matrix.IsPrimitive`) when its entries are nonnegative and
some power `A ^ k` with `k > 0` is strictly positive. Every later power is then strictly positive
too (`Matrix.pow_apply_pos_of_le`). A primitive matrix is irreducible
(`Matrix.IsPrimitive.isIrreducible`), so the theorem for irreducible matrices applies: it has a
Perron root `r > 0` with an eigenvector `v` whose entries are strictly positive
(`Matrix.IsIrreducible.exists_mulVec_eq_smul`), `r` is its spectral radius
(`Matrix.spectralRadius_eq_of_mulVec_eq_smul`), and `r` is a simple root of the characteristic
polynomial (`Matrix.IsIrreducible.rootMultiplicity_charpoly_eq_one`).

What primitivity adds is that `r` **strictly dominates** every other complex eigenvalue: if
`A z = μ z` for a nonzero complex vector `z` and `μ ≠ r`, then `‖μ‖ < r`. This fails for
irreducible matrices in general: the permutation matrix of a cycle of length `p` is irreducible,
with Perron root `1`, and all `p`-th roots of unity are eigenvalues. The proof applies the
strictly positive case, `Matrix.eq_of_norm_eq_of_mulVec_eq_smul`, to the strictly positive
matrices `A ^ k` and `A ^ (k + 1)`: an eigenvalue `μ` of modulus `r` has `μ ^ k = r ^ k` and
`μ ^ (k + 1) = r ^ (k + 1)`, hence `μ = r`.

## Main results

* `Matrix.IsPrimitive.eq_of_norm_eq_of_mulVec_eq_smul`: the Perron root of a primitive matrix is
  its only complex eigenvalue of maximal modulus.
* `Matrix.IsPrimitive.norm_lt_of_mulVec_eq_smul` and `Matrix.IsPrimitive.norm_lt_of_mem_spectrum`:
  every other complex eigenvalue of a primitive matrix has modulus strictly less than its
  Perron root.

## References

* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer (2006), Chapter 1 (primitive
  matrices, Theorem 1.1).
-/

public section

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Real

variable {A : Matrix n n ℝ} {v : n → ℝ} {r : ℝ} {μ : ℂ}

/-- **Perron–Frobenius**: if `A v = r v` for a primitive real matrix `A` and a vector `v` with
strictly positive entries, then `r` is the only complex eigenvalue of `A` of modulus `r`. -/
theorem IsPrimitive.eq_of_norm_eq_of_mulVec_eq_smul (hA : A.IsPrimitive) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) {z : n → ℂ} (hz : z ≠ 0) (hAz : A.map (↑) *ᵥ z = μ • z)
    (hμ : ‖μ‖ = r) : μ = r := by
  obtain ⟨k, hk, hAk⟩ := hA.exists_pos_pow
  -- For `m ≥ k`, `μ ^ m` is an eigenvalue of modulus `r ^ m` of the strictly positive `A ^ m`.
  have hpow : ∀ m, k ≤ m → μ ^ m = (r : ℂ) ^ m := fun m hm => by
    have hmap : (A ^ m).map (↑) = A.map ((↑) : ℝ → ℂ) ^ m := by
      rw [← funext Complex.ofRealHom_eq_coe]
      exact Matrix.map_pow A Complex.ofRealHom m
    exact_mod_cast Matrix.eq_of_norm_eq_of_mulVec_eq_smul
      (pow_apply_pos_of_le hA.nonneg hk hAk hm) hv (pow_mulVec_eq_pow_smul hAv m) hz
      (hmap ▸ pow_mulVec_eq_pow_smul hAz m) (by rw [norm_pow, hμ])
  rcases eq_or_ne (r : ℂ) 0 with hr | hr
  · rw [hr, ← norm_eq_zero, hμ]
    exact_mod_cast hr
  · have h := hpow (k + 1) k.le_succ
    rw [pow_succ, pow_succ, hpow k le_rfl] at h
    exact mul_left_cancel₀ (pow_ne_zero k hr) h

/-- **Perron–Frobenius**: if `A v = r v` for a primitive real matrix `A` and a vector `v` with
strictly positive entries, then every complex eigenvalue `μ ≠ r` of `A` has `‖μ‖ < r`. -/
theorem IsPrimitive.norm_lt_of_mulVec_eq_smul (hA : A.IsPrimitive) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) {z : n → ℂ} (hz : z ≠ 0) (hAz : A.map (↑) *ᵥ z = μ • z)
    (hμ : μ ≠ r) : ‖μ‖ < r :=
  (norm_le_of_mulVec_le_smul hA.nonneg hv hAv.le hz hAz).lt_of_ne
    fun h => hμ (hA.eq_of_norm_eq_of_mulVec_eq_smul hv hAv hz hAz h)

/-- **Perron–Frobenius**: if `A v = r v` for a primitive real matrix `A` and a vector `v` with
strictly positive entries, then every point `μ ≠ r` of the spectrum of `A`, viewed as a complex
matrix, has `‖μ‖ < r`. -/
theorem IsPrimitive.norm_lt_of_mem_spectrum (hA : A.IsPrimitive) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = r • v) (hμ : μ ∈ spectrum ℂ (A.map (↑) : Matrix n n ℂ)) (hμr : μ ≠ r) :
    ‖μ‖ < r := by
  obtain ⟨z, hz, hAz⟩ := mem_spectrum_iff_exists_mulVec_eq_smul.1 hμ
  exact hA.norm_lt_of_mulVec_eq_smul hv hAv hz hAz hμr

end Real

end Matrix
