/-
Copyright (c) 2026 Tau Ceti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Row-vector congruence lifting and discriminant-index weight splitting

This file provides two elementary tools used when counting linear forms vanishing on a sublattice
of given corank:

* `TauCeti.mem_smul_pi_subring_iff`: for a unit `d : Rˣ` and a subring `O : Subring R`, a vector
  `v : ι → R` lies in `d • O^ι` iff `d⁻¹ • v` has entries in `O`.
* `TauCeti.sub_mem_smul_pi_subring_of_values`: if `U : GL π R` has `U⁻¹` with entries in `O`,
  `e : Fin r ⊕ Fin l ≃ π` splits the columns of `U`, and `A : GL (Fin r) R`, then two row vectors
  `v, w : π → R` are congruent modulo `d • O^π` whenever their values on the last `l` columns of
  `U` are congruent modulo `d • O^l` and their values on `(first r columns of U) * A`, divided by
  `d`, differ by an `O`-linear combination of the rows of `A`.
* `TauCeti.mul_inv_pow_le_of_mul_le`: the weight-splitting bound
  `i * ((d * i) ^ k)⁻¹ ≤ H ^ (μ + 2) * ((d ^ (k + 1))⁻¹ * i⁻¹ ^ (r + μ))` for `1 ≤ d`, `1 ≤ i`,
  `d * i ≤ H`, and `r ≤ k`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/Spanning/RemainingTerms/LatticesOfCorank.lean`, declarations
`New.Filling.mem_smul_intVectors_iff`, `New.Filling.sub_mem_smul_intVectors_of_values`, and
`New.Filling.mul_inv_pow_le_of_mul_le`, generalized from `Ô E ⊆ 𝔸f E` to an arbitrary subring
`O : Subring R` of a commutative ring `R`.
-/

@[expose] public section

namespace TauCeti

open Matrix
open scoped Pointwise

/-- A vector `v : ι → R` lies in `d • O^ι` for a unit `d : Rˣ` iff `d⁻¹ • v` has all entries in
the subring `O`. -/
theorem mem_smul_pi_subring_iff {R ι : Type*} [CommRing R] {O : Subring R} {d : Rˣ} {v : ι → R} :
    v ∈ d • {w : ι → R | ∀ i, w i ∈ O} ↔ ∀ i, (d⁻¹ • v) i ∈ O := by
  refine ⟨?_, fun hv ↦ ⟨d⁻¹ • v, hv, smul_inv_smul d v⟩⟩
  rintro ⟨w, hw, rfl⟩
  simpa [Units.smul_def, ← mul_assoc] using hw

/-- Let `U : GL π R` have inverse with entries in a subring `O`, let `e : Fin r ⊕ Fin l ≃ π` split
the columns of `U`, and let `A : GL (Fin r) R`. Two row vectors `v, w : π → R` satisfy
`v - w ∈ d • O^π` whenever their values on the last `l` columns of `U` are congruent modulo `d O`
and their values on `(first r columns of U) * A`, scaled by `d⁻¹`, differ by `Aᵀ *ᵥ s` with
`s ∈ O^r`. -/
theorem sub_mem_smul_pi_subring_of_values {R π : Type*} [CommRing R] [Fintype π] [DecidableEq π]
    {r l : ℕ} {O : Subring R} {e : Fin r ⊕ Fin l ≃ π} {U : GL π R}
    (hU_inv : ∀ i j, (U⁻¹ : Matrix π π R) i j ∈ O) {A : GL (Fin r) R} {d : Rˣ} {v w : π → R}
    (h_rows : ∃ s : Fin r → R, (∀ i, s i ∈ O) ∧
      A.valᵀ *ᵥ s = d⁻¹ • v ᵥ* (U.val.submatrix id (e ∘ Sum.inl) * A.val) -
        d⁻¹ • w ᵥ* (U.val.submatrix id (e ∘ Sum.inl) * A.val))
    (h_rest : (fun i : Fin l ↦ (v ᵥ* U.val) (e (.inr i)) - (w ᵥ* U.val) (e (.inr i))) ∈
      d • {u : Fin l → R | ∀ i, u i ∈ O}) :
    v - w ∈ d • {u : π → R | ∀ i, u i ∈ O} := by
  obtain ⟨s, hs_int, hs⟩ := h_rows
  let z : π → R := d⁻¹ • (v - w)
  have h_first : z ᵥ* U.val.submatrix id (e ∘ Sum.inl) = s := by
    have h_mul : (z ᵥ* U.val.submatrix id (e ∘ Sum.inl)) ᵥ* A.val = s ᵥ* A.val := by
      rw [← mulVec_transpose A.val s, hs, vecMul_vecMul, smul_vecMul, sub_vecMul, smul_sub]
    have h_inv := congrArg (· ᵥ* (A⁻¹ : Matrix (Fin r) (Fin r) R)) h_mul
    simpa [vecMul_vecMul] using h_inv
  have h_values : ∀ p : π, (z ᵥ* U.val) p ∈ O := by
    intro p
    obtain ⟨i | i, rfl⟩ := e.surjective p
    · have h_eq : (z ᵥ* U.val) (e (.inl i)) = (z ᵥ* U.val.submatrix id (e ∘ Sum.inl)) i := rfl
      rw [h_eq, h_first]
      exact hs_int i
    · simpa only [z, smul_vecMul, sub_vecMul, Pi.smul_apply, Pi.sub_apply] using
        mem_smul_pi_subring_iff.mp h_rest i
  refine mem_smul_pi_subring_iff.mpr fun p ↦ ?_
  have h_rec : z = (z ᵥ* U.val) ᵥ* (U⁻¹ : Matrix π π R) := by simp [vecMul_vecMul]
  change z p ∈ O
  rw [h_rec]
  exact sum_mem fun q _ ↦ mul_mem (h_values q) (hU_inv q p)

/-- Let `d, i ≥ 1` be real numbers with `d * i ≤ H`, and let `r ≤ k`. Then `i * ((d * i) ^ k)⁻¹`
is at most `H ^ (μ + 2) * ((d ^ (k + 1))⁻¹ * i⁻¹ ^ (r + μ))` for every `μ : ℕ`. -/
theorem mul_inv_pow_le_of_mul_le {d i H : ℝ} (hd : 1 ≤ d) (hi : 1 ≤ i) (hH : d * i ≤ H)
    {r k : ℕ} (hr : r ≤ k) (μ : ℕ) :
    i * ((d * i) ^ k)⁻¹ ≤ H ^ (μ + 2) * ((d ^ (k + 1))⁻¹ * i⁻¹ ^ (r + μ)) := by
  have hi_le : i ≤ H := (le_mul_of_one_le_left (by positivity) hd).trans hH
  have hH_pos : 0 < H := by linarith
  calc i * ((d * i) ^ k)⁻¹
      = i * (d * i) ^ (μ + 1) * (d ^ (k + μ + 1) * i ^ (k + μ + 1))⁻¹ := by
        field_simp; ring
    _ ≤ H * H ^ (μ + 1) * (d ^ (k + 1) * i ^ (r + μ))⁻¹ := by
        have hd_pow : d ^ (k + 1) ≤ d ^ (k + μ + 1) := pow_le_pow_right₀ hd (by omega)
        have hi_pow : i ^ (r + μ) ≤ i ^ (k + μ + 1) := pow_le_pow_right₀ hi (by omega)
        gcongr
    _ = H ^ (μ + 2) * ((d ^ (k + 1))⁻¹ * i⁻¹ ^ (r + μ)) := by
        rw [mul_inv, inv_pow]; ring

end TauCeti
