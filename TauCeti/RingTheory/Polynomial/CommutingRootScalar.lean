/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Vandermonde cancellation and scalar action on `T - 1` for commuting algebra elements

This file proves a module-valued Vandermonde linear independence criterion over a field and uses it
to deduce that a commuting element `F` acts as a scalar `α 0` on the image of `T - 1` from a family
of annihilating polynomials for `F * T ^ b`.

## Main results

* `TauCeti.eq_zero_of_forall_sum_pow_smul_eq_zero`: if `r : Fin n → k` is injective and
  `∑ i, r b ^ i • v i = 0` in a `k`-module `M` for all `b : Fin n`, then `v i = 0` for all `i`.
* `TauCeti.mul_sub_one_eq_smul_sub_one`: if `F` and `T` commute in a `k`-algebra `A`,
  `(T - 1) * (T - d 0 • 1) = 0` with `d 0 ≠ 0`, `d 0 ^ N ! ≠ 1`, `d i = 1` for `i ≠ 0`, `α i ≠ 0`,
  and `∏ i, (X - C (α i * d i ^ b))` kills `F * T ^ b` for every `b : ℕ`, then
  `F * (T - 1) = α 0 • (T - 1)`.

## References

* Provenance: adapted from `mul_sub_one_eq_smul_sub_one` in
  `grh/src/Lib/GaloisRep/LocalGlobal/IwahoriCompatibility.lean` of `grh-lean`
  (https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

namespace TauCeti

open Finset Matrix Polynomial

variable {k : Type*} [Field k]

/-- Vandermonde cancellation in a `k`-module: if `r : Fin n → k` is injective and
`∑ i : Fin n, r b ^ (i : ℕ) • v i = 0` for every `b : Fin n`, then `v i = 0` for every `i`. -/
theorem eq_zero_of_forall_sum_pow_smul_eq_zero {M : Type*} [AddCommGroup M] [Module k M]
    {n : ℕ} {r : Fin n → k} (hr : Function.Injective r) {v : Fin n → M}
    (h : ∀ b : Fin n, ∑ i : Fin n, r b ^ (i : ℕ) • v i = 0) (j : Fin n) :
    v j = 0 := by
  have hdet : IsUnit (Matrix.vandermonde r).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hr)
  let Vinv := (Matrix.vandermonde r)⁻¹
  have hmul : Vinv * Matrix.vandermonde r = 1 := Matrix.nonsing_inv_mul _ hdet
  have hsum : ∑ b : Fin n, Vinv j b • ∑ i : Fin n, r b ^ (i : ℕ) • v i = 0 := by
    simp [h]
  calc v j
      = ∑ i : Fin n, (1 : Matrix (Fin n) (Fin n) k) j i • v i := by
        simp [Matrix.one_apply]
    _ = ∑ i : Fin n, (∑ b : Fin n, Vinv j b * r b ^ (i : ℕ)) • v i := by
        refine sum_congr rfl fun i _ ↦ ?_
        have hij := congrFun₂ hmul j i
        simpa [Matrix.mul_apply, Matrix.vandermonde_apply] using congrArg (· • v i) hij.symm
    _ = ∑ b : Fin n, Vinv j b • ∑ i : Fin n, r b ^ (i : ℕ) • v i := by
        simp_rw [sum_smul, smul_sum, mul_smul]
        exact sum_comm
    _ = 0 := hsum

/-- Let `F` and `T` commute in a `k`-algebra `A`, with `(X - 1) * (X - C (d 0))` killing `T`,
`d i = 1` for `i ≠ 0`, `d 0 ≠ 0`, `d 0 ^ N ! ≠ 1`, and `α i ≠ 0` for all `i : Fin N`. If
`∏ i, (X - C (α i * d i ^ b))` kills `F * T ^ b` for every `b : ℕ`, then
`F * (T - 1) = α 0 • (T - 1)`. -/
theorem mul_sub_one_eq_smul_sub_one {A : Type*} [Ring A] [Algebra k A] {N : ℕ} [NeZero N]
    {F T : A} {α d : Fin N → k} (hd : ∀ i : Fin N, i ≠ 0 → d i = 1) (hd_ne : d 0 ≠ 0)
    (hζ : d 0 ^ N.factorial ≠ 1) (hα : ∀ i : Fin N, α i ≠ 0) (hFT : Commute F T)
    (hT : aeval T ((X - 1) * (X - C (d 0))) = 0)
    (hF : ∀ b : ℕ, aeval (F * T ^ b) (∏ i : Fin N, (X - C (α i * d i ^ b))) = 0) :
    F * (T - 1) = α 0 • (T - 1) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  let q : k[X] := ∏ i : Fin N, (X - C (α i.succ))
  have hq_zero : q.coeff 0 ≠ 0 := by simp [q, hα, coeff_zero_prod, prod_eq_zero_iff]
  have hT_semi : SemiconjBy (T - 1) T (d 0 • 1) := by
    simpa [SemiconjBy, mul_sub (T - 1), sub_eq_zero, Algebra.algebraMap_eq_smul_one] using hT
  have h_semi (b : ℕ) : SemiconjBy (T - 1) (F * T ^ b) (d 0 ^ b • F) := by
    simpa [smul_pow] using
      (hFT.sub_right (.one_right F)).symm.semiconjBy.mul_right (hT_semi.pow_right b)
  have h_sum (b : ℕ) : ∑ i : Fin (N + 1),
      (d 0 ^ b) ^ i.val • (q.coeff i • F ^ i.val * (F - α 0 • 1) * (T - 1)) = 0 := by
    have h_prod : ∏ i, (X - C (α i * d i ^ b)) = q * (X - C (α 0 * d 0 ^ b)) := by
      simp [Fin.prod_univ_succ, hd, q, mul_comm]
    have h_move : aeval (d 0 ^ b • F) q * (d 0 ^ b • (F - α 0 • 1)) * (T - 1) = 0 := by
      have h_sem : (T - 1) * aeval (F * T ^ b) (∏ i, (X - C (α i * d i ^ b))) =
          aeval (d 0 ^ b • F) (∏ i, (X - C (α i * d i ^ b))) * (T - 1) := by
        have h_aeval (p : k[X]) :
            SemiconjBy (T - 1) (aeval (F * T ^ b) p) (aeval (d 0 ^ b • F) p) := by
          induction p using Polynomial.induction_on' with
          | add p₁ p₂ h₁ h₂ => simpa only [map_add] using h₁.add_right h₂
          | monomial n c =>
            simpa only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
              SemiconjBy, mul_smul_comm, smul_mul_assoc] using
              congrArg (c • ·) ((h_semi b).pow_right n).eq
        exact (h_aeval _).eq
      rw [hF b, mul_zero] at h_sem
      rw [h_prod, map_mul] at h_sem
      simpa [smul_sub, smul_pow, smul_smul, mul_comm, Algebra.algebraMap_eq_smul_one] using
        h_sem.symm
    rw [aeval_eq_sum_range, show q.natDegree = N by simp [q], sum_range] at h_move
    simpa [hd_ne, sum_mul, smul_pow, ← smul_sum, smul_comm (q.coeff _)] using h_move
  have h_inj : Function.Injective fun b : Fin (N + 1) ↦ d 0 ^ b.val := by
    refine .of_lt_imp_ne fun i j hij (h_eq : d 0 ^ i.val = d 0 ^ j.val) ↦ hζ ?_
    have h_pow : d 0 ^ (j.val - i.val) = 1 := by simp [pow_sub₀ _ hd_ne hij.le, ← h_eq, hd_ne]
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_pow_eq_one h_pow).trans (Nat.dvd_factorial (by omega) (by omega)))
  have h_zero := eq_zero_of_forall_sum_pow_smul_eq_zero h_inj (fun b ↦ h_sum b.val) 0
  simpa [hq_zero, sub_mul, sub_eq_zero] using h_zero

end TauCeti
