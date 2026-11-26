/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Newton
public import TauCeti.NumberTheory.SatoTate.Ambient

import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots
import TauCeti.LinearAlgebra.Matrix.Charpoly.Symplectic
import TauCeti.Topology.Instances.Matrix

/-!
# The coefficient map on `U(d)`

For `g ∈ U(d)` the **coefficients** `a_i(g)` are the coefficients of the reversed characteristic
polynomial `det (1 - T g) = ∏ⱼ (1 - λⱼ T) = 1 + a_1 T + a_2 T² + ⋯ + a_d T^d`, Mathlib's
`Matrix.charpolyRev`. This is the normalized `L`-polynomial of Sato–Tate theory, read with the
constant term first, so `a_0 = 1`, `a_1 = -tr g`, `a_i = (-1)^i e_i(λ_1, …, λ_d)` for the
eigenvalues `λ_j` of `g`, `a_d = (-1)^d det g`, and `a_i = 0` for `i > d`. The coefficients are
the random variables whose joint distribution under the Haar measure of a closed subgroup of
`U(d)` is the Sato–Tate distribution.

Each `a_i` is a polynomial in the matrix entries, hence continuous on `U(d)`, and a class
function. For a unitary `g` the eigenvalue multiset is closed under `λ ↦ (conj λ)⁻¹`, which
gives the reciprocity `a_(d-i) = (-1)^d det(g) conj(a_i)`. On the ambient groups of Sato–Tate
theory it becomes:

* on `USp(d)`, `d` even, the coefficients are **real** and **palindromic**: `a_(d-i) = a_i`, since
  a symplectic matrix is conjugate to its inverse transpose;
* on `O(d)` the coefficients are real and `a_(d-i) = (-1)^d det(g) a_i`.

The power sums `s_k(g) = tr (g^k)` and the coefficients are related by **Newton's identities**
`k a_k = -(a_(k-1) s_1 + ⋯ + a_0 s_k)`, and every `s_k` is `(-1)^k` times the integer Newton
polynomial `TauCeti.newtonMvPolynomial ℤ d k` in `a_1, …, a_d`.

## Main definitions

* `TauCeti.SatoTate.coeff g i`: the coefficient `a_i(g)` of `T^i` in `det (1 - T g)`.
* `TauCeti.SatoTate.trace g`: the trace `tr g`.
* `TauCeti.SatoTate.coeffVec g`: the vector `(a_0(g), …, a_d(g))`.

## Main results

* `TauCeti.SatoTate.continuous_trace`, `TauCeti.SatoTate.trace_eq_of_isConj`: the trace is a
  continuous class function.
* `TauCeti.SatoTate.coeff_zero`, `TauCeti.SatoTate.coeff_one`, `TauCeti.SatoTate.coeff_dim`,
  `TauCeti.SatoTate.coeff_eq_zero_of_dim_lt`: `a_0 = 1`, `a_1 = -tr g` (also for `d = 0`),
  `a_d = (-1)^d det g`, and `a_i = 0` beyond the degree.
* `TauCeti.SatoTate.coeff_eq_neg_one_pow_mul_esymm`: `a_i = (-1)^i e_i` of the eigenvalues.
* `TauCeti.SatoTate.continuous_coeff`, `TauCeti.SatoTate.continuous_coeffVec`: continuity.
* `TauCeti.SatoTate.coeff_eq_of_isConj`: the coefficients are class functions.
* `TauCeti.SatoTate.coeff_dim_sub`: `a_(d-i) = (-1)^d det(g) conj(a_i)` for `i ≤ d` on
  `U(d)`.
* `TauCeti.SatoTate.coeff_dim_sub_of_mem_USp`, `TauCeti.SatoTate.conj_coeff_of_mem_USp`: on
  `USp(d)` the coefficients are palindromic and real.
* `TauCeti.SatoTate.coeff_dim_sub_of_mem_Od`, `TauCeti.SatoTate.conj_coeff_of_mem_Od`: on `O(d)`
  they are real and satisfy `a_(d-i) = (-1)^d det(g) a_i`.
* `TauCeti.SatoTate.mul_coeff_eq_neg_sum`, `TauCeti.SatoTate.trace_pow_eq_aeval_coeff`: Newton's
  identities, and the power sums as integer polynomials in the coefficients.

## References

* F. Fité, K. S. Kedlaya, V. Rotger, A. V. Sutherland, *Sato–Tate distributions and Galois
  endomorphism modules in genus 2*, Compositio Math. 148 (2012), §2.
* N. M. Katz, P. Sarnak, *Random Matrices, Frobenius Eigenvalues, and Monodromy*, AMS Colloquium
  Publications 45 (1999), §5.0.
-/

public section

open Matrix ComplexConjugate

namespace TauCeti.SatoTate

variable {d : ℕ}

/-- The trace `tr g` of `g ∈ U(d)`. -/
noncomputable def trace (g : U d) : ℂ :=
  Matrix.trace (g : Matrix (Fin d) (Fin d) ℂ)

theorem trace_def (g : U d) : trace g = Matrix.trace (g : Matrix (Fin d) (Fin d) ℂ) :=
  (rfl)

/-- The trace is continuous on `U(d)`. -/
@[continuity, fun_prop]
theorem continuous_trace : Continuous (trace : U d → ℂ) :=
  (continuous_id.matrix_trace).comp continuous_subtypeVal

/-- `tr (gh) = tr (hg)`. -/
theorem trace_mul_comm (g h : U d) : trace (g * h) = trace (h * g) := by
  rw [trace_def, trace_def, Submonoid.coe_mul, Submonoid.coe_mul, Matrix.trace_mul_comm]

/-- The trace is a class function on `U(d)`. -/
theorem trace_eq_of_isConj {g h : U d} (hgh : IsConj g h) : trace g = trace h := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hgh
  rw [trace_mul_comm, inv_mul_cancel_left]

/-- The coefficient `a_i(g)` of `T^i` in the reversed characteristic polynomial
`det (1 - T g) = 1 + a_1 T + ⋯ + a_d T^d` of `g ∈ U(d)`. It is `(-1)^i` times the `i`-th
elementary symmetric function of the eigenvalues of `g`
(`TauCeti.SatoTate.coeff_eq_neg_one_pow_mul_esymm`), and it vanishes for `i > d`. -/
noncomputable def coeff (g : U d) (i : ℕ) : ℂ :=
  (g : Matrix (Fin d) (Fin d) ℂ).charpolyRev.coeff i

theorem coeff_def (g : U d) (i : ℕ) :
    coeff g i = (g : Matrix (Fin d) (Fin d) ℂ).charpolyRev.coeff i :=
  (rfl)

/-- `a_0 = 1`. -/
@[simp]
theorem coeff_zero (g : U d) : coeff g 0 = 1 :=
  coeff_charpolyRev_zero _

/-- `a_1 = -tr g`; for `d = 0` both sides vanish. -/
@[simp]
theorem coeff_one (g : U d) : coeff g 1 = -trace g :=
  coeff_charpolyRev_eq_neg_trace _

/-- `a_d = (-1)^d det g`. -/
theorem coeff_dim (g : U d) : coeff g d = (-1) ^ d * (g : Matrix (Fin d) (Fin d) ℂ).det := by
  simpa [coeff_def] using coeff_charpolyRev_card (g : Matrix (Fin d) (Fin d) ℂ)

/-- The coefficients vanish beyond the degree. -/
theorem coeff_eq_zero_of_dim_lt (g : U d) {i : ℕ} (hi : d < i) : coeff g i = 0 :=
  coeff_charpolyRev_eq_zero _ (by simpa using hi)

/-- `a_i = (-1)^i e_i(λ_1, …, λ_d)`, where `λ_1, …, λ_d` are the eigenvalues of `g`, the roots of
its characteristic polynomial counted with multiplicity. -/
theorem coeff_eq_neg_one_pow_mul_esymm (g : U d) (i : ℕ) :
    coeff g i = (-1) ^ i * (g : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm i :=
  coeff_charpolyRev_eq_esymm_roots_charpoly_of_splits (IsAlgClosed.splits _) i

/-- For `i ≤ d`, `a_(d-i)` is the coefficient of `T^i` in the characteristic polynomial
`det (T - g)`. -/
theorem coeff_dim_sub_eq_coeff_charpoly (g : U d) {i : ℕ} (hi : i ≤ d) :
    coeff g (d - i) = (g : Matrix (Fin d) (Fin d) ℂ).charpoly.coeff i := by
  simpa [coeff_def] using
    coeff_charpolyRev_card_sub (g : Matrix (Fin d) (Fin d) ℂ) (k := i) (by simpa)

/-- Each coefficient `a_i` is continuous on `U(d)`. -/
@[continuity, fun_prop]
theorem continuous_coeff (i : ℕ) : Continuous fun g : U d ↦ coeff g i :=
  (continuous_charpolyRev_coeff i).comp continuous_subtypeVal

/-- `a_i(gh) = a_i(hg)`. -/
theorem coeff_mul_comm (g h : U d) (i : ℕ) : coeff (g * h) i = coeff (h * g) i := by
  rw [coeff_def, coeff_def, Submonoid.coe_mul, Submonoid.coe_mul, charpolyRev_mul_comm]

/-- The coefficients are class functions on `U(d)`. -/
theorem coeff_eq_of_isConj {g h : U d} (hgh : IsConj g h) (i : ℕ) : coeff g i = coeff h i := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hgh
  rw [coeff_mul_comm, inv_mul_cancel_left]

/-- **Reciprocity on `U(d)`.** For `i ≤ d`, `a_(d-i)(g) = (-1)^d det(g) conj (a_i(g))`: the
eigenvalues of a unitary matrix are closed under `λ ↦ (conj λ)⁻¹`. -/
theorem coeff_dim_sub (g : U d) {i : ℕ} (hi : i ≤ d) :
    coeff g (d - i) = (-1) ^ d * (g : Matrix (Fin d) (Fin d) ℂ).det * conj (coeff g i) := by
  simpa [coeff_def] using coeff_charpolyRev_card_sub_of_mem_unitaryGroup g.property (k := i)
    (by simpa)

/-- **Palindromy on `USp(d)`.** For even `d` and `g ∈ USp(d)`, `a_(d-i)(g) = a_i(g)` for `i ≤ d`:
a symplectic matrix has the same characteristic polynomial as its inverse. -/
theorem coeff_dim_sub_of_mem_USp (hd : Even d) {g : U d} (hg : g ∈ USp d) {i : ℕ}
    (hi : i ≤ d) : coeff g (d - i) = coeff g i := by
  obtain ⟨m, rfl⟩ := hd
  have h := SymplecticGroup.charpolyRev_eq_charpoly
    ((mem_USp_iff_reindex_mem_symplecticGroup g).mp hg)
  rw [charpolyRev_reindex, charpoly_reindex] at h
  rw [coeff_dim_sub_eq_coeff_charpoly g hi, coeff_def, h]

/-- **The coefficients are real on `USp(d)`** for even `d`. -/
theorem conj_coeff_of_mem_USp (hd : Even d) {g : U d} (hg : g ∈ USp d) (i : ℕ) :
    conj (coeff g i) = coeff g i := by
  rcases le_or_gt i d with hi | hi
  · have h := coeff_dim_sub g hi
    rwa [coeff_dim_sub_of_mem_USp hd hg hi, det_eq_one_of_mem_USp hd hg, hd.neg_one_pow,
      one_mul, one_mul, eq_comm] at h
  · simp [coeff_eq_zero_of_dim_lt g hi]

/-- **The coefficients are real on `O(d)`.** -/
theorem conj_coeff_of_mem_Od {g : U d} (hg : g ∈ Od d) (i : ℕ) :
    conj (coeff g i) = coeff g i := by
  -- `⇑Complex.ofRealHom` is the coercion `ℝ → ℂ` by definition (`Complex.ofRealHom_eq_coe` is
  -- `rfl`); stating `hN` with the ring homomorphism lets `Matrix.charpolyRev_map` apply.
  have hN : ((g : Matrix (Fin d) (Fin d) ℂ).map Complex.re).map Complex.ofRealHom = g :=
    map_ofReal_map_re_of_mem_Od hg
  rw [coeff_def, ← hN, charpolyRev_map, Polynomial.coeff_map, Complex.ofRealHom_eq_coe,
    Complex.conj_ofReal]

/-- **Reciprocity on `O(d)`.** For `g ∈ O(d)` and `i ≤ d`, `a_(d-i)(g) = (-1)^d det(g) a_i(g)`,
where `det g = ±1` (`TauCeti.SatoTate.det_eq_one_or_neg_one_of_mem_Od`). -/
theorem coeff_dim_sub_of_mem_Od {g : U d} (hg : g ∈ Od d) {i : ℕ} (hi : i ≤ d) :
    coeff g (d - i) = (-1) ^ d * (g : Matrix (Fin d) (Fin d) ℂ).det * coeff g i := by
  rw [coeff_dim_sub g hi, conj_coeff_of_mem_Od hg]

/-- **Newton's identities** on `U(d)`: `k a_k = -(a_(k-1) s_1 + a_(k-2) s_2 + ⋯ + a_0 s_k)`, where
`s_j = tr (g^j)`. -/
theorem mul_coeff_eq_neg_sum (g : U d) (k : ℕ) :
    (k : ℂ) * coeff g k =
      -∑ j ∈ Finset.range k, coeff g (k - (j + 1)) * trace (g ^ (j + 1)) := by
  simpa [coeff_def, trace_def] using
    (g : Matrix (Fin d) (Fin d) ℂ).mul_coeff_charpolyRev_eq_neg_sum k

/-- **The power sums are integer polynomials in the coefficients.** `s_k(g) = tr (g^k)` is
`(-1)^k` times the integer Newton polynomial `TauCeti.newtonMvPolynomial ℤ d k` evaluated at the
coefficients `a_1(g), …, a_d(g)`. -/
theorem trace_pow_eq_aeval_coeff (g : U d) (k : ℕ) :
    trace (g ^ k) =
      (-1) ^ k *
        MvPolynomial.aeval (fun j : Fin d ↦ coeff g (j + 1)) (newtonMvPolynomial ℤ d k) := by
  have h := ((g : Matrix (Fin d) (Fin d) ℂ).trace_pow_eq_aeval_newtonMvPolynomial k).trans
    (aeval_neg_one_pow_mul_newtonMvPolynomial _)
  rw [Fintype.card_fin] at h
  simpa [coeff_def, trace_def] using h

/-- The coefficient vector `(a_0(g), a_1(g), …, a_d(g))` of `g ∈ U(d)`. -/
noncomputable def coeffVec (g : U d) : Fin (d + 1) → ℂ :=
  fun i ↦ coeff g i

@[simp]
theorem coeffVec_apply (g : U d) (i : Fin (d + 1)) : coeffVec g i = coeff g i :=
  (rfl)

/-- The coefficient vector is continuous on `U(d)`. -/
@[continuity, fun_prop]
theorem continuous_coeffVec : Continuous (coeffVec : U d → Fin (d + 1) → ℂ) :=
  continuous_pi fun i ↦ continuous_coeff i

end TauCeti.SatoTate
