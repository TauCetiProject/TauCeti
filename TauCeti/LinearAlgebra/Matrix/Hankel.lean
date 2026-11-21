/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Shifted Hankel determinants

For a sequence `a : ℕ → R` over a commutative ring and `n : ℕ`, the shifted Hankel matrix is the
`n × n` matrix with entries `a (i + j + 1)` for `0 ≤ i, j < n`, and its determinant is the shifted
Hankel determinant `TauCeti.shiftedHankelDet a n`, written `D_n(a)`. The coefficient `a 0` does
not enter. The shift by one is the convention of the coefficients `∮ G(z) z ^ k dz` of a Laurent
series at infinity, which is how these determinants arise in arithmetic (the Pólya–Carlson and
Dimitrov arguments); for the unshifted Hankel determinant `det (m (i + j))` of a sequence of
moments `m`, take `a (k + 1) = m k`.

The main structural fact is the invariance of `D_n(a)` under a monic change of basis. If a linear
functional `L` on `R[X]` has moments `L (X ^ k) = a (k + 1)`, then `D_n(a)` is the determinant of
the moment matrix `L (X ^ i * X ^ j)`, and it does not change when the powers `X ^ i` in the rows
and the columns are replaced by any polynomials `p i`, `q j` of degree at most `i`, `j` with
coefficient `1` there, for instance monic polynomials of exact degrees `i`, `j`
(`LinearMap.det_of_apply_mul_eq_shiftedHankelDet`). This is how the Hankel determinants of the
moments of a measure become products of the norms of its monic orthogonal polynomials. It comes
from the corresponding statement for any bilinear form on `R[X]`
(`LinearMap.det_of_apply_eq_det_of_apply_X_pow`): the change of basis is unitriangular.

## Main definitions and results

* `TauCeti.shiftedHankelDet a n`: the determinant `det (a (i + j + 1))_{i, j < n}`, with
  `shiftedHankelDet_zero`, `shiftedHankelDet_one` and `shiftedHankelDet_two` computing it for
  `n ≤ 2`, and `shiftedHankelDet_congr` showing that only `a (k + 1)` matters;
* `RingHom.map_shiftedHankelDet`: a ring homomorphism applied to `D_n(a)` gives `D_n(f ∘ a)`;
  for an integer sequence, `TauCeti.one_le_norm_shiftedHankelDet_intCast` shows that a nonzero
  determinant has norm at least one in `ℝ` or `ℂ`;
* `LinearMap.det_of_apply_eq_det_of_apply_X_pow`: the Gram determinant of a bilinear form on
  `R[X]` on the families `p`, `q` equals the one on the monomials;
* `LinearMap.det_of_apply_mul_eq_shiftedHankelDet`: the invariance of `D_n(a)` under a monic change
  of basis;
* `TauCeti.shiftedHankelDet_eq_zero_of_recurrence`: if `a (m + r + 1)` is a fixed linear
  combination of `a (m + 1), …, a (m + r)` for every `m < n`, then `D_n(a) = 0` for `n > r`.

## References

* V. Dimitrov, *A proof of the Schinzel–Zassenhaus conjecture on polynomials*, §4, the Hankel
  determinant in the proof of Theorem 4.
* T. S. Chihara, *An Introduction to Orthogonal Polynomials*, Ch. I, §3.
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- The shifted Hankel determinant `D_n(a) = det (a (i + j + 1))_{i, j < n}` of a sequence
`a : ℕ → R`. The coefficient `a 0` does not enter, and `D_0(a) = 1`. -/
def shiftedHankelDet (a : ℕ → R) (n : ℕ) : R :=
  (Matrix.of fun i j : Fin n => a (i + j + 1)).det

/-- The defining determinant of `shiftedHankelDet`. -/
theorem shiftedHankelDet_def (a : ℕ → R) (n : ℕ) :
    shiftedHankelDet a n = (Matrix.of fun i j : Fin n => a (i + j + 1)).det :=
  (rfl)

@[simp]
theorem shiftedHankelDet_zero (a : ℕ → R) : shiftedHankelDet a 0 = 1 := by
  simp [shiftedHankelDet_def]

@[simp]
theorem shiftedHankelDet_one (a : ℕ → R) : shiftedHankelDet a 1 = a 1 := by
  simp [shiftedHankelDet_def]

theorem shiftedHankelDet_two (a : ℕ → R) : shiftedHankelDet a 2 = a 1 * a 3 - a 2 ^ 2 := by
  simp only [shiftedHankelDet_def, Matrix.det_fin_two, Matrix.of_apply, Fin.val_zero, Fin.val_one]
  ring

/-- The shifted Hankel determinants only depend on the terms `a (k + 1)`. -/
theorem shiftedHankelDet_congr {a b : ℕ → R} (h : ∀ k, a (k + 1) = b (k + 1)) (n : ℕ) :
    shiftedHankelDet a n = shiftedHankelDet b n := by
  simp only [shiftedHankelDet_def, h]

end TauCeti

open TauCeti in
/-- A ring homomorphism maps the shifted Hankel determinant of `a` to that of `f ∘ a`. -/
theorem RingHom.map_shiftedHankelDet {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a : ℕ → R) (n : ℕ) : f (shiftedHankelDet a n) = shiftedHankelDet (f ∘ a) n := by
  rw [shiftedHankelDet_def, shiftedHankelDet_def, f.map_det, RingHom.mapMatrix_apply]
  exact congrArg Matrix.det (Matrix.ext fun i j => by simp)

namespace TauCeti

/-- The shifted Hankel determinant of an integer sequence, computed in `ℝ` or `ℂ`, is an integer,
so it has norm at least one unless it vanishes. -/
theorem one_le_norm_shiftedHankelDet_intCast {K : Type*} [RCLike K] (a : ℕ → ℤ) {n : ℕ}
    (h : shiftedHankelDet (fun k => (a k : K)) n ≠ 0) :
    1 ≤ ‖shiftedHankelDet (fun k => (a k : K)) n‖ := by
  have hcast : shiftedHankelDet (fun k => (a k : K)) n = ((shiftedHankelDet a n : ℤ) : K) :=
    ((Int.castRingHom K).map_shiftedHankelDet a n).symm
  rw [hcast] at h ⊢
  rw [← RCLike.ofReal_intCast, RCLike.norm_ofReal, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (by exact_mod_cast h)

end TauCeti

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- A polynomial of degree less than `n` is the sum of its first `n` monomials, indexed by
`Fin n`. -/
private theorem eq_sum_fin_coeff_smul_X_pow {p : R[X]} {n : ℕ} (hp : p.natDegree < n) :
    p = ∑ k : Fin n, p.coeff k • X ^ (k : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => p.coeff k • X ^ k)]
  simpa only [smul_X_eq_monomial] using p.as_sum_range' n hp

end Polynomial

/-- The Gram matrix of a bilinear form `B` on `R[X]` on two families `p i`, `q j` of degree at most
`i`, `j`, each with coefficient `1` in its top degree, has the same determinant as the Gram matrix
of `B` on the monomials `X ^ i`, `X ^ j`: the change of basis is unitriangular. -/
theorem LinearMap.det_of_apply_eq_det_of_apply_X_pow {R : Type*} [CommRing R]
    (B : R[X] →ₗ[R] R[X] →ₗ[R] R) {n : ℕ} {p q : Fin n → R[X]}
    (hpdeg : ∀ i, (p i).natDegree ≤ i) (hpcoeff : ∀ i, (p i).coeff i = 1)
    (hqdeg : ∀ j, (q j).natDegree ≤ j) (hqcoeff : ∀ j, (q j).coeff j = 1) :
    (Matrix.of fun i j => B (p i) (q j)).det =
      (Matrix.of fun i j : Fin n => B (X ^ (i : ℕ)) (X ^ (j : ℕ))).det := by
  -- The columns of the coefficient matrix of a family `p i` of degree at most `i` with
  -- coefficient `1` in degree `i` form an upper unitriangular matrix.
  have hU {p : Fin n → R[X]} (hdeg : ∀ i, (p i).natDegree ≤ i) (hcoeff : ∀ i, (p i).coeff i = 1) :
      (Matrix.of fun k i : Fin n => (p i).coeff k).IsUpperUnitriangular :=
    (Matrix.isUpperUnitriangular_def _).2
      ⟨fun _ i hik => coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_lt hik), hcoeff⟩
  have key : (Matrix.of fun i j => B (p i) (q j)) =
      (Matrix.of fun k i : Fin n => (p i).coeff k).transpose *
        (Matrix.of fun i j : Fin n => B (X ^ (i : ℕ)) (X ^ (j : ℕ))) *
          Matrix.of fun l j : Fin n => (q j).coeff l := by
    ext i j
    rw [Matrix.of_apply]
    conv_lhs => rw [eq_sum_fin_coeff_smul_X_pow ((hpdeg i).trans_lt i.isLt),
      eq_sum_fin_coeff_smul_X_pow ((hqdeg j).trans_lt j.isLt)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    (hU hpdeg hpcoeff).det_eq_one, (hU hqdeg hqcoeff).det_eq_one, one_mul, mul_one]

open TauCeti in
/-- **Invariance of the shifted Hankel determinant under a monic change of basis.** If a linear
functional `L` on `R[X]` has moments `L (X ^ k) = a (k + 1)`, then for families `p i`, `q j` of
degree at most `i`, `j` with coefficient `1` in that degree (for instance monic polynomials of
exact degrees `i`, `j`), the determinant of the moment matrix `L (p i * q j)` is `D_n(a)`. -/
theorem LinearMap.det_of_apply_mul_eq_shiftedHankelDet {R : Type*} [CommRing R]
    (L : R[X] →ₗ[R] R) {a : ℕ → R} (hL : ∀ k, L (X ^ k) = a (k + 1)) {n : ℕ} {p q : Fin n → R[X]}
    (hpdeg : ∀ i, (p i).natDegree ≤ i) (hpcoeff : ∀ i, (p i).coeff i = 1)
    (hqdeg : ∀ j, (q j).natDegree ≤ j) (hqcoeff : ∀ j, (q j).coeff j = 1) :
    (Matrix.of fun i j => L (p i * q j)).det = shiftedHankelDet a n := by
  have := ((LinearMap.mul R R[X]).compr₂ L).det_of_apply_eq_det_of_apply_X_pow hpdeg hpcoeff
    hqdeg hqcoeff
  simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', ← pow_add, hL] at this
  rw [this, shiftedHankelDet_def]

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- If the terms of `a` from index `1` on satisfy a linear recurrence of order `r`,
`a (m + r + 1) = ∑_{l < r} c l * a (m + l + 1)` for every `m < n`, then the `r`-th column of the
shifted Hankel matrix is a combination of the earlier ones, so `D_n(a) = 0` for every `n > r`. -/
theorem shiftedHankelDet_eq_zero_of_recurrence {a : ℕ → R} {r n : ℕ} (hrn : r < n) (c : ℕ → R)
    (h : ∀ m < n, a (m + r + 1) = ∑ l ∈ Finset.range r, c l * a (m + l + 1)) :
    shiftedHankelDet a n = 0 := by
  set v : Fin n → R := fun j => if (j : ℕ) < r then c j else if (j : ℕ) = r then -1 else 0
  have hv : (Matrix.of fun i j : Fin n => a (i + j + 1)).mulVec v = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j => a (i + j + 1) *
      (if j < r then c j else if j = r then -1 else 0)) n,
      ← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hrn)]
    have hIco : ∑ j ∈ Finset.Ico (r + 1) n,
        a (i + j + 1) * (if j < r then c j else if j = r then -1 else 0) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        have hj := (Finset.mem_Ico.mp hj).1
        simp [show ¬j < r by omega, show j ≠ r by omega]
    have hrange : ∑ j ∈ Finset.range r,
        a (i + j + 1) * (if j < r then c j else if j = r then -1 else 0) =
          ∑ j ∈ Finset.range r, c j * a (i + j + 1) :=
      Finset.sum_congr rfl fun j hj => by simp [Finset.mem_range.mp hj, mul_comm]
    rw [hIco, Finset.sum_range_succ, hrange, ← h i i.isLt]
    simp
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hv (i := ⟨r, hrn⟩)
    (by simpa [v] using isUnit_one.neg.mem_nonZeroDivisors)

/-! ### Checks -/

/-- For `a j = 2 ^ j`, `D_1(a) = 2` and `D_2(a) = 0`. -/
example : shiftedHankelDet (fun j => (2 : ℤ) ^ j) 1 = 2 ∧
    shiftedHankelDet (fun j => (2 : ℤ) ^ j) 2 = 0 := by
  simp [shiftedHankelDet_two]

/-- One vanishing determinant does not force the next one to vanish: for `a 1 = 0`, `a 2 = 1`,
`a 3 = 0`, `D_1(a) = 0` but `D_2(a) = -1`. -/
example : shiftedHankelDet (fun j => if j = 2 then (1 : ℤ) else 0) 1 = 0 ∧
    shiftedHankelDet (fun j => if j = 2 then (1 : ℤ) else 0) 2 = -1 := by
  simp [shiftedHankelDet_two]

end TauCeti
