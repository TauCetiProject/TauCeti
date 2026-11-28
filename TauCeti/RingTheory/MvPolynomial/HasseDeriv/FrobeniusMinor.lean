/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Nat.Choose.Sum
import TauCeti.RingTheory.Derivation.Ideal

/-!
# Frobenius divisibility of ordinary jet minors

At points with `x ^ p ≡ y (mod p)`, a rectangular array of bivariate monomials admits a
determinant-one row change that introduces powers of `X ^ p - Y`. The ordinary derivatives in
`X` of this factor are divisible by `p`, with no restriction on the derivative order.

* `TauCeti.exists_det_one_mul_monomial_eq_frobenius` gives the row change after applying
  any linear map to the polynomials, using `Matrix.BlockTriangular.det_fintype`.
* `TauCeti.pow_dvd_det_ordinaryJet_of_frobenius` bounds every full-row minor of the
  original ordinary jet matrix, including after applying coordinate linear maps to its entries.
  It uses `Derivation.iterate_mul_prod_mem_ideal_pow` and `Matrix.prod_dvd_det_of_dvd_row`.

The row change and its divisibility are from Ben Green, *On Landau–Siegel zeros*,
Hexagon 2610.00311 (2026), §§2–6.
-/

public section

open Finset Matrix MvPolynomial

namespace TauCeti

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- A determinant-one row operation replaces each monomial `X^i Y^j` in a rectangle by
`X^(i - p*h) Y^j (X^p - Y)^h`, provided the latter stays in the rectangle.
This holds after applying any linear map to the polynomial rows. See Green, *On Landau–Siegel
zeros*. -/
theorem exists_det_one_mul_monomial_eq_frobenius {ι : Type*} {m n : ℕ} (p : ℕ)
    (h : Fin m × Fin n → ℕ)
    (hx : ∀ i, p * h i ≤ i.1.val) (hy : ∀ i, i.2.val + h i < n)
    (L : MvPolynomial (Fin 2) R →ₗ[R] (ι → R)) :
    ∃ T : Matrix (Fin m × Fin n) (Fin m × Fin n) R, T.det = 1 ∧
      T * Matrix.of (fun i ↦ L (X 0 ^ i.1.val * X 1 ^ i.2.val)) =
        Matrix.of (fun i ↦
          L (X 0 ^ (i.1.val - p * h i) * X 1 ^ i.2.val * (X 0 ^ p - X 1) ^ h i)) := by
  let index (i : Fin m × Fin n) (t : Fin (h i)) : Fin m × Fin n :=
    (⟨i.1.val - p * h i + p * t.val, by
      calc
        _ ≤ i.1.val - p * h i + p * h i := by gcongr; exact t.isLt.le
        _ < m := by simpa only [Nat.sub_add_cancel (hx i)] using i.1.isLt⟩,
      ⟨i.2.val + (h i - t.val), (Nat.add_le_add_left (Nat.sub_le _ _) _).trans_lt (hy i)⟩)
  let coeff (i : Fin m × Fin n) (t : ℕ) : R := (-1) ^ (h i - t) * (h i).choose t
  let U : Matrix (Fin m × Fin n) (Fin m × Fin n) R :=
    Matrix.of fun i j ↦ ∑ t : Fin (h i), if index i t = j then coeff i t.val else 0
  have hzero (i j : Fin m × Fin n) (hij : j.2 ≤ i.2) : U i j = 0 := by
    simp only [U, of_apply]
    refine sum_eq_zero fun t _ ↦ ite_eq_right fun e ↦ ?_
    have he := congrArg (fun x : Fin m × Fin n ↦ x.2.val) e
    simp only [index] at he
    lia
  refine ⟨1 + U, ?_, ?_⟩
  · have htri : (1 + U).BlockTriangular Prod.snd := by
      refine fun i j (hlt : j.2 < i.2) ↦ ?_
      have hne : i ≠ j := ne_of_apply_ne Prod.snd hlt.ne'
      simp only [Matrix.add_apply, hzero i j hlt.le, Matrix.one_apply_ne hne, add_zero]
    have hblock (j : Fin n) : (1 + U).toSquareBlock Prod.snd j = 1 := by
      ext u v
      have huv : u.val.2 = v.val.2 := u.property.trans v.property.symm
      simp only [toSquareBlock_def, of_apply, Matrix.add_apply, hzero _ _ huv.ge, add_zero,
        Matrix.one_apply, Subtype.ext_iff]
    rw [htri.det_fintype]
    simp only [hblock, det_one, prod_const_one]
  · rw [Matrix.add_mul, Matrix.one_mul]
    ext i j
    have hbinom : X 0 ^ (i.1.val - p * h i) * X 1 ^ i.2.val * (X 0 ^ p - X 1) ^ h i =
        (∑ t : Fin (h i), coeff i t.val •
          (X 0 ^ (index i t).1.val * X 1 ^ (index i t).2.val : MvPolynomial (Fin 2) R)) +
        X 0 ^ i.1.val * X 1 ^ i.2.val := by
      rw [sub_eq_add_neg, add_pow, sum_range_succ]
      simp only [mul_add, mul_sum, ← Fin.sum_univ_eq_sum_range, Nat.sub_self, pow_zero, mul_one,
        Nat.choose_self, Nat.cast_one, ← pow_mul]
      congr 1
      · apply sum_congr rfl
        intro t _
        rw [← neg_one_mul (X 1 : MvPolynomial (Fin 2) R), mul_pow]
        simp only [index, coeff, Algebra.smul_def, map_mul, map_pow, map_neg, map_one,
          map_natCast, pow_add, pow_mul]
        ring
      · rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel (hx i)]
    simp only [Matrix.add_apply, Matrix.mul_apply, of_apply, U, hbinom, map_add, map_sum, map_smul,
      Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul]
    rw [sum_comm, add_comm]
    congr 1
    exact sum_congr rfl fun t _ ↦ by
      simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

/-- All ordinary jets in `X i` of `g * (X i ^ p - X j)^e` are divisible by `p ^ e` at
a point satisfying `a i ^ p ≡ a j (mod p)`, when `i ≠ j`. See Green, *On Landau–Siegel zeros*. -/
theorem _root_.MvPolynomial.pow_dvd_aeval_iterate_pderiv_mul_X_pow_sub_X_pow {σ : Type*} {i j : σ}
    (g : MvPolynomial σ R) (hij : j ≠ i) {p : ℕ} {a : σ → S}
    (ha : (p : S) ∣ a i ^ p - a j) (e k : ℕ) :
    (p : S) ^ e ∣ aeval a ((pderiv i)^[k] (g * (X i ^ p - X j) ^ e)) := by
  let d : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) := pderiv i
  have hfactor (t : ℕ) : aeval a (d^[t] (X i ^ p - X j)) ∈ Ideal.span {(p : S)} := by
    rw [Ideal.mem_span_singleton]
    cases t with
    | zero =>
      simpa only [Function.iterate_zero_apply, map_sub, map_pow, aeval_X] using ha
    | succ t =>
      have hd : d (X i ^ p - X j) = p • X i ^ (p - 1) := by
        simp only [d, map_sub, pderiv_pow, pderiv_X_self, pderiv_X_of_ne hij, mul_one,
          sub_zero, nsmul_eq_mul]
      rw [Function.iterate_succ_apply, hd]
      have hmap (f : MvPolynomial σ R) : d^[t] (p • f) = p • d^[t] f := by
        simpa only [pow_apply_eq_iterate, Derivation.coeFn_coe] using
          map_nsmul (d.toLinearMap ^ t) p f
      rw [hmap, map_nsmul, nsmul_eq_mul]
      exact dvd_mul_right _ _
  have hprod := d.iterate_mul_prod_mem_ideal_pow (RingHomClass.toRingHom (aeval a))
    (fun _ : Fin e ↦ X i ^ p - X j) g (Ideal.span {(p : S)}) k (fun _ t _ ↦ hfactor t) k le_rfl
  simpa only [prod_const, card_univ, Fintype.card_fin, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, RingHom.coe_coe, d] using hprod

/-- At points satisfying the Frobenius congruence, the determinant of any full-row ordinary jet
minor is divisible by `p` to the sum of the row gains
`min (i / p) (n - 1 - j)`. A column specifies a point in an `R`-algebra `S`, a jet order, and a
linear projection back to `R`. This allows computing minors in `R` of coordinate arrays of jets
evaluated in `S`. See Green, *On Landau–Siegel zeros*. -/
theorem pow_dvd_det_ordinaryJet_of_frobenius {m n : ℕ} {p : ℕ}
    (a : Fin m × Fin n → Fin 2 → S) (k : Fin m × Fin n → ℕ)
    (coord : Fin m × Fin n → S →ₗ[R] R) (ha : ∀ j, (p : S) ∣ a j 0 ^ p - a j 1) :
    (p : R) ^ (∑ i : Fin m × Fin n, min (i.1.val / p) (n - 1 - i.2.val)) ∣
      (Matrix.of fun (i j : Fin m × Fin n) ↦
        coord j (aeval (a j) ((pderiv (0 : Fin 2))^[k j]
          (X 0 ^ i.1.val * X 1 ^ i.2.val : MvPolynomial (Fin 2) R)))).det := by
  let h (i : Fin m × Fin n) := min (i.1.val / p) (n - 1 - i.2.val)
  have hx (i : Fin m × Fin n) : p * h i ≤ i.1.val := by
    exact (Nat.mul_le_mul_left _ (min_le_left _ _)).trans (Nat.mul_div_le _ _)
  have hy (i : Fin m × Fin n) : i.2.val + h i < n := by
    have hi := i.2.isLt
    have hm : h i ≤ n - 1 - i.2.val := min_le_right _ _
    lia
  let L : MvPolynomial (Fin 2) R →ₗ[R] (Fin m × Fin n → R) :=
    LinearMap.pi fun j ↦
      coord j ∘ₗ (aeval (a j)).toLinearMap ∘ₗ ((pderiv (0 : Fin 2)).toLinearMap ^ k j)
  obtain ⟨T, hT, hmul⟩ := exists_det_one_mul_monomial_eq_frobenius p h hx hy L
  have hL (f : MvPolynomial (Fin 2) R) (j : Fin m × Fin n) :
      L f j = coord j (aeval (a j) ((pderiv (0 : Fin 2))^[k j] f)) := by
    simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      pow_apply_eq_iterate, Derivation.coeFn_coe]
  have hrow (i j : Fin m × Fin n) :
      (p : R) ^ h i ∣ L (X 0 ^ (i.1.val - p * h i) * X 1 ^ i.2.val *
        (X 0 ^ p - X 1) ^ h i) j := by
    rw [hL]
    obtain ⟨y, hy⟩ := pow_dvd_aeval_iterate_pderiv_mul_X_pow_sub_X_pow
      (X 0 ^ (i.1.val - p * h i) * X 1 ^ i.2.val : MvPolynomial (Fin 2) R)
      (by decide) (ha j) (h i) (k j)
    refine ⟨coord j y, ?_⟩
    simpa only [hy, nsmul_eq_mul, Nat.cast_pow] using map_nsmul (coord j) (p ^ h i) y
  have hdet := prod_dvd_det_of_dvd_row
    (.of fun i ↦ L (X 0 ^ (i.1.val - p * h i) * X 1 ^ i.2.val * (X 0 ^ p - X 1) ^ h i))
    (fun i ↦ (p : R) ^ h i) hrow
  rw [← hmul, det_mul, hT, one_mul, prod_pow_eq_pow_sum] at hdet
  simpa only [← hL] using hdet

end TauCeti
