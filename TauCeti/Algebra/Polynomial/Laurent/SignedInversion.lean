/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Symmetric
public import TauCeti.Algebra.Polynomial.Dickson
import TauCeti.Algebra.Polynomial.Laurent.Basic

/-!
# Laurent polynomials fixed by signed inversion

The fixed ring of `T ↦ -T⁻¹` is the polynomial ring in `T - T⁻¹`, over any
commutative coefficient ring. No division by two is needed: Dickson polynomials
express the pairs `Tⁿ + (-T⁻¹)ⁿ`. This gives polynomial descent for half-power
Seifert determinants, including matrices of odd size.

The decomposition into positive and negative powers follows the truncation argument
for ordinary inversion in `LaurentPolynomial.toLaurent_trunc_add_invert`.
-/

public section

noncomputable section

open LaurentPolynomial
open scoped Polynomial

namespace LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- The signed inversion homomorphism of Laurent polynomials, sending `T` to `-T⁻¹`
and fixing the coefficient ring. -/
def signedInvert : R[T;T⁻¹] →+* R[T;T⁻¹] :=
  eval₂ C (-(isUnit_T (R := R) 1).unit⁻¹)

@[simp] theorem signedInvert_C (r : R) : signedInvert (C r) = C r := by
  simp [signedInvert]

/-- Signed inversion multiplies a reflected monomial by its parity sign. -/
@[simp] theorem signedInvert_T (n : ℤ) :
    signedInvert (T n : R[T;T⁻¹]) = C ((-1 : R) ^ n.natAbs) * T (-n) := by
  have hinv : ((isUnit_T (R := R) 1).unit⁻¹ : R[T;T⁻¹]ˣ).val = T (-1) := by
    simpa using TauCeti.val_isUnit_T_unit_inv_pow (R := R) 1 1
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, signedInvert, eval₂_T, zpow_natCast, Units.val_pow_eq_pow_val,
      Units.val_neg, hinv, Int.natAbs_natCast]
    rw [neg_pow, T_pow]
    simp
  | negSucc n =>
    rw [signedInvert, eval₂_T, zpow_negSucc, ← inv_pow, inv_neg, inv_inv,
      Units.val_pow_eq_pow_val, Units.val_neg, IsUnit.unit_spec, neg_pow, T_pow]
    simp

/-- The coefficient of a signed-inverted Laurent polynomial is the reflected
coefficient with the parity sign. -/
@[simp] theorem coeff_signedInvert (p : R[T;T⁻¹]) (n : ℤ) :
    (signedInvert p).coeff n = (-1 : R) ^ n.natAbs * p.coeff (-n) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | C_mul_T k r =>
    rw [map_mul, signedInvert_C, signedInvert_T, ← mul_assoc, ← map_mul,
      ← single_eq_C_mul_T, ← single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : -k = n
    · subst n
      simp [mul_comm]
    · simp only [h, ↓reduceIte]
      split_ifs with hkn
      · omega
      · simp

/-- Signed inversion is an involution. -/
@[simp] theorem signedInvert_signedInvert (p : R[T;T⁻¹]) :
    signedInvert (signedInvert p) = p := by
  ext n
  simp only [coeff_signedInvert, neg_neg, Int.natAbs_neg, ← mul_assoc, ← mul_pow]
  simp

/-- The truncation and its signed reflection recover a fixed Laurent polynomial,
with its constant term counted once. -/
theorem toLaurent_trunc_add_signedInvert {p : R[T;T⁻¹]} (hp : signedInvert p = p) :
    (trunc p).toLaurent + signedInvert (trunc p).toLaurent - C (p.coeff 0) = p := by
  have hcoeff (n : ℤ) : (trunc p).toLaurent.coeff n =
      if 0 ≤ n then p.coeff n else 0 := by
    by_cases hn : 0 ≤ n
    · rw [ite_eq_left hn, ← Int.toNat_of_nonneg hn, coeff_toLaurent,
        ← Nat.castEmbedding_apply,
        Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective,
        Polynomial.toFinsupp_apply, coeff_trunc, Nat.castEmbedding_apply]
    · rw [ite_eq_right hn, coeff_toLaurent]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨k, hk⟩
      have hkn : (0 : ℤ) ≤ k := Int.natCast_nonneg k
      exact hn (hk ▸ hkn)
  ext n
  have hc := congrArg (fun q : R[T;T⁻¹] => q.coeff n) hp
  rw [coeff_signedInvert] at hc
  simp only [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.sub_apply,
    Finsupp.add_apply, coeff_signedInvert, hcoeff]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · simp [hn.not_ge, hn.le, hc, hn.ne]
  · simp
  · simp [hn.le, (not_le.mpr hn), hn.ne']

/-- A Laurent polynomial is fixed by signed inversion exactly when it is an ordinary
polynomial in `T - T⁻¹`. The result includes rings of characteristic two. -/
theorem signedInvert_eq_self_iff_exists_eval₂ (p : R[T;T⁻¹]) :
    signedInvert p = p ↔ ∃ q : R[X], Polynomial.eval₂ C (T 1 - T (-1)) q = p := by
  have hpair (n : ℕ) :
      Polynomial.eval₂ C (T 1 - T (-1)) (Polynomial.dickson 1 (-1 : R) n) =
        T (n : ℤ) + C ((-1 : R) ^ n) * T (-(n : ℤ)) := by
    have h := Polynomial.dickson_one_eval₂_add C (-1 : R)
      (T 1 : R[T;T⁻¹]) (-T (-1)) (by rw [mul_neg, ← T_add]; simp) n
    rw [neg_pow, T_pow, T_pow] at h
    simpa only [sub_eq_add_neg, neg_one_mul, Int.one_mul, neg_mul,
      map_pow, map_neg, map_one, mul_one, mul_neg_one] using h
  have hpoly (q : R[X]) : ∃ q' : R[X],
      Polynomial.eval₂ C (T 1 - T (-1)) q' =
        q.toLaurent + signedInvert q.toLaurent - C (q.coeff 0) := by
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      refine ⟨p' + q', ?_⟩
      simp only [Polynomial.eval₂_add, map_add, Polynomial.coeff_add, hp', hq']
      ring
    | monomial n r =>
      cases n with
      | zero => exact ⟨Polynomial.C r, by simp⟩
      | succ n =>
        refine ⟨Polynomial.C r * Polynomial.dickson 1 (-1 : R) (n + 1), ?_⟩
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hpair]
        simp only [Polynomial.toLaurent_C_mul_T, map_mul, signedInvert_C, signedInvert_T,
          Nat.cast_add, Nat.cast_one, Polynomial.coeff_monomial,
          Nat.succ_ne_zero, ↓reduceIte, map_zero, sub_zero, mul_add]
        simp only [← Nat.cast_add_one, Int.natAbs_natCast]
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := hpoly (trunc p)
    refine ⟨q, ?_⟩
    rw [hq, coeff_trunc]
    exact toLaurent_trunc_add_signedInvert hp
  · rintro ⟨q, rfl⟩
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp [Polynomial.eval₂_add, hp, hq]
    | monomial n r => simp [Polynomial.eval₂_monomial, sub_eq_add_neg, add_comm]

/-- A signed-inversion invariant is also a polynomial in `T⁻¹ - T`, the Conway variable. -/
theorem exists_eval₂_T_neg_sub_T {p : R[T;T⁻¹]} (hp : signedInvert p = p) :
    ∃ q : R[X], Polynomial.eval₂ C (T (-1) - T 1) q = p := by
  obtain ⟨q, hq⟩ := (signedInvert_eq_self_iff_exists_eval₂ p).mp hp
  refine ⟨q.comp (-Polynomial.X), ?_⟩
  simpa [Polynomial.eval₂_comp, neg_sub] using hq

end LaurentPolynomial
