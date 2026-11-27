/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The coefficients of `∏ⱼ (T - Xⱼ)` as coordinates on the symmetric polynomials

Let `X₀, …, X_{n-1}` be the variables of `R[X₀, …, X_{n-1}]`. The coefficient of `T^k` in
`∏ⱼ (T - Xⱼ)` is `(-1)^(n - k) e_{n - k}` (`MvPolynomial.coeff_prod_X_sub_C_X`), with `e_m` the
elementary symmetric polynomial. The algebra map `MvPolynomial.vietaAlgHom R n` sending `Xᵢ` to the
coefficient of `T^i`, for `i < n`, is therefore the fundamental theorem of symmetric polynomials up
to reindexing and signs: it is injective (`MvPolynomial.vietaAlgHom_injective`) and its range is
the symmetric subalgebra (`MvPolynomial.range_vietaAlgHom`).

This is the form in which the coefficients of a characteristic polynomial `det(T - g)` appear:
restricted to the diagonal matrices with entries `X₀, …, X_{n-1}`, the coefficients of the
characteristic polynomial are the coefficients of `∏ⱼ (T - Xⱼ)`.

## Main declarations

* `MvPolynomial.vietaAlgHom`: `Xᵢ ↦` the coefficient of `T^i` in `∏ⱼ (T - Xⱼ)`.
* `MvPolynomial.vietaAlgHom_injective`, `MvPolynomial.range_vietaAlgHom`: it is an isomorphism
  onto the symmetric polynomials.
-/

public section

namespace MvPolynomial

variable (R : Type*) [CommRing R] (n : ℕ)

/-- **Vieta's formulas** in `n` variables: the coefficient of `T^k` in `∏ⱼ (T - Xⱼ)` is
`(-1)^(n - k) e_{n - k}`. -/
theorem coeff_prod_X_sub_C_X {k : ℕ} (hk : k ≤ n) :
    (∏ j : Fin n, (Polynomial.X - Polynomial.C (X j : MvPolynomial (Fin n) R))).coeff k =
      (-1) ^ (n - k) * esymm (Fin n) R (n - k) := by
  have h := Multiset.prod_X_sub_C_coeff
    (Finset.univ.val.map (X : Fin n → MvPolynomial (Fin n) R)) (k := k) (by simpa using hk)
  rw [Multiset.map_map] at h
  simpa [esymm_eq_multiset_esymm, Finset.prod_eq_multiset_prod] using h

/-- The algebra map sending `Xᵢ`, for `i < n`, to the coefficient of `T^i` in `∏ⱼ (T - Xⱼ)`. -/
noncomputable def vietaAlgHom : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval fun i : Fin n ↦
    (∏ j : Fin n, (Polynomial.X - Polynomial.C (X j : MvPolynomial (Fin n) R))).coeff i

/-- `vietaAlgHom` sends `Xᵢ` to the coefficient of `T^i` in `∏ⱼ (T - Xⱼ)`. -/
@[simp]
theorem vietaAlgHom_X (i : Fin n) :
    vietaAlgHom R n (X i) =
      (∏ j : Fin n, (Polynomial.X - Polynomial.C (X j : MvPolynomial (Fin n) R))).coeff i :=
  aeval_X _ _

/-- The signed reversal `Xᵢ ↦ (-1)^(n - i) X_{n-1-i}`, relating `vietaAlgHom` to Mathlib's
`esymmAlgHom`. -/
private noncomputable def signRev : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval fun i : Fin n ↦ C ((-1) ^ (n - i : ℕ)) * X (Fin.rev i)

/-- The inverse of `signRev`. -/
private noncomputable def signRevInv : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval fun i : Fin n ↦ C ((-1) ^ (n - (Fin.rev i : ℕ))) * X (Fin.rev i)

private theorem neg_one_pow_mul_self (a : ℕ) : ((-1 : R) ^ a) * (-1) ^ a = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem signRevInv_comp_signRev :
    (signRevInv R n).comp (signRev R n) = AlgHom.id R _ := by
  ext i : 1
  rw [AlgHom.comp_apply, signRev, aeval_X, map_mul, signRevInv, aeval_C, aeval_X, Fin.rev_rev,
    algebraMap_eq, ← mul_assoc, ← map_mul, neg_one_pow_mul_self, map_one, one_mul,
    AlgHom.id_apply]

private theorem signRev_comp_signRevInv :
    (signRev R n).comp (signRevInv R n) = AlgHom.id R _ := by
  ext i : 1
  rw [AlgHom.comp_apply, signRevInv, aeval_X, map_mul, signRev, aeval_C, aeval_X, Fin.rev_rev,
    algebraMap_eq, ← mul_assoc, ← map_mul, neg_one_pow_mul_self, map_one, one_mul,
    AlgHom.id_apply]

private theorem vietaAlgHom_eq :
    vietaAlgHom R n =
      ((symmetricSubalgebra (Fin n) R).val.comp (esymmAlgHom (Fin n) R n)).comp (signRev R n) := by
  ext i : 1
  have hi : n - (i : ℕ) = (Fin.rev i : ℕ) + 1 := by rw [Fin.val_rev]; omega
  simp [vietaAlgHom, signRev, esymmAlgHom, coeff_prod_X_sub_C_X R n i.is_lt.le, hi]

/-- **The coefficients of `∏ⱼ (T - Xⱼ)` are algebraically independent.** -/
theorem vietaAlgHom_injective : Function.Injective (vietaAlgHom R n) := by
  rw [vietaAlgHom_eq, AlgHom.coe_comp, AlgHom.coe_comp]
  refine (Subtype.val_injective.comp
    (esymmAlgHom_injective (σ := Fin n) R (Fintype.card_fin n).ge)).comp ?_
  exact Function.LeftInverse.injective (g := signRevInv R n)
    fun x ↦ AlgHom.congr_fun (signRevInv_comp_signRev R n) x

/-- **The coefficients of `∏ⱼ (T - Xⱼ)` generate the symmetric polynomials.** -/
theorem range_vietaAlgHom : (vietaAlgHom R n).range = symmetricSubalgebra (Fin n) R := by
  ext p
  refine ⟨fun ⟨q, hq⟩ ↦ hq ▸ ?_, fun hp ↦ ?_⟩
  · rw [vietaAlgHom_eq]
    exact Subtype.property _
  · obtain ⟨q, hq⟩ :=
      esymmAlgHom_surjective (σ := Fin n) (n := n) R (Fintype.card_fin n).le ⟨p, hp⟩
    refine ⟨signRevInv R n q, ?_⟩
    change vietaAlgHom R n (signRevInv R n q) = p
    rw [vietaAlgHom_eq, AlgHom.comp_apply, AlgHom.comp_apply,
      ← AlgHom.comp_apply (signRev R n), signRev_comp_signRevInv, AlgHom.id_apply, hq]
    rfl

end MvPolynomial
