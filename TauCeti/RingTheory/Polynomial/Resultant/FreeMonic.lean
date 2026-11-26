/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Polynomial.Vieta
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Discriminant
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The discriminant of the generic monic polynomial is prime

Mathlib's `Polynomial.freeMonic R n` is the generic monic polynomial
`Xⁿ + cₙ₋₁ Xⁿ⁻¹ + ⋯ + c₀` of degree `n` over `R[c₀, …, cₙ₋₁]`. Substituting for `cᵢ` the elementary
symmetric polynomial `eₙ₋ᵢ` of `n` new variables turns it into `∏ j, (X + X j)`
(`Polynomial.map_aeval_esymm_freeMonic`), whose discriminant is the square of the Vandermonde
product of the variables. By the fundamental theorem of symmetric polynomials this substitution
is an isomorphism onto the symmetric polynomials, and there the squared Vandermonde product is
prime (`MvPolynomial.prime_vandermonde_sq`). Hence, over a domain in which `2 ≠ 0`, the
discriminant of the generic monic polynomial of degree `n ≥ 2` is prime
(`Polynomial.prime_discr_freeMonic`).

The hypotheses are needed: for `n ≤ 1` the discriminant is `1`, a unit; in characteristic `2` the
discriminant `c₁ ^ 2 - 4 c₀` of `X ^ 2 + c₁ X + c₀` is the square `c₁ ^ 2`.

## Main results

* `Polynomial.map_aeval_coeff_freeMonic`: the free monic polynomial specializes to every monic
  polynomial `p` of degree `n` at `cᵢ = p.coeff i`.
* `Polynomial.map_aeval_esymm_freeMonic`: the free monic polynomial specializes to
  `∏ j, (X + X j)` at `cᵢ = eₙ₋ᵢ`.
* `Polynomial.prime_discr_freeMonic`: the discriminant of the free monic polynomial is prime.

-/

public section

open MvPolynomial Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The free monic polynomial of degree `n` specializes to every monic polynomial `p` of degree
`n`, at `cᵢ = p.coeff i`. -/
theorem map_aeval_coeff_freeMonic {S : Type*} [CommRing S] [Algebra R S] {n : ℕ} {p : S[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) :
    (freeMonic R n).map (MvPolynomial.aeval fun i : Fin n ↦ p.coeff i).toRingHom = p := by
  ext i
  rw [coeff_map, coeff_freeMonic]
  split_ifs with hi hin
  · simp
  · rw [map_one, hin, ← hdeg, hp.coeff_natDegree]
  · rw [map_zero, coeff_eq_zero_of_natDegree_lt (by lia)]

/-- **Vieta's formulas for the free monic polynomial.** Substituting the elementary symmetric
polynomial `eₙ₋ᵢ` of `n` variables for the coefficient `cᵢ` of `Xⁱ` in the free monic polynomial
of degree `n` gives `∏ j, (X + X j)`. -/
theorem map_aeval_esymm_freeMonic (n : ℕ) :
    (freeMonic R n).map (MvPolynomial.aeval fun i : Fin n ↦ esymm (Fin n) R (n - i)).toRingHom =
      ∏ j : Fin n, (X + C (MvPolynomial.X j)) := by
  nontriviality R
  have hmonic : (∏ j : Fin n, (X + C (MvPolynomial.X j : MvPolynomial (Fin n) R))).Monic :=
    monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _
  have hdeg : (∏ j : Fin n, (X + C (MvPolynomial.X j : MvPolynomial (Fin n) R))).natDegree = n := by
    simp [natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _]
  convert map_aeval_coeff_freeMonic hmonic hdeg using 4
  ext i : 1
  rw [prod_X_add_C_coeff _ _ _ (by simp [i.isLt.le]), Fintype.card_fin]

/-- **The generic discriminant is prime.** Over a domain in which `2 ≠ 0`, the discriminant of the
free monic polynomial `Xⁿ + cₙ₋₁ Xⁿ⁻¹ + ⋯ + c₀` of degree `n ≥ 2` is a prime element of
`R[c₀, …, cₙ₋₁]`. -/
theorem prime_discr_freeMonic [IsDomain R] (h2 : (2 : R) ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    Prime (freeMonic R n).discr := by
  -- The substitution `cᵢ ↦ eₙ₋ᵢ` is an isomorphism onto the symmetric polynomials.
  let e : MvPolynomial (Fin n) R ≃ₐ[R] symmetricSubalgebra (Fin n) R :=
    (renameEquiv R Fin.revPerm).trans (esymmAlgEquiv (Fin n) R (Fintype.card_fin n))
  have he : (symmetricSubalgebra (Fin n) R).val.comp e.toAlgHom =
      MvPolynomial.aeval fun i : Fin n ↦ esymm (Fin n) R (n - i) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp only [e, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply, renameEquiv_apply,
      rename_X, Fin.revPerm_apply, esymmAlgEquiv_apply, Subalgebra.coe_val, esymmAlgHom_apply,
      MvPolynomial.aeval_X, Fin.val_rev]
    congr 1
    have := i.isLt
    omega
  rw [← MulEquiv.prime_iff e]
  convert prime_vandermonde_sq h2 hn using 1
  apply Subtype.ext
  have h := DFunLike.congr_fun he (freeMonic R n).discr
  simp only [AlgHom.comp_apply, Subalgebra.coe_val, AlgEquiv.coe_toAlgHom] at h
  rw [h]
  have hmap := (monic_freeMonic R n).discr_map
    (MvPolynomial.aeval fun i : Fin n ↦ esymm (Fin n) R (n - i)).toRingHom
  rw [map_aeval_esymm_freeMonic, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hmap
  rw [← hmap]
  -- The roots of `∏ j, (X + X j)` are the `-X j`.
  have hprod : ∏ j : Fin n, (X + C (MvPolynomial.X j : MvPolynomial (Fin n) R)) =
      ∏ j : Fin n, (X - C (-MvPolynomial.X j)) := by
    simp [sub_eq_add_neg]
  rw [hprod, discr_prod_X_sub_C_eq_sq]
  simp [neg_add_eq_sub]

end Polynomial
