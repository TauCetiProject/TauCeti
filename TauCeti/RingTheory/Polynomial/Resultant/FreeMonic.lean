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

import TauCeti.LinearAlgebra.Matrix.LeibnizPart

/-!
# The discriminant of the generic monic polynomial

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

The even and odd parts of the Vandermonde determinant also show that the discriminant of
every monic polynomial is a square modulo four. This uses Stickelberger's argument as
formalized in `TauCeti.NumberTheory.NumberField.Discriminant.Stickelberger`: the permanent and
the product of the two parts descend to the coefficients via Mathlib's
`MvPolynomial.esymmAlgEquiv`.

## Main results

* `Polynomial.map_aeval_coeff_freeMonic`: the free monic polynomial specializes to every monic
  polynomial `p` of degree `n` at `cᵢ = p.coeff i`.
* `Polynomial.map_aeval_esymm_freeMonic`: the free monic polynomial specializes to
  `∏ j, (X + X j)` at `cᵢ = eₙ₋ᵢ`.
* `Polynomial.prime_discr_freeMonic`: the discriminant of the free monic polynomial is prime.
* `Polynomial.Monic.exists_discr_eq_sq_sub_four_mul`: the discriminant of a monic polynomial
  is a square modulo four.

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

-- The substitution `cᵢ ↦ eₙ₋ᵢ` is an isomorphism onto the symmetric polynomials.
private noncomputable def freeMonicSymmetricEquiv (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n) R ≃ₐ[R] symmetricSubalgebra (Fin n) R :=
  (renameEquiv R Fin.revPerm).trans (esymmAlgEquiv (Fin n) R (Fintype.card_fin n))

private theorem coe_freeMonicSymmetricEquiv_apply {n : ℕ} (p : MvPolynomial (Fin n) R) :
    (freeMonicSymmetricEquiv R n p : MvPolynomial (Fin n) R) =
      MvPolynomial.aeval (fun i : Fin n ↦ esymm (Fin n) R (n - i)) p := by
  have he : (symmetricSubalgebra (Fin n) R).val.comp (freeMonicSymmetricEquiv R n).toAlgHom =
      MvPolynomial.aeval fun i : Fin n ↦ esymm (Fin n) R (n - i) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp only [freeMonicSymmetricEquiv, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.trans_apply, renameEquiv_apply, rename_X, Fin.revPerm_apply, esymmAlgEquiv_apply,
      Subalgebra.coe_val, esymmAlgHom_apply, MvPolynomial.aeval_X, Fin.val_rev]
    congr 1
    have := i.isLt
    omega
  simpa only [AlgHom.comp_apply, Subalgebra.coe_val, AlgEquiv.coe_toAlgHom]
    using DFunLike.congr_fun he p

private theorem coe_freeMonicSymmetricEquiv_discr (R : Type*) [CommRing R] (n : ℕ) :
    (freeMonicSymmetricEquiv R n (freeMonic R n).discr : MvPolynomial (Fin n) R) =
      (Matrix.vandermonde (MvPolynomial.X (R := R) (σ := Fin n))).det ^ 2 := by
  rw [coe_freeMonicSymmetricEquiv_apply]
  let φ := MvPolynomial.aeval (R := R) fun i : Fin n ↦ esymm (Fin n) R (n - i)
  have hmap : ((freeMonic R n).map φ.toRingHom).discr = φ (freeMonic R n).discr :=
    (monic_freeMonic R n).discr_map φ.toRingHom
  rw [← hmap]
  -- The roots of `∏ j, (X + X j)` are the `-X j`.
  have hprod : (freeMonic R n).map φ.toRingHom =
      ∏ j : Fin n, (X - C (-(MvPolynomial.X j : MvPolynomial (Fin n) R))) := by
    rw [map_aeval_esymm_freeMonic]
    simp
  rw [hprod, discr_prod_X_sub_C_eq_sq, Matrix.det_vandermonde]
  simp only [neg_sub_neg]

/-- **The generic discriminant is prime.** Over a domain in which `2 ≠ 0`, the discriminant of the
free monic polynomial `Xⁿ + cₙ₋₁ Xⁿ⁻¹ + ⋯ + c₀` of degree `n ≥ 2` is a prime element of
`R[c₀, …, cₙ₋₁]`. -/
theorem prime_discr_freeMonic [IsDomain R] (h2 : (2 : R) ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    Prime (freeMonic R n).discr := by
  rw [← MulEquiv.prime_iff (freeMonicSymmetricEquiv R n)]
  convert prime_vandermonde_sq h2 hn using 1
  apply Subtype.ext
  rw [coe_freeMonicSymmetricEquiv_discr, Matrix.det_vandermonde]

private theorem exists_discr_freeMonic_eq_sq_sub_four_mul (R : Type*) [CommRing R] (n : ℕ) :
    ∃ s t : MvPolynomial (Fin n) R, (freeMonic R n).discr = s ^ 2 - 4 * t := by
  let A := MvPolynomial (Fin n) R
  let M : Matrix (Fin n) (Fin n) A := Matrix.vandermonde (MvPolynomial.X (R := R))
  have hM (σ : Equiv.Perm (Fin n)) : M.map (rename σ) = M.submatrix σ id := by
    ext i j
    simp [M, Matrix.vandermonde_apply]
  have hS : M.permanent.IsSymmetric := fun σ ↦ by
    have hperm : (rename σ) M.permanent = (M.map (rename σ)).permanent := by
      simp [Matrix.permanent, map_sum, map_prod]
    rw [hperm, hM, Matrix.permanent_permute_cols]
  have hT : (M.leibnizPart 1 * M.leibnizPart (-1)).IsSymmetric := fun σ ↦ by
    rw [map_mul, ← Matrix.leibnizPart_map, ← Matrix.leibnizPart_map, hM,
      Matrix.leibnizPart_one_mul_leibnizPart_neg_one_submatrix_left]
  obtain ⟨s, hs⟩ := (freeMonicSymmetricEquiv R n).surjective ⟨_, hS⟩
  obtain ⟨t, ht⟩ := (freeMonicSymmetricEquiv R n).surjective ⟨_, hT⟩
  refine ⟨s, t, (freeMonicSymmetricEquiv R n).injective (Subtype.ext ?_)⟩
  rw [coe_freeMonicSymmetricEquiv_discr]
  have hfour : (↑(4 : symmetricSubalgebra (Fin n) R) : A) = 4 :=
    map_ofNat (symmetricSubalgebra (Fin n) R).val 4
  simpa [hs, ht, map_ofNat, hfour] using M.det_sq_eq_permanent_sq_sub_four_mul

/-- The discriminant of a monic polynomial is a square minus four times an element of its
coefficient ring. -/
theorem Monic.exists_discr_eq_sq_sub_four_mul {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) :
    ∃ s t : R, f.discr = s ^ 2 - 4 * t := by
  let φ := MvPolynomial.aeval (R := R) fun i : Fin f.natDegree ↦ f.coeff i
  obtain ⟨s, t, h⟩ := exists_discr_freeMonic_eq_sq_sub_four_mul R f.natDegree
  refine ⟨φ s, φ t, ?_⟩
  have hmap : (freeMonic R f.natDegree).map φ.toRingHom = f :=
    map_aeval_coeff_freeMonic hf rfl
  calc
    f.discr = ((freeMonic R f.natDegree).map φ.toRingHom).discr := congrArg discr hmap.symm
    _ = φ s ^ 2 - 4 * φ t := by
      rw [(monic_freeMonic R _).discr_map, h]
      simp [map_ofNat]

end Polynomial
