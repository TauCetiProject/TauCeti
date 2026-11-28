/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.Polynomial.Coeff
import TauCeti.RingTheory.Polynomial.Vieta

/-!
# The coefficients of `∏ⱼ (T - Xⱼ)` as coordinates on the symmetric polynomials

For a finite type `σ`, the coefficient of `T^k` in `∏ⱼ (T - Xⱼ)` over `R[Xⱼ : j ∈ σ]` is
`(-1)^(|σ| - k) e_{|σ| - k}`, with `e_m` the elementary symmetric polynomial
(`MvPolynomial.prod_X_sub_C_coeff`, in `TauCeti.RingTheory.Polynomial.Vieta`). For `σ = Fin n`,
the algebra map `MvPolynomial.vietaAlgHom R n` of `R[X₀, …, X_{n-1}]` sending `Xᵢ` to the
coefficient of `T^i`, for `i < n`, is therefore the fundamental theorem of symmetric polynomials
up to reindexing and signs: it is injective (`MvPolynomial.vietaAlgHom_injective`)
and its range is the symmetric subalgebra (`MvPolynomial.range_vietaAlgHom`).

This is the form in which the coefficients of a characteristic polynomial `det(T - g)` appear:
restricted to the diagonal matrices with entries `X₀, …, X_{n-1}`, the coefficients of the
characteristic polynomial are the coefficients of `∏ⱼ (T - Xⱼ)`.

## Main declarations

* `MvPolynomial.vietaAlgHom`: `Xᵢ ↦` the coefficient of `T^i` in `∏ⱼ (T - Xⱼ)`.
* `MvPolynomial.vietaAlgHom_injective`, `MvPolynomial.range_vietaAlgHom`,
  `MvPolynomial.vietaAlgEquiv`, `MvPolynomial.mem_range_vietaAlgHom_iff`,
  `MvPolynomial.isUnit_of_isUnit_vietaAlgHom`: it is an isomorphism onto the symmetric
  polynomials and reflects units.
-/

public section

namespace MvPolynomial

variable (R : Type*) [CommRing R] (n : ℕ)

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

private theorem signRevInv_comp_signRev :
    (signRevInv R n).comp (signRev R n) = AlgHom.id R _ := by
  ext i : 1
  simp [signRev, signRevInv, -Fin.val_rev, ← mul_assoc, ← mul_pow]

private theorem signRev_comp_signRevInv :
    (signRev R n).comp (signRevInv R n) = AlgHom.id R _ := by
  ext i : 1
  simp [signRev, signRevInv, -Fin.val_rev, ← mul_assoc, ← mul_pow]

private theorem vietaAlgHom_eq :
    vietaAlgHom R n =
      ((symmetricSubalgebra (Fin n) R).val.comp (esymmAlgHom (Fin n) R n)).comp (signRev R n) := by
  ext i : 1
  have hi : n - (i : ℕ) = (Fin.rev i : ℕ) + 1 := by rw [Fin.val_rev]; omega
  simp [vietaAlgHom, signRev, esymmAlgHom,
    prod_X_sub_C_coeff R (Fin n) (k := i) (by simp), hi]

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
    refine (AlgHom.mem_range _).2 ⟨signRevInv R n q, ?_⟩
    simp [vietaAlgHom_eq, ← AlgHom.comp_apply (signRev R n), signRev_comp_signRevInv, hq]

/-- Vieta's `R`-algebra isomorphism from `MvPolynomial (Fin n) R` onto
`symmetricSubalgebra (Fin n) R`. -/
noncomputable def vietaAlgEquiv :
    MvPolynomial (Fin n) R ≃ₐ[R] symmetricSubalgebra (Fin n) R :=
  (AlgEquiv.ofInjective (vietaAlgHom R n) (vietaAlgHom_injective R n)).trans
    (Subalgebra.equivOfEq _ _ (range_vietaAlgHom R n))

/-- Applying `MvPolynomial.vietaAlgHom` returns the underlying symmetric polynomial of
`MvPolynomial.vietaAlgEquiv`. -/
theorem vietaAlgHom_apply {R : Type*} [CommRing R] {n : ℕ} (p : MvPolynomial (Fin n) R) :
    vietaAlgHom R n p = (vietaAlgEquiv R n p : MvPolynomial (Fin n) R) := by
  simp [vietaAlgEquiv]

/-- Every polynomial in the image of `MvPolynomial.vietaAlgHom` is symmetric. -/
theorem isSymmetric_vietaAlgHom {R : Type*} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) : (vietaAlgHom R n p).IsSymmetric :=
  (vietaAlgEquiv R n p).property

/-- A polynomial in `MvPolynomial (Fin n) R` lies in the range of `MvPolynomial.vietaAlgHom` if
and only if it is symmetric. -/
theorem mem_range_vietaAlgHom_iff {R : Type*} [CommRing R] {n : ℕ}
    {q : MvPolynomial (Fin n) R} :
    q ∈ Set.range (vietaAlgHom R n) ↔ q.IsSymmetric := by
  rw [Set.mem_range, ← AlgHom.mem_range, range_vietaAlgHom, mem_symmetricSubalgebra]

/-- On variables, `MvPolynomial.vietaAlgHom` sends `X i` to the signed elementary symmetric
polynomial `(-1) ^ (n - i) * esymm (Fin n) R (n - i)`. -/
theorem vietaAlgHom_X_eq_esymm {R : Type*} [CommRing R] {n : ℕ} (i : Fin n) :
    vietaAlgHom R n (X i) =
      (-1) ^ (n - (i : ℕ)) * esymm (Fin n) R (n - (i : ℕ)) := by
  rw [vietaAlgHom_X, prod_X_sub_C_coeff R (Fin n) (by simp), Fintype.card_fin]

/-- On variables, `MvPolynomial.vietaAlgEquiv` sends `X i` to the signed elementary symmetric
polynomial `(-1) ^ (n - i) * esymm (Fin n) R (n - i)` in `symmetricSubalgebra (Fin n) R`. -/
@[simp]
theorem vietaAlgEquiv_X {R : Type*} [CommRing R] {n : ℕ} (i : Fin n) :
    vietaAlgEquiv R n (X i) =
      ⟨(-1) ^ (n - (i : ℕ)) * esymm (Fin n) R (n - (i : ℕ)), by
        rw [← vietaAlgHom_X_eq_esymm]
        exact isSymmetric_vietaAlgHom (X i)⟩ :=
  Subtype.ext (vietaAlgHom_X_eq_esymm i)

/-- The inverse of `MvPolynomial.vietaAlgEquiv` maps the elementary symmetric generator
`esymm (Fin n) R (j + 1)` to `(-1) ^ (j + 1) * X j.rev`. -/
@[simp]
theorem vietaAlgEquiv_symm_esymm {R : Type*} [CommRing R] {n : ℕ} (j : Fin n) :
    (vietaAlgEquiv R n).symm ⟨esymm (Fin n) R (j + 1), esymm_isSymmetric (Fin n) R _⟩ =
      (-1) ^ ((j : ℕ) + 1) * X j.rev := by
  rw [AlgEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [← vietaAlgHom_apply, map_mul, map_pow, map_neg, map_one, vietaAlgHom_X_eq_esymm, Fin.val_rev]
  have hj := j.isLt
  have hj' : n - (n - ((j : ℕ) + 1)) = (j : ℕ) + 1 := by omega
  rw [hj', ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- `MvPolynomial.vietaAlgHom R n` reflects units. -/
theorem isUnit_of_isUnit_vietaAlgHom {R : Type*} [CommRing R] {n : ℕ}
    {b : MvPolynomial (Fin n) R} (hb : IsUnit (vietaAlgHom R n b)) : IsUnit b := by
  obtain ⟨c, hc⟩ := hb.exists_right_inv
  have hc_symm : c.IsSymmetric := by
    intro e
    have h1 : vietaAlgHom R n b * rename e c = 1 := by
      have h := congrArg (rename e) hc
      rw [map_mul, map_one, isSymmetric_vietaAlgHom b e] at h
      exact h
    calc rename e c = (c * vietaAlgHom R n b) * rename e c := by
          rw [mul_comm c, hc, one_mul]
      _ = c * (vietaAlgHom R n b * rename e c) := mul_assoc _ _ _
      _ = c := by rw [h1, mul_one]
  obtain ⟨d, hd⟩ := mem_range_vietaAlgHom_iff.mpr hc_symm
  have hbd : b * d = 1 := vietaAlgHom_injective R n (by rw [map_mul, map_one, hd, hc])
  exact IsUnit.of_mul_eq_one d hbd

end MvPolynomial
