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
* `MvPolynomial.vietaAlgHom_injective`, `MvPolynomial.range_vietaAlgHom`: it is an isomorphism
  onto the symmetric polynomials.
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

end MvPolynomial
