/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Polynomials evaluated at `ε`

Since `ε² = 0`, evaluating a polynomial `p` at the dual-number unit `ε` keeps only its first two
coefficients: the classical part of `p(ε)` is the constant coefficient of `p` and its
infinitesimal part is the linear coefficient.

Evaluation at `ε` kills `X²`, and over a commutative ring it identifies the quotient `R[X] ⧸ (X²)`
with the dual numbers, the class of `X` going to `ε`. Rings presented as such quotients, such as
the truncated polynomial ring `k[t] ⧸ (t²)` of the cusp `k[t², t³]`, thereby inherit the API of
`R[ε]`.

## Main definitions

* `TauCeti.dualNumberPolynomialQuotientAlgEquiv`: the `R`-algebra isomorphism
  `R[X] ⧸ (X²) ≃ₐ[R] R[ε]` induced by evaluation at `ε`.

## Main results

* `TauCeti.isLocalRing_polynomialQuotientSpanXSq`: over a field `K`, the ring `K[X] ⧸ (X²)` is
  local, like `K[ε]`.
* `TauCeti.isMulCommutative_units_polynomialQuotientSpanXSq`: the units of `R[X] ⧸ (X²)` commute,
  so every subgroup of them is normal.
-/

public section

open Polynomial

namespace DualNumber

section Eval

variable {R B : Type*} [CommSemiring R] [CommRing B] [Algebra R B]

/-- A polynomial evaluated at `ε` is its constant coefficient plus its linear coefficient
times `ε`. -/
theorem aeval_eps (p : R[X]) :
    aeval (eps : DualNumber B) p =
      TrivSqZeroExt.inl (algebraMap R B (p.coeff 0)) +
        TrivSqZeroExt.inr (algebraMap R B (p.coeff 1)) := by
  rw [← zero_add (eps : DualNumber B),
    aeval_add_of_sq_eq_zero _ _ _ (by rw [sq, eps_mul_eps]),
    ← coeff_zero_eq_aeval_zero', ← coeff_zero_eq_aeval_zero']
  ext <;> simp [coeff_derivative, Algebra.algebraMap_eq_smul_one]

/-- The classical part of a polynomial evaluated at `ε` is its constant coefficient. -/
@[simp]
theorem fst_aeval_eps (p : R[X]) :
    (aeval (eps : DualNumber B) p).fst = algebraMap R B (p.coeff 0) := by
  simp [aeval_eps]

/-- The infinitesimal part of a polynomial evaluated at `ε` is its linear coefficient. -/
@[simp]
theorem snd_aeval_eps (p : R[X]) :
    (aeval (eps : DualNumber B) p).snd = algebraMap R B (p.coeff 1) := by
  simp [aeval_eps, Algebra.algebraMap_eq_smul_one]

end Eval

end DualNumber

namespace TauCeti

open DualNumber

section Quotient

variable (R : Type*) [CommRing R]

/-- Evaluation at `ε` kills the ideal `(X²)`. -/
private theorem aeval_eps_eq_zero_of_mem {p : R[X]} (hp : p ∈ Ideal.span {(X : R[X]) ^ 2}) :
    aeval (eps : DualNumber R) p = 0 := by
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hp
  simp

/-- The class of `X` squares to zero in `R[X] ⧸ (X²)`. -/
private theorem mk_X_mul_mk_X :
    Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ 2}) X *
      Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ 2}) X = 0 := by
  rw [← map_mul, ← sq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- **The dual numbers as a polynomial quotient.** Evaluation at `ε` identifies `R[X] ⧸ (X²)` with
the dual numbers `R[ε]`, the class of `X` going to `ε`; the inverse sends `ε` to the class of
`X`. -/
noncomputable def dualNumberPolynomialQuotientAlgEquiv :
    (R[X] ⧸ Ideal.span {(X : R[X]) ^ 2}) ≃ₐ[R] DualNumber R :=
  AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ _ (aeval eps) fun _ ↦ aeval_eps_eq_zero_of_mem R)
    (DualNumber.lift
      ⟨(Algebra.ofId R _, Ideal.Quotient.mk _ X), mk_X_mul_mk_X R, fun _ ↦ Commute.all _ _⟩)
    (DualNumber.algHom_ext (by
      simp only [AlgHom.comp_apply, lift_apply_eps, AlgHom.id_apply]
      rw [← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp, aeval_X]))
    (Ideal.Quotient.algHom_ext R (Polynomial.algHom_ext (by
      rw [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
      simp)))

variable {R}

/-- `TauCeti.dualNumberPolynomialQuotientAlgEquiv` sends the class of `p` to `p(ε)`. -/
@[simp]
theorem _root_.Polynomial.dualNumberPolynomialQuotientAlgEquiv_mk (p : R[X]) :
    dualNumberPolynomialQuotientAlgEquiv R (Ideal.Quotient.mk _ p) = aeval eps p := by
  rw [dualNumberPolynomialQuotientAlgEquiv, AlgEquiv.ofAlgHom_apply, ← Ideal.Quotient.mkₐ_eq_mk R,
    ← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp]

/-- The inverse of `TauCeti.dualNumberPolynomialQuotientAlgEquiv` sends `a + bε` to the class of
`a + bX`. -/
theorem _root_.DualNumber.dualNumberPolynomialQuotientAlgEquiv_symm_apply (z : DualNumber R) :
    (dualNumberPolynomialQuotientAlgEquiv R).symm z =
      Ideal.Quotient.mk _ (C z.fst + C z.snd * X) := by
  rw [AlgEquiv.symm_apply_eq, Polynomial.dualNumberPolynomialQuotientAlgEquiv_mk]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

variable (R)

/-- The inverse of `TauCeti.dualNumberPolynomialQuotientAlgEquiv` sends `ε` to the class of
`X`. -/
@[simp]
theorem dualNumberPolynomialQuotientAlgEquiv_symm_eps :
    (dualNumberPolynomialQuotientAlgEquiv R).symm eps = Ideal.Quotient.mk _ X := by
  rw [AlgEquiv.symm_apply_eq, Polynomial.dualNumberPolynomialQuotientAlgEquiv_mk, aeval_X]

/-- Over a field `K`, the ring `K[X] ⧸ (X²)` is local, like the dual numbers `K[ε]`. -/
instance isLocalRing_polynomialQuotientSpanXSq (K : Type*) [Field K] :
    IsLocalRing (K[X] ⧸ Ideal.span {(X : K[X]) ^ 2}) :=
  (dualNumberPolynomialQuotientAlgEquiv K).symm.toRingEquiv.isLocalRing

/-- The units of `R[X] ⧸ (X²)` commute, so every subgroup of them is normal. Instance search does
not find this through the commutative ring structure of the quotient unaided. -/
instance isMulCommutative_units_polynomialQuotientSpanXSq :
    IsMulCommutative (R[X] ⧸ Ideal.span {(X : R[X]) ^ 2})ˣ :=
  CommMagma.to_isCommutative (G := (R[X] ⧸ Ideal.span {(X : R[X]) ^ 2})ˣ)

end Quotient

end TauCeti
