/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

import TauCeti.Algebra.Polynomial.Laurent.Basic
import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Laurent polynomials coming from polynomials

A Laurent polynomial comes from a polynomial exactly when all its negative coefficients
vanish. The same criterion applies to an algebra homomorphism with Laurent-polynomial values:
it factors through `Polynomial.toLaurent` exactly when all negative coefficients of its values
vanish, and such a factorization is unique because `Polynomial.toLaurent` is injective.

Multiplying by `T⁻¹` moves a polynomial `p` out of the image only by its constant coefficient:
`p T⁻¹ = divX p + p(0) T⁻¹`. Correspondingly, `T f` is a polynomial exactly when `f` is a
polynomial plus the multiple `f₋₁ T⁻¹` of `T⁻¹` by its coefficient of degree `-1`, and no nonzero
multiple of a negative power of `T` is a polynomial. In the `R[X]`-module `R[T;T⁻¹] ⧸ R[X]` of
principal parts, these say that multiplication by `X` is onto, with kernel spanned by the class
of `T⁻¹`.

## Main results

* `TauCeti.exists_toLaurent_eq_iff`: a Laurent polynomial lies in the image of
  `Polynomial.toLaurent` iff its negative coefficients vanish.
* `TauCeti.exists_algHom_toLaurent_comp_eq_iff`: the same criterion for a Laurent-valued
  algebra homomorphism to factor through `Polynomial.toLaurentAlg`.
* `LaurentPolynomial.isScalarTower_polynomial`: the scalar tower `R → R[X] → R[T;T⁻¹]` along
  `Polynomial.toLaurent`.
* `LaurentPolynomial.smul_eq_toLaurent_mul`: polynomials act on Laurent polynomials by
  multiplication.
* `Polynomial.toLaurent_mul_T_neg_one`: `p T⁻¹ = divX p + p(0) T⁻¹`.
* `LaurentPolynomial.C_mul_T_eq_toLaurent_iff`: `a Tⁿ` with `n < 0` is a polynomial only when
  `a = 0`.
* `LaurentPolynomial.T_one_mul_mem_range_toLaurent_iff`: `T f` is a polynomial exactly when
  `f - f₋₁ T⁻¹` is.
-/

public section

namespace TauCeti

variable {R A H : Type*}

/-- A Laurent polynomial comes from a polynomial exactly when its negative coefficients vanish. -/
@[simp]
theorem exists_toLaurent_eq_iff [Semiring A] {p : LaurentPolynomial A} :
    (∃ q : Polynomial A, q.toLaurent = p) ↔ ∀ n : ℤ, n < 0 → p.coeff n = 0 := by
  have hrange : p ∈ Set.range Polynomial.toLaurent ↔
      p.coeff ∈ Set.range (Finsupp.mapDomain (Nat.cast : ℕ → ℤ)) :=
    ⟨fun ⟨q, hq⟩ ↦ ⟨q.coeff, congrArg AddMonoidAlgebra.coeff hq⟩,
      fun ⟨q, hq⟩ ↦ ⟨.ofCoeff q, AddMonoidAlgebra.coeff_injective hq⟩⟩
  rw [← Set.mem_range, hrange, Finsupp.mem_range_mapDomain_iff _ Nat.cast_injective]
  refine forall_congr' fun n ↦ imp_congr_left ?_
  rw [not_iff_comm, not_lt]
  exact ⟨fun hn ↦ ⟨n.toNat, by omega⟩, by rintro ⟨m, rfl⟩; omega⟩

variable [CommSemiring R] [CommSemiring A] [Semiring H]
variable [Algebra R A] [Algebra R H]

/-- A Laurent-valued algebra homomorphism extends to polynomial values exactly when all its
negative coefficients vanish. -/
theorem exists_algHom_toLaurent_comp_eq_iff {f : H →ₐ[R] LaurentPolynomial A} :
    (∃ F : H →ₐ[R] Polynomial A,
      (Polynomial.toLaurentAlg.restrictScalars R).comp F = f) ↔
      ∀ h : H, ∀ n : ℤ, n < 0 → (f h).coeff n = 0 := by
  constructor
  · rintro ⟨F, rfl⟩ h
    exact exists_toLaurent_eq_iff.mp ⟨F h, rfl⟩
  · intro hf
    let i : Polynomial A →ₐ[R] LaurentPolynomial A :=
      Polynomial.toLaurentAlg.restrictScalars R
    let e := AlgEquiv.ofInjective i Polynomial.toLaurent_injective
    let F := e.symm.toAlgHom.comp (f.codRestrict i.range fun h ↦
      exists_toLaurent_eq_iff.mpr (hf h))
    exact ⟨F, AlgHom.ext fun h ↦ congrArg Subtype.val (e.apply_symm_apply _)⟩

end TauCeti

namespace LaurentPolynomial

open Polynomial

/-- The scalar tower `R → R[X] → R[T;T⁻¹]`, along `Polynomial.toLaurent`. -/
instance isScalarTower_polynomial (R : Type*) [CommSemiring R] :
    IsScalarTower R R[X] R[T;T⁻¹] :=
  .of_algebraMap_eq fun r ↦ by simp [← C_eq_algebraMap]

variable {R : Type*} [Semiring R]

/-- A polynomial acts on Laurent polynomials by multiplication through `Polynomial.toLaurent`. -/
theorem smul_eq_toLaurent_mul (p : R[X]) (f : R[T;T⁻¹]) : p • f = toLaurent p * f :=
  (rfl)

/-- The variable `X` acts on Laurent polynomials as multiplication by `T 1`. -/
theorem X_smul_eq_T_one_mul (f : R[T;T⁻¹]) : (X : R[X]) • f = T 1 * f := by
  rw [smul_eq_toLaurent_mul, toLaurent_X]

/-- Multiplying a polynomial `p` by `T⁻¹` gives the polynomial `divX p` plus the multiple
`p(0) T⁻¹` of `T⁻¹`. -/
theorem _root_.Polynomial.toLaurent_mul_T_neg_one (p : R[X]) :
    toLaurent p * T (-1) = toLaurent p.divX + C (p.coeff 0) * T (-1) := by
  conv_lhs => rw [← X_mul_divX_add p]
  rw [map_add, map_mul, toLaurent_X, toLaurent_C, add_mul, T_mul_mul_T_neg]

/-- A multiple `a Tⁿ` of a negative power of `T` is a polynomial only when it vanishes. -/
theorem C_mul_T_eq_toLaurent_iff {n : ℤ} (hn : n < 0) {a : R} {p : R[X]} :
    C a * T n = toLaurent p ↔ a = 0 ∧ p = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hp⟩ ↦ by simp [ha, hp]⟩
  have ha : a = 0 := by
    have := TauCeti.exists_toLaurent_eq_iff.mp ⟨p, h.symm⟩ n hn
    rwa [coeff_C_mul_T, ite_eq_left rfl] at this
  subst ha
  exact ⟨rfl, by simpa using h.symm⟩

/-- `T f` is a polynomial exactly when `f` is a polynomial plus the multiple `f₋₁ T⁻¹` of `T⁻¹`
by its coefficient of degree `-1`. -/
theorem T_one_mul_mem_range_toLaurent_iff {f : R[T;T⁻¹]} :
    T 1 * f ∈ Set.range (toLaurent : R[X] → R[T;T⁻¹]) ↔
      ∃ p : R[X], toLaurent p + C (f.coeff (-1)) * T (-1) = f := by
  constructor
  · rintro ⟨q, hq⟩
    have hf : f = toLaurent q.divX + C (q.coeff 0) * T (-1) := by
      rw [← toLaurent_mul_T_neg_one, hq, T_mul_mul_T_neg]
    have hcoeff : f.coeff (-1) = q.coeff 0 := by
      simp [hf, Finsupp.mapDomain_of_notMem_range]
    exact ⟨q.divX, by rw [hcoeff, ← hf]⟩
  · rintro ⟨p, hp⟩
    refine ⟨X * p + Polynomial.C (f.coeff (-1)), ?_⟩
    generalize f.coeff (-1) = a at hp ⊢
    rw [← hp, map_add, map_mul, toLaurent_X, toLaurent_C, mul_add, ← mul_assoc,
      T_mul_mul_T_neg]

end LaurentPolynomial
