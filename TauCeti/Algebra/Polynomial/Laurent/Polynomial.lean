/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Laurent polynomials coming from polynomials

A Laurent polynomial comes from a polynomial exactly when all its negative coefficients
vanish. The same criterion applies to an algebra homomorphism with Laurent-polynomial values:
it factors through `Polynomial.toLaurent` exactly when all negative coefficients of its values
vanish, and such a factorization is unique because `Polynomial.toLaurent` is injective.

## Main results

* `TauCeti.exists_toLaurent_eq_iff`: a Laurent polynomial lies in the image of
  `Polynomial.toLaurent` iff its negative coefficients vanish.
* `TauCeti.exists_algHom_toLaurent_comp_eq_iff`: the same criterion for a Laurent-valued
  algebra homomorphism to factor through `Polynomial.toLaurentAlg`.
* `LaurentPolynomial.isScalarTower_polynomial`: the scalar tower `R → R[X] → R[T;T⁻¹]` along
  `Polynomial.toLaurent`.
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
    ⟨fun ⟨q, hq⟩ ↦ ⟨q.toFinsupp.coeff, congrArg AddMonoidAlgebra.coeff hq⟩,
      fun ⟨q, hq⟩ ↦ ⟨.ofFinsupp (.ofCoeff q), AddMonoidAlgebra.coeff_injective hq⟩⟩
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

end LaurentPolynomial
