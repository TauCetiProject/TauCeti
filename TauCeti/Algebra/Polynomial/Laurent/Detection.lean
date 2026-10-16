/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Detecting Laurent polynomials by evaluations

An infinite family of distinct units in an integral domain detects Laurent polynomials over a
commutative semiring, provided that the coefficient homomorphism is injective. This applies in
particular to reconstructing a polynomial from specializations of an invertible variable to
successive powers of an indeterminate. Evaluation at a single transcendental unit also detects
Laurent polynomials over a commutative ring.
-/

public section

namespace LaurentPolynomial

open scoped Polynomial

variable {R S : Type*} [CommSemiring R] [CommRing S]

section Infinite

variable [IsDomain S]

/-- Laurent polynomials over a commutative semiring that agree at infinitely many units
of an integral domain are equal, provided the coefficient homomorphism is injective. -/
theorem eq_of_infinite_eval₂_eq (p q : LaurentPolynomial R) (f : R →+* S)
    (hf : Function.Injective f)
    (h : Set.Infinite {u : Sˣ | eval₂ f u p = eval₂ f u q}) : p = q := by
  obtain ⟨n, g, hg⟩ := p.exists_T_pow
  obtain ⟨m, k, hk⟩ := q.exists_T_pow
  have hg' : Polynomial.toLaurent (g * Polynomial.X ^ m) =
      p * T ((n : ℤ) + m) := by simp [map_mul, hg]
  have hk' : Polynomial.toLaurent (k * Polynomial.X ^ n) =
      q * T ((n : ℤ) + m) := by simp [map_mul, hk, add_comm]
  have hevals : Set.Infinite {x : S |
      ((g * Polynomial.X ^ m).map f).eval x = ((k * Polynomial.X ^ n).map f).eval x} := by
    refine (h.image Units.val_injective.injOn).mono ?_
    rintro x ⟨u, hu, rfl⟩
    have he := congrArg (· * (u ^ ((n : ℤ) + m)).val) hu
    simpa only [Set.mem_ofPred_eq, ← Polynomial.eval₂_eq_eval_map, ← eval₂_toLaurent,
      hg', hk', map_mul, eval₂_T] using he
  have hgk := Polynomial.map_injective f hf <|
    Polynomial.eq_of_infinite_eval_eq _ _ hevals
  apply (isUnit_T (R := R) ((n : ℤ) + m)).mul_left_inj.mp
  rw [← hg', ← hk', hgk]

/-- A Laurent polynomial over a commutative semiring vanishing at infinitely many units
of an integral domain is zero, provided the coefficient homomorphism is injective. -/
theorem eq_zero_of_infinite_eval₂_eq_zero (p : LaurentPolynomial R) (f : R →+* S)
    (hf : Function.Injective f)
    (h : Set.Infinite {u : Sˣ | eval₂ f u p = 0}) : p = 0 := by
  apply p.eq_of_infinite_eval₂_eq 0 f hf
  simpa only [map_zero] using h

end Infinite

end LaurentPolynomial

namespace RingHom

open LaurentPolynomial

variable {R S : Type*} [CommSemiring R] [CommRing S] [IsDomain S]

/-- Evaluations along any infinite range of units in an integral domain jointly detect
Laurent polynomials over a commutative semiring, provided the coefficient homomorphism
is injective. The index type need not be countable, and the family need not be injective. -/
theorem laurent_eval₂_family_injective {ι : Type*} (f : R →+* S)
    (hf : Function.Injective f) (u : ι → Sˣ) (hu : Set.Infinite (Set.range u)) :
    Function.Injective (fun p : LaurentPolynomial R ↦ fun i ↦ eval₂ f (u i) p) := by
  intro p q hpq
  apply p.eq_of_infinite_eval₂_eq q f hf
  refine hu.mono ?_
  rintro x ⟨i, rfl⟩
  exact congrFun hpq i

end RingHom

namespace Units

open LaurentPolynomial
open scoped Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Evaluation at a transcendental unit is injective. -/
theorem laurent_eval₂_injective_of_transcendental (u : Sˣ)
    (hu : Transcendental R (u : S)) :
    Function.Injective (eval₂ (algebraMap R S) u) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (Polynomial.X : R[X]))]
  intro p q
  simp only [algebraMap_eq_toLaurent, Polynomial.toLaurent_inj, eval₂_toLaurent,
    ← Polynomial.aeval_def]
  exact (transcendental_iff_injective.mp hu).eq_iff.symm

end Units
