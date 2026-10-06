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

An infinite family of distinct units in an integral domain detects Laurent polynomials,
provided that the coefficient homomorphism is injective. This applies in particular to
reconstructing a polynomial from specializations of an invertible variable to successive
powers of an indeterminate.
-/

public section

namespace TauCeti

open LaurentPolynomial
open scoped Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

section Infinite

variable [IsDomain S]

/-- A Laurent polynomial vanishing at infinitely many units is zero, as long as the
coefficient homomorphism is injective. -/
theorem eq_zero_of_infinite_laurent_eval₂_eq_zero (f : R →+* S)
    (hf : Function.Injective f) (p : LaurentPolynomial R)
    (h : Set.Infinite {u : Sˣ | eval₂ f u p = 0}) : p = 0 := by
  obtain ⟨n, g, hg⟩ := p.exists_T_pow
  have hroots : Set.Infinite {x : S | (g.map f).IsRoot x} := by
    refine (h.image Units.val_injective.injOn).mono ?_
    rintro x ⟨u, hu, rfl⟩
    simp only [Set.mem_ofPred_eq] at hu
    have he := congrArg (eval₂ f u) hg
    simpa [hu, Polynomial.eval₂_eq_eval_map, Polynomial.IsRoot] using he
  have hg0 : g = 0 := (Polynomial.map_injective f hf) <| by
    simpa using (g.map f).eq_zero_of_infinite_isRoot hroots
  have hp : p * T (n : ℤ) = 0 := by simpa [hg0] using hg.symm
  exact (isUnit_T (R := R) n).mul_left_eq_zero.mp hp

/-- Laurent polynomials that agree at infinitely many units are equal. -/
theorem eq_of_infinite_laurent_eval₂_eq (f : R →+* S) (hf : Function.Injective f)
    (p q : LaurentPolynomial R)
    (h : Set.Infinite {u : Sˣ | eval₂ f u p = eval₂ f u q}) : p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_infinite_laurent_eval₂_eq_zero f hf
  simpa only [map_sub, sub_eq_zero] using h

/-- Evaluations along any infinite range of units jointly detect Laurent polynomials.
The index type need not be countable, and the family need not be injective. -/
theorem laurent_eval₂_family_injective {ι : Type*} (f : R →+* S)
    (hf : Function.Injective f) (u : ι → Sˣ) (hu : Set.Infinite (Set.range u)) :
    Function.Injective (fun p : LaurentPolynomial R ↦ fun i ↦ eval₂ f (u i) p) := by
  intro p q hpq
  apply eq_of_infinite_laurent_eval₂_eq f hf p q
  refine hu.mono ?_
  rintro x ⟨i, rfl⟩
  exact congrFun hpq i

end Infinite

/-- Evaluation at a transcendental unit is injective. -/
theorem laurent_eval₂_injective_of_transcendental [Algebra R S] (u : Sˣ)
    (hu : Transcendental R (u : S)) :
    Function.Injective (eval₂ (algebraMap R S) u) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (Polynomial.X : R[X]))]
  intro p q
  simp only [algebraMap_eq_toLaurent, Polynomial.toLaurent_inj, eval₂_toLaurent,
    ← Polynomial.aeval_def]
  exact (transcendental_iff_injective.mp hu).eq_iff.symm

end TauCeti
