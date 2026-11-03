/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent.Roots
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Detecting Laurent polynomials by evaluations

An infinite family of distinct units in an integral domain detects Laurent polynomials over a
commutative semiring, provided that the coefficient homomorphism is injective. This applies in
particular to reconstructing a polynomial from specializations of an invertible variable to
successive powers of an indeterminate. Evaluation at a single transcendental unit also detects
Laurent polynomials over a commutative ring.

As a consequence, an endomorphism of a field that fixes infinitely many elements and agrees with a
Laurent polynomial at every unit is the identity (`RingHom.eq_id_of_forall_eval₂_eq`). For
instance complex conjugation is not a Laurent polynomial function on `ℂˣ`.
-/

public section

namespace LaurentPolynomial

open scoped Polynomial

variable {R S : Type*} [CommSemiring R] [CommRing S]

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
  let _ := f.toAlgebra
  let _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr <| by
    simpa only [RingHom.algebraMap_toAlgebra] using hf
  intro p q hpq
  apply LaurentPolynomial.eq_of_infinite_smeval_eq (S := S)
  refine hu.mono ?_
  rintro x ⟨i, rfl⟩
  rw [Set.mem_ofPred_eq]
  simpa only [← LaurentPolynomial.eval₂_eq_smeval,
    RingHom.algebraMap_toAlgebra] using congrFun hpq i

/-- **A field endomorphism that is a Laurent polynomial on units is the identity**, provided it
fixes infinitely many elements: if `σ u = p(u)` for every unit `u` of `K`, then `σ = id`. -/
theorem eq_id_of_forall_eval₂_eq {K : Type*} [Field K] (σ : K →+* K)
    (hσ : {x : K | σ x = x}.Infinite) (p : LaurentPolynomial K)
    (h : ∀ u : Kˣ, eval₂ (RingHom.id K) u p = σ u) : σ = RingHom.id K := by
  have hfix : {u : Kˣ | σ u = u}.Infinite := by
    refine Set.Infinite.of_image Units.val ((hσ.sdiff (Set.finite_singleton 0)).mono ?_)
    rintro x ⟨hx, hx0⟩
    exact ⟨Units.mk0 x hx0, hx, rfl⟩
  -- `p` agrees with `T` at the infinitely many nonzero fixed points of `σ`, so `p = T`.
  have hp : p = T 1 := by
    refine LaurentPolynomial.eq_of_infinite_smeval_eq (S := K) (hfix.mono ?_)
    intro u hu
    rw [Set.mem_ofPred_eq, ← eval₂_eq_smeval, ← eval₂_eq_smeval]
    simp [h, hu.out]
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simpa [hp] using (h (Units.mk0 x hx)).symm

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
