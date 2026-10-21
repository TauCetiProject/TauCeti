/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nullstellensatz

/-!
# The weak Nullstellensatz

Let `K` be an algebraically closed extension of a field `k` and `σ` a finite type. An ideal of
`k[X_σ]` whose polynomials have no common zero in `K^σ` is the unit ideal. This is the weak form of
Hilbert's Nullstellensatz, read off from Mathlib's description of the maximal ideals of `k[X_σ]` as
vanishing ideals of points of `K^σ` (`MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal`). It
is the form in which a polynomial condition checked at the points of `K^σ` gives an identity in
`k[X_σ]`.

## Main results

* `MvPolynomial.zeroLocus_eq_empty_iff`: an ideal of `k[X_σ]` has no zero in `K^σ` exactly when it
  is the unit ideal.
* `MvPolynomial.span_eq_top_iff_forall_exists_aeval_ne_zero`: a set of polynomials generates the
  unit ideal exactly when they have no common zero in `K^σ`.
-/

public section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] [Finite σ]

/-- **The weak Nullstellensatz**: for an algebraically closed extension `K` of `k`, an ideal of
`k[X_σ]` has no zero in `K^σ` exactly when it is the unit ideal. -/
theorem zeroLocus_eq_empty_iff {I : Ideal (MvPolynomial σ k)} :
    zeroLocus K I = ∅ ↔ I = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_contra hI
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI
  obtain ⟨x, rfl⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hM
  have hx : x ∈ zeroLocus K I := fun p hp ↦ (mem_vanishingIdeal_singleton_iff x p).mp (hIM hp)
  simp [h] at hx

/-- **The weak Nullstellensatz for generators**: for an algebraically closed extension `K` of
`k`, polynomials in `k[X_σ]` generate the unit ideal exactly when they have no common zero in
`K^σ`. -/
theorem span_eq_top_iff_forall_exists_aeval_ne_zero {S : Set (MvPolynomial σ k)} :
    Ideal.span S = ⊤ ↔ ∀ x : σ → K, ∃ p ∈ S, aeval x p ≠ 0 := by
  rw [← zeroLocus_eq_empty_iff (K := K), zeroLocus_span, Set.eq_empty_iff_forall_notMem]
  simp

end MvPolynomial
