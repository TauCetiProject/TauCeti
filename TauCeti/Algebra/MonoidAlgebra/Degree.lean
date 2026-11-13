/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Degree
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Leading coefficients and coefficient maps

A coefficient map preserves the existing generic leading coefficient when it does not kill that
coefficient. This applies to quotient maps at unit leading coefficients, even when lower
coefficients disappear. The separate-variable Laurent intersection uses this to retain a unit
highest coefficient over a possibly nonreduced coefficient quotient.
-/

public section

namespace AddMonoidAlgebra

variable {R S A B : Type*} [Semiring R] [Semiring S] [AddMonoid A]
  [LinearOrder B] [OrderBot B] {D : A → B}

/-- A coefficient homomorphism cannot increase the supremum of the exponent degrees. -/
theorem supDegree_mapRingHom_le (f : R →+* S) (p : R[A]) :
    (mapRingHom A f p).supDegree D ≤ p.supDegree D := by
  classical
  apply Finset.sup_le
  intro a ha
  apply Finset.le_sup
  simp only [Finsupp.mem_support_iff, coeff_mapRingHom] at ha ⊢
  exact fun h ↦ ha (by simp [h])

/-- A coefficient homomorphism preserves the supremum degree if it retains the leading term. -/
theorem supDegree_mapRingHom_eq_of_leadingCoeff_ne_zero (hD : Function.Injective D)
    (f : R →+* S) {p : R[A]} (hp : f (p.leadingCoeff D) ≠ 0) :
    (mapRingHom A f p).supDegree D = p.supDegree D := by
  classical
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  obtain ⟨a, -, he⟩ := exists_supDegree_mem_support D hp0
  have hl : p.leadingCoeff D = p.coeff a := by
    rw [leadingCoeff, he, Function.leftInverse_invFun hD a]
  apply le_antisymm (supDegree_mapRingHom_le f p)
  rw [he]
  apply Finset.le_sup
  simpa only [Finsupp.mem_support_iff, coeff_mapRingHom, ← hl] using hp

/-- A coefficient homomorphism preserves the leading coefficient when it does not kill it. -/
theorem leadingCoeff_mapRingHom_of_leadingCoeff_ne_zero (hD : Function.Injective D)
    (f : R →+* S) {p : R[A]} (hp : f (p.leadingCoeff D) ≠ 0) :
    (mapRingHom A f p).leadingCoeff D = f (p.leadingCoeff D) := by
  rw [leadingCoeff, supDegree_mapRingHom_eq_of_leadingCoeff_ne_zero hD f hp,
    coeff_mapRingHom, leadingCoeff]

/-- A coefficient homomorphism preserves a unit leading coefficient, including in a zero ring. -/
theorem isUnit_leadingCoeff_mapRingHom (hD : Function.Injective D) (f : R →+* S)
    {p : R[A]} (hp : IsUnit (p.leadingCoeff D)) :
    IsUnit ((mapRingHom A f p).leadingCoeff D) := by
  cases subsingleton_or_nontrivial S
  · exact isUnit_of_subsingleton _
  rw [leadingCoeff_mapRingHom_of_leadingCoeff_ne_zero hD f (hp.map f).ne_zero]
  exact hp.map f

end AddMonoidAlgebra
