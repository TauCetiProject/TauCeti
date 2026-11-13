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

A coefficient map cannot increase `AddMonoidAlgebra.supDegree`, for degrees in any semilattice
with bottom. For linearly ordered degrees, it preserves both `supDegree` and the generic
`leadingCoeff` when it does not kill the selected leading coefficient. No injectivity of the
degree map is required. In particular this nonvanishing applies to unit leading coefficients
under maps to nontrivial rings, including quotients by proper ideals. Unitness of the mapped
leading coefficient is preserved unconditionally, including into a zero ring.
-/

public section

namespace AddMonoidAlgebra

variable {R S A B : Type*} [Semiring R] [Semiring S] [AddMonoid A]

section SupDegree

variable [SemilatticeSup B] [OrderBot B] {D : A → B}

/-- A coefficient homomorphism cannot increase the supremum of the exponent degrees. -/
theorem supDegree_mapRingHom_le (f : R →+* S) (p : R[A]) :
    (mapRingHom A f p).supDegree D ≤ p.supDegree D := by
  classical
  apply Finset.sup_le
  intro a ha
  apply Finset.le_sup
  simp only [Finsupp.mem_support_iff, coeff_mapRingHom] at ha ⊢
  exact fun h ↦ ha (by simp [h])

end SupDegree

variable [LinearOrder B] [OrderBot B] {D : A → B}

/-- A coefficient homomorphism preserves the supremum degree if it retains the leading term. -/
theorem supDegree_mapRingHom_eq_of_leadingCoeff_ne_zero
    (f : R →+* S) {p : R[A]} (hp : f (p.leadingCoeff D) ≠ 0) :
    (mapRingHom A f p).supDegree D = p.supDegree D := by
  classical
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  apply le_antisymm (supDegree_mapRingHom_le f p)
  have he : D (D.invFun (p.supDegree D)) = p.supDegree D :=
    Function.invFun_eq (supDegree_mem_range D hp0)
  rw [← he]
  apply Finset.le_sup
  simpa only [Finsupp.mem_support_iff, coeff_mapRingHom, leadingCoeff] using hp

/-- A coefficient homomorphism preserves the leading coefficient when it does not kill it. -/
theorem leadingCoeff_mapRingHom_of_leadingCoeff_ne_zero
    (f : R →+* S) {p : R[A]} (hp : f (p.leadingCoeff D) ≠ 0) :
    (mapRingHom A f p).leadingCoeff D = f (p.leadingCoeff D) := by
  rw [leadingCoeff, supDegree_mapRingHom_eq_of_leadingCoeff_ne_zero f hp,
    coeff_mapRingHom, leadingCoeff]

/-- A coefficient homomorphism preserves a unit leading coefficient, including in a zero ring. -/
theorem isUnit_leadingCoeff_mapRingHom (f : R →+* S)
    {p : R[A]} (hp : IsUnit (p.leadingCoeff D)) :
    IsUnit ((mapRingHom A f p).leadingCoeff D) := by
  cases subsingleton_or_nontrivial S
  · exact isUnit_of_subsingleton _
  rw [leadingCoeff_mapRingHom_of_leadingCoeff_ne_zero f (hp.map f).ne_zero]
  exact hp.map f

end AddMonoidAlgebra
