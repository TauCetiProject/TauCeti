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

/-- A coefficient homomorphism preserves the leading coefficient when it does not kill it. -/
theorem leadingCoeff_mapRingHom_of_ne_zero (hD : Function.Injective D)
    (f : R →+* S) {p : R[A]} (hp : f (p.leadingCoeff D) ≠ 0) :
    (mapRingHom A f p).leadingCoeff D = f (p.leadingCoeff D) := by
  classical
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  obtain ⟨a, -, he⟩ := exists_supDegree_mem_support D hp0
  have hl : p.leadingCoeff D = p.coeff a := by
    rw [leadingCoeff, he, Function.leftInverse_invFun hD a]
  have hd : (mapRingHom A f p).supDegree D = D a := by
    apply supDegree_eq_of_max ⟨a, rfl⟩
    · simpa only [Function.leftInverse_invFun hD a, Finsupp.mem_support_iff,
        coeff_mapRingHom, ← hl] using hp
    · intro b hb
      have hb' : b ∈ p.coeff.support := by
        simp only [Finsupp.mem_support_iff, coeff_mapRingHom] at hb ⊢
        exact fun h ↦ hb (by simp [h])
      exact he ▸ Finset.le_sup hb'
  rw [leadingCoeff, hd, Function.leftInverse_invFun hD a, coeff_mapRingHom, hl]

end AddMonoidAlgebra
