/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Algebra

/-!
# Examples of almost algebras

These examples test the category `TauCeti.Almost.Algebra S` of almost algebras and the
almostification functor `TauCeti.Almost.Algebra.toAlmost S`:

* `(V ⧸ m)^a` is zero for every setup, and for the zero setup every almost algebra is zero;
* for the classical setup `(ℤ, ℤ)`, `ℤ^a` is not zero, and almostification of algebras is full
  and faithful;
* the inclusion `ℤ → ℚ` almostifies to an isomorphism for the zero setup but not for the classical
  setup, since it is not surjective.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2.
-/

open CategoryTheory Limits TauCeti.Almost TauCeti.Almost.BasicSetup TauCeti.Almost.Algebra

variable {V : Type*} [CommRing V]

/-! ### Zero and nonzero almost algebras -/

-- `(V ⧸ m)^a` is zero for every setup.
example (S : BasicSetup V) : IsZero ((toAlmost S).obj (CommAlgCat.of V (V ⧸ S.ideal))).X := by
  rw [isZero_toAlmost_obj_X_iff, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

-- For the zero setup, every almost algebra is zero.
example (A : Algebra (zero V)) : IsZero A.X :=
  Module.isZero_of_ideal_eq_bot _ zero_ideal A.X

-- For the classical setup, `ℤ^a` is not zero.
example : ¬ IsZero ((toAlmost (classical ℤ)).obj (CommAlgCat.of ℤ ℤ)).X := by
  rw [isZero_toAlmost_obj_X_iff, classical_ideal, top_le_iff]
  exact RingHom.ker_ne_top _

/-! ### Almostification in the classical setup -/

-- For the classical setup, almostification of algebras is full and faithful.
example : (toAlmost (classical V)).Full := inferInstance

example : (toAlmost (classical V)).Faithful := inferInstance

/-! ### Almost isomorphisms of algebras -/

-- For the zero setup, the inclusion `ℤ → ℚ` almostifies to an isomorphism.
example : IsIso ((toAlmost (zero ℤ)).map
    (CommAlgCat.ofHom (Algebra.ofId ℤ ℚ) : CommAlgCat.of ℤ ℤ ⟶ CommAlgCat.of ℤ ℚ)) :=
  (isIso_toAlmost_map_iff _ _).mpr (isAlmostIso_zero _)

-- For the classical setup, it does not, since `1 / 2` is not in its range.
example : ¬ IsIso ((toAlmost (classical ℤ)).map
    (CommAlgCat.ofHom (Algebra.ofId ℤ ℚ) : CommAlgCat.of ℤ ℤ ⟶ CommAlgCat.of ℤ ℚ)) := by
  rw [isIso_toAlmost_map_iff, isAlmostIso_classical_iff]
  rintro ⟨-, hs⟩
  obtain ⟨n, hn⟩ := hs (1 / 2)
  simp only [ConcreteCategory.hom_ofHom, Algebra.ofId_toLinearMap, Algebra.linearMap_apply,
    algebraMap_int_eq, eq_intCast] at hn
  have h : ((n * 2 : ℤ) : ℚ) = 1 := by
    rw [Int.cast_mul, hn]
    norm_num
  norm_cast at h
  omega
