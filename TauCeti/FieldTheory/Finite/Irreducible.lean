/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Irreducible polynomials over finite fields

For every positive degree, a finite field has a monic irreducible polynomial of that degree. We
obtain one as the minimal polynomial of a primitive element of a finite extension of that degree.

Such a polynomial `f` of degree `d` over `k` presents the degree-`d` extension of `k` as the
quotient `k[X] ⧸ (f)`. Over a prime field `ZMod p` these polynomials are the irreducible factors
from which one assembles polynomials with a prescribed factorization pattern modulo `p`, as used
when reading off cycle types of Galois groups by reduction modulo primes.

## Main results

* `TauCeti.exists_monic_irreducible_natDegree_eq`: a monic irreducible polynomial of any
  prescribed positive degree over a finite field.
* `TauCeti.exists_monic_irreducible_natDegree_eq_ne_X`: such a polynomial can be chosen distinct
  from `X`.

## References

The construction follows Mathlib's finite-field extensions `FiniteField.Extension` and
`FiniteField.finrank_extension` (`Mathlib/FieldTheory/Finite/Extension.lean`) and its
primitive element theorem `Field.exists_primitive_element_of_finite_top`
(`Mathlib/FieldTheory/PrimitiveElement.lean`).
-/

public section

noncomputable section

open Polynomial

namespace TauCeti

/-- For every positive `d`, there is a monic irreducible polynomial of degree `d` over any
finite field. -/
theorem exists_monic_irreducible_natDegree_eq
    (k : Type*) [Field k] [Finite k] (d : ℕ) (hd : 0 < d) :
    ∃ f : k[X], f.Monic ∧ Irreducible f ∧ f.natDegree = d := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top k
    (FiniteField.Extension k (ringChar k) d)
  have hαint : IsIntegral k α := .of_finite k α
  exact ⟨minpoly k α, minpoly.monic hαint, minpoly.irreducible hαint,
    ((Field.primitive_element_iff_minpoly_natDegree_eq k α).mp hα).trans
      (FiniteField.finrank_extension k _ d)⟩

/-- For every positive `d`, a finite field has a monic irreducible polynomial of degree `d` other
than `X`. -/
theorem exists_monic_irreducible_natDegree_eq_ne_X
    (k : Type*) [Field k] [Finite k] (d : ℕ) (hd : 0 < d) :
    ∃ h : k[X], h.Monic ∧ Irreducible h ∧ h.natDegree = d ∧ h ≠ X := by
  rcases eq_or_ne d 1 with rfl | hd1
  · exact ⟨X + C 1, monic_X_add_C 1, irreducible_of_degree_eq_one (degree_X_add_C 1),
      natDegree_X_add_C 1, fun h ↦ by simpa using congrArg (coeff · 0) h⟩
  · obtain ⟨h, hmonic, hirr, rfl⟩ := exists_monic_irreducible_natDegree_eq k d hd
    exact ⟨h, hmonic, hirr, rfl, by rintro rfl; simp at hd1⟩

end TauCeti
