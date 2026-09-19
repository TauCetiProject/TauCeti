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
  let ⟨p, hp⟩ := CharP.exists k
  let _ : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let _ : NeZero d := ⟨hd.ne'⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top
    k (FiniteField.Extension k p d)
  have hαint : IsIntegral k α := IsIntegral.of_finite k α
  refine ⟨minpoly k α, minpoly.monic hαint, minpoly.irreducible hαint, ?_⟩
  calc
    (minpoly k α).natDegree = Module.finrank k (FiniteField.Extension k p d) :=
      (Field.primitive_element_iff_minpoly_natDegree_eq k α).mp hα
    _ = d := FiniteField.finrank_extension k p d

/-- For every positive `d`, a finite field has a monic irreducible polynomial of degree `d` other
than `X`: in degree `1` take `X + 1`, and in higher degree any irreducible polynomial differs
from `X` by its degree. -/
theorem exists_monic_irreducible_natDegree_eq_ne_X
    (k : Type*) [Field k] [Finite k] (d : ℕ) (hd : 0 < d) :
    ∃ h : k[X], h.Monic ∧ Irreducible h ∧ h.natDegree = d ∧ h ≠ X := by
  obtain rfl | hd1 := eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hd.ne')
  · refine ⟨X + C 1, monic_X_add_C 1, irreducible_of_degree_eq_one (degree_X_add_C 1),
      natDegree_X_add_C 1, fun h ↦ ?_⟩
    simpa using congrArg (coeff · 0) h
  · obtain ⟨h, hmonic, hirr, hdeg⟩ := exists_monic_irreducible_natDegree_eq k d hd
    exact ⟨h, hmonic, hirr, hdeg, fun hX ↦ by simp [hX] at hdeg; omega⟩

end TauCeti
