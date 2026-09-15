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

* `TauCeti.Nat.exists_monic_irreducible_natDegree_eq`: a monic irreducible polynomial of any
  prescribed positive degree over a finite field.

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

namespace Nat

/-- For every positive `d`, there is a monic irreducible polynomial of degree `d` over any
finite field. -/
theorem exists_monic_irreducible_natDegree_eq
    {k : Type*} [Field k] [Finite k] (d : ℕ) (hd : 0 < d) :
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

end Nat

end TauCeti
