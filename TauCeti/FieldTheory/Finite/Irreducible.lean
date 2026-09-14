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

## Main results

* `Polynomial.exists_monic_irreducible_natDegree_eq`: a monic irreducible polynomial of any
  prescribed positive degree over a finite field.
* `Polynomial.exists_monic_irreducible_natDegree_eq_zmod`: a monic irreducible polynomial of
  any prescribed positive degree over `ZMod p`, for prime `p`.
* `Polynomial.exists_monic_irreducible_natDegree_eq_zmod_two`: the specialization to `ZMod 2`.
-/

public section

noncomputable section

open Polynomial

namespace TauCeti

/-- For every positive `d`, there is a monic irreducible polynomial of degree `d` over any
finite field. -/
theorem _root_.Polynomial.exists_monic_irreducible_natDegree_eq
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

/-- For a prime `p` and every positive `d`, there is a monic irreducible polynomial of
degree `d` over `ZMod p`. -/
theorem _root_.Polynomial.exists_monic_irreducible_natDegree_eq_zmod
    (p d : ℕ) [Fact p.Prime] (hd : 0 < d) :
    ∃ f : (ZMod p)[X], f.Monic ∧ Irreducible f ∧ f.natDegree = d := by
  exact Polynomial.exists_monic_irreducible_natDegree_eq d hd

/-- For every positive `d`, there is a monic irreducible polynomial of degree `d` over
`ZMod 2`. -/
theorem _root_.Polynomial.exists_monic_irreducible_natDegree_eq_zmod_two
    (d : ℕ) (hd : 0 < d) :
    ∃ f : (ZMod 2)[X], f.Monic ∧ Irreducible f ∧ f.natDegree = d := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Polynomial.exists_monic_irreducible_natDegree_eq_zmod 2 d hd

end TauCeti
