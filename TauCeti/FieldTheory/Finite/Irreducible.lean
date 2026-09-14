/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Irreducible polynomials over prime fields

For every positive degree, a prime field has a monic irreducible polynomial of that degree. We
obtain one as the minimal polynomial of a primitive element of the corresponding Galois field.

## Main results

* `Polynomial.exists_monic_irreducible_natDegree_eq_zmod`: a monic irreducible polynomial of
  any prescribed positive degree over `ZMod p`, for prime `p`.
* `Polynomial.exists_monic_irreducible_natDegree_eq_zmod_two`: the specialization to `ZMod 2`.

The binary-field result is prerequisite 1 of Layer 9 in the
`PolynomialGaloisGroups` roadmap. It supplies the irreducible reduction used by the three-prime
construction of integral polynomials with full symmetric Galois group.
-/

public section

noncomputable section

open Polynomial

namespace TauCeti

/-- For a prime `p` and every positive `d`, there is a monic irreducible polynomial of
degree `d` over `ZMod p`. -/
theorem _root_.Polynomial.exists_monic_irreducible_natDegree_eq_zmod
    (p d : ℕ) [Fact p.Prime] (hd : 0 < d) :
    ∃ f : (ZMod p)[X], f.Monic ∧ Irreducible f ∧ f.natDegree = d := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top
    (ZMod p) (GaloisField p d)
  have hαint : IsIntegral (ZMod p) α := IsIntegral.of_finite (ZMod p) α
  refine ⟨minpoly (ZMod p) α, minpoly.monic hαint, minpoly.irreducible hαint, ?_⟩
  calc
    (minpoly (ZMod p) α).natDegree = Module.finrank (ZMod p) (GaloisField p d) :=
      (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) α).mp hα
    _ = d := GaloisField.finrank p hd.ne'

/-- For every positive `d`, there is a monic irreducible polynomial of degree `d` over
`ZMod 2`. -/
theorem _root_.Polynomial.exists_monic_irreducible_natDegree_eq_zmod_two
    (d : ℕ) (hd : 0 < d) :
    ∃ f : (ZMod 2)[X], f.Monic ∧ Irreducible f ∧ f.natDegree = d := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Polynomial.exists_monic_irreducible_natDegree_eq_zmod 2 d hd

end TauCeti
