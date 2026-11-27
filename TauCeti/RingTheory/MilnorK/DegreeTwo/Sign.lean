/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.MatsumotoGroup.OrderedField
public import TauCeti.RingTheory.MilnorK.DegreeTwo.Basic
public import TauCeti.RingTheory.MilnorK.Sign

/-!
# Comparison of degree-two Milnor K-theory and Matsumoto signs

Over a linearly ordered commutative ring `R`, this file identifies the degree-two sign map
`TauCeti.MilnorK.sign R 2` with `TauCeti.MatsumotoGroup.sign R` under the canonical isomorphism
`TauCeti.MilnorK.degreeTwoEquiv R : degree R 2 ≃ₗ[ℤ] MatsumotoGroup R`.

## Main results

* `TauCeti.MilnorK.sign_two_eq_matsumotoGroup_sign`: agreement of `MilnorK.sign R 2` and
  `MatsumotoGroup.sign R` under `degreeTwoEquiv`.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. **9** (1970), §1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, Example 6.2.1
  and Example 7.2(c).
-/

public section

namespace TauCeti.MilnorK

section OrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- In degree `2`, `MilnorK.sign` agrees with `MatsumotoGroup.sign` under `degreeTwoEquiv`. -/
theorem sign_two_eq_matsumotoGroup_sign (x : degree R 2) :
    sign R 2 x = MatsumotoGroup.sign R (degreeTwoEquiv R x) :=
  LinearMap.congr_fun
    (f := (sign R 2).toIntLinearMap.comp (degree R 2).subtype)
    (g := (MatsumotoGroup.sign R).toIntLinearMap.comp (degreeTwoEquiv R).toLinearMap)
    (degreeTwo_linearMap_ext fun a b => by
      rw [← degreeTwo_symbol_eq_ofUnit_mul]
      simp only [LinearMap.comp_apply, Submodule.coe_subtype, AddMonoidHom.coe_toIntLinearMap,
        LinearEquiv.coe_coe, degreeTwoEquiv_symbol, MatsumotoGroup.sign_symbol, sign_symbol,
        List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, List.forall_mem_cons,
        List.not_mem_nil, false_implies, implies_true, and_true, true_and]) x

end OrderedCommRing

end TauCeti.MilnorK
