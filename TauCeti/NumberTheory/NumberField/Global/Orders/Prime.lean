/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Conductor
public import TauCeti.RingTheory.Ideal.Conductor

/-!
# Primes and residue rings away from the conductor of an order

Inclusion of an order into its maximal order identifies the prime ideals coprime to the
conductor. The forward map extends an ideal, and the inverse contracts it. Both carriers
record primality and coprimality, so the correspondence cannot be applied at a prime dividing
the conductor. The induced quotient-ring isomorphism also identifies the residue rings.

These comparisons are the local arithmetic input to comparing invertible ideals of the two
orders. They make no assertion that a general proper fractional ideal is invertible.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §12.
-/

public section
noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- Extension and contraction identify prime ideals coprime to the conductor of an order
with prime ideals of its maximal order coprime to the conductor. -/
def primesAwayConductorEquiv :
    {p : Ideal O.toRingOfIntegers // p.IsPrime ∧
      p ⊔ O.conductor.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) = ⊤} ≃
    {P : Ideal (𝓞 K) // P.IsPrime ∧ P ⊔ O.conductor = ⊤} where
  toFun p := ⟨p.1.map (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K),
    (isPrime_map_iff_of_coprime_comap (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers p.2.2).mpr p.2.1,
    map_sup_eq_top_of_coprime_comap (S := O.toRingOfIntegers.toSubring) p.2.2⟩
  invFun P := ⟨P.1.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K), by
    have := P.2.1
    exact Ideal.comap_isPrime _ _,
    comap_sup_eq_top_of_le (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers P.2.2⟩
  left_inv p := Subtype.ext <|
    comap_map_of_coprime_comap (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers p.2.2
  right_inv P := Subtype.ext <|
    map_comap_of_coprime (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers P.2.2

/-- The prime correspondence sends a prime of the order to its extension in the maximal order. -/
@[simp]
theorem primesAwayConductorEquiv_apply
    (p : {p : Ideal O.toRingOfIntegers // p.IsPrime ∧
      p ⊔ O.conductor.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) = ⊤}) :
    (O.primesAwayConductorEquiv p).1 =
      p.1.map (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) :=
  (rfl)

/-- The inverse prime correspondence sends a prime of the maximal order to its contraction. -/
@[simp]
theorem primesAwayConductorEquiv_symm_apply
    (P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ⊔ O.conductor = ⊤}) :
    (O.primesAwayConductorEquiv.symm P).1 =
      P.1.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) :=
  (rfl)

end TauCeti.GlobalNumberFields.NumberFieldOrder
