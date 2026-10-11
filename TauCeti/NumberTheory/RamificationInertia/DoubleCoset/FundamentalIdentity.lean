/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariants

/-!
# The fundamental identity indexed by double cosets

For a finite Galois extension `M/K`, a subgroup `H` of its Galois group, and a prime `Q` of
`𝓞 M` above `p`, the double cosets `H \ Gal(M/K) / D(Q)` enumerate the primes of the fixed
field `Mᴴ` above `p`. Their local degrees `e·f` add up to `[Mᴴ : K]`.

This is the fundamental identity in the indexing used by the non-Galois splitting law. The
individual local degree is the size of its double coset divided by `|H|`; summing those
sizes counts the right cosets of `H` in the Galois group.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §§8–9.
-/

public section

open IntermediateField MulAction NumberField
open scoped NumberField Pointwise

namespace TauCeti

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

/-- **The fundamental identity in double-coset coordinates.** The primes of the fixed field
`Mᴴ` above `p` are indexed by `H \ Gal(M/K) / D(Q)`; their ramification indices times their
residue degrees sum to the degree of `Mᴴ/K`. -/
theorem sum_ramificationIdx_mul_inertiaDeg_doubleCoset_eq_finrank
    (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p]
    (H : Subgroup (M ≃ₐ[K] M)) :
    (∑ᶠ q : DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
        (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)),
      (Ideal.doubleCosetQuotientEquivPrimesOver p Q H q : Ideal (𝓞 ↥(fixedField H))).ramificationIdx
          (𝓞 K) *
        (Ideal.doubleCosetQuotientEquivPrimesOver p Q H q : Ideal (𝓞 ↥(fixedField H))).inertiaDeg
          (𝓞 K)) = Module.finrank K ↥(fixedField H) := by
  classical
  let _ := Fintype.ofFinite
    (DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
      (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)))
  rw [finsum_eq_sum_of_fintype]
  calc
    _ = ∑ q, Nat.card (DoubleCoset.quotToDoubleCoset H (stabilizer (M ≃ₐ[K] M) Q) q) /
        Nat.card H := by
      apply Finset.sum_congr rfl
      intro q _
      exact Ideal.ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOver_eq_card_div
        p Q H q
    _ = H.index := Subgroup.sum_card_quotToDoubleCoset_div_card_eq_index H
      (stabilizer (M ≃ₐ[K] M) Q)
    _ = Module.finrank K ↥(fixedField H) := by
      rw [IntermediateField.finrank_eq_fixingSubgroup_index,
        IntermediateField.fixingSubgroup_fixedField]

end TauCeti

end
