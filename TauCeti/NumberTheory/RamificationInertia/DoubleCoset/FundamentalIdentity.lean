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

namespace Ideal

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
      (doubleCosetQuotientEquivPrimesOver p Q H q : Ideal (𝓞 ↥(fixedField H))).ramificationIdx
          (𝓞 K) *
        (doubleCosetQuotientEquivPrimesOver p Q H q : Ideal (𝓞 ↥(fixedField H))).inertiaDeg
          (𝓞 K)) = Module.finrank K ↥(fixedField H) := by
  classical
  let _ : p.IsPrime := Ideal.isPrime_of_liesOver (P := Q) (p := p)
  let e := doubleCosetQuotientEquivPrimesOver p Q H
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
    (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)))
  let _ : Fintype (p.primesOver (𝓞 ↥(fixedField H))) := Fintype.ofEquiv _ e
  rw [finsum_eq_sum_of_fintype]
  rw [e.sum_comp (fun q : p.primesOver (𝓞 ↥(fixedField H)) =>
    q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K))]
  calc
    _ = Module.finrank (𝓞 K) (𝓞 ↥(fixedField H)) :=
      Ideal.sum_ramification_inertia_eq_finrank p (𝓞 ↥(fixedField H))
    _ = Module.finrank K ↥(fixedField H) :=
      (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 ↥(fixedField H))
        (↥(fixedField H))).symm

end Ideal

end
