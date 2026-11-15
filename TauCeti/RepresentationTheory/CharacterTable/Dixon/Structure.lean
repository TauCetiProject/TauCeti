/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Prime
public import TauCeti.RepresentationTheory.CharacterTable.FiniteField

/-!
# The good-prime structure theorem

The Burnside--Dixon--Schneider algorithm computes over `ZMod p` instead of over `ℂ`, and the
theorem that licenses the substitution is this one: at a good Dixon prime the centre of
`ZMod p [G]` looks exactly like the centre of `ℂ[G]`, namely a product of `r` copies of the
coefficient field, `r` the number of conjugacy classes.

The arithmetic condition `Monoid.exponent G ∣ p - 1` says `g ^ p = g` for every `g : G`, so that
`ZMod p` already contains the eigenvalues of every group element. For finite `G` this also
forces `p ∤ |G|`, by Cauchy's theorem. Dixon's size bound plays no part here -- it is about the
lift back to characteristic zero, not about the modular computation.

Everything is inherited from
`TauCeti/RepresentationTheory/CharacterTable/FiniteField.lean`, which proves the statement for an
arbitrary finite coefficient field satisfying that power-map condition. Since `ZMod p` has `p`
elements, `g ^ Fintype.card (ZMod p) = g` is exactly the exponent condition.

## Main results

* `TauCeti.IsGoodDixonPrime.pow_prime_eq_self`: `g ^ p = g` at a good Dixon prime.
* `TauCeti.IsGoodDixonPrime.center_pow_prime`: the modular centre is fixed by the Frobenius.
* `TauCeti.IsGoodDixonPrime.nonempty_center_algEquiv_conjClasses` and
  `TauCeti.IsGoodDixonPrime.nonempty_center_algEquiv_pi`: **the good-prime structure theorem**,
  `Z(ZMod p [G]) ≃ₐ[ZMod p] (ConjClasses G → ZMod p)`, indexed by the conjugacy classes and by
  `Fin r` respectively.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
-/

public section

namespace TauCeti

namespace IsGoodDixonPrime

variable {G : Type*} [Group G] {p : ℕ}

/-- **Every group element is fixed by the `p`-th power map at a good Dixon prime.** The exponent of
`G` divides `p - 1`, so `g ^ (p - 1) = 1`. This is the group-side form of the condition that
`ZMod p` contains the `e`-th roots of unity. -/
theorem pow_prime_eq_self (hp : IsGoodDixonPrime G p) (g : G) : g ^ p = g := by
  have hdvd : orderOf g ∣ p - 1 := (Monoid.order_dvd_exponent g).trans hp.exponent_dvd
  have h1 : g ^ (p - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  calc g ^ p = g ^ (p - 1 + 1) := by rw [Nat.sub_add_cancel hp.prime.one_lt.le]
    _ = g := by rw [pow_succ, h1, one_mul]

/-- **The modular centre is fixed by the Frobenius.** Every central element `y` of `ZMod p [G]`
satisfies `y ^ p = y`; equivalently, the central characters take values in the prime field rather
than in a proper extension of it. This is the mechanism behind the structure theorem. -/
theorem center_pow_prime (hp : IsGoodDixonPrime G p) {y : MonoidAlgebra (ZMod p) G}
    (hy : y ∈ Subalgebra.center (ZMod p) (MonoidAlgebra (ZMod p) G)) :
    y ^ p = y := by
  have := hp.fact_prime
  have := hp.neZero
  have := hp.finite
  have h := pow_card_eq_self_of_mem_center (by simpa using hp.pow_prime_eq_self) hy
  rwa [ZMod.card] at h

/-- **The good-prime structure theorem.** At a good Dixon prime the centre of `ZMod p [G]` is the
algebra of `ZMod p`-valued functions on the conjugacy classes of `G`.

This is what guarantees that the class-multiplication matrices are simultaneously diagonalizable
over `ZMod p` with exactly `r` distinct common eigenrows, so that the eigenvector search of the
Burnside--Dixon--Schneider algorithm terminates in one-dimensional common eigenspaces, with no
bad-prime merging of distinct central characters. -/
theorem nonempty_center_algEquiv_conjClasses (hp : IsGoodDixonPrime G p) :
    Nonempty (Subalgebra.center (ZMod p) (MonoidAlgebra (ZMod p) G) ≃ₐ[ZMod p]
      (ConjClasses G → ZMod p)) := by
  have := hp.fact_prime
  have := hp.neZero
  have := hp.finite
  exact TauCeti.nonempty_center_algEquiv_conjClasses (by simpa using hp.pow_prime_eq_self)

/-- The good-prime structure theorem with the factors indexed by `Fin r` rather than by the
conjugacy classes themselves: the shape in which the finite-field linear algebra of the
Burnside--Dixon--Schneider algorithm consumes it. -/
theorem nonempty_center_algEquiv_pi (hp : IsGoodDixonPrime G p) :
    Nonempty (Subalgebra.center (ZMod p) (MonoidAlgebra (ZMod p) G) ≃ₐ[ZMod p]
      (Fin (Nat.card (ConjClasses G)) → ZMod p)) := by
  have := hp.finite
  have := Fintype.ofFinite (ConjClasses G)
  obtain ⟨e⟩ := hp.nonempty_center_algEquiv_conjClasses
  refine ⟨e.trans (AlgEquiv.piCongrLeft' (ZMod p) (fun _ => ZMod p) ?_)⟩
  exact (Fintype.equivFin (ConjClasses G)).trans
    (finCongr (Nat.card_eq_fintype_card (α := ConjClasses G)).symm)

end IsGoodDixonPrime

end TauCeti
