/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Span

/-!
# Ideals lying over a principal ideal, and towers of residue rings

For an ideal `Q` of an `R`-algebra lying over the principal ideal `(a)` of a commutative semiring
`R` (`Ideal.LiesOver`), an element `m : R` maps into `Q` exactly when `a ∣ m`; this unfolds
`Ideal.mem_of_liesOver` through `Ideal.mem_span_singleton` once. Over `R = ℤ`, the base residue
ring `ℤ ⧸ Q ∩ ℤ` of an ideal lying over `(n)` is `ℤ ⧸ (n)`, so its `Nat.card` is `n`: for `n ≠ 0`
it has exactly `n` elements, while for `n = 0` it is the infinite ring `ℤ`, whose `Nat.card` is
`0` by convention.

Together they let arithmetic arguments move between divisibility in `ℤ` and membership in `Q`,
and pin the residue cardinality that `AlgHom.IsArithFrobAt` exponentiates by, without repeating
the translation at each use site.

For a tower of ideals `p ⊆ Q ⊆ P` along a tower of algebras `A → B → C`, the residue rings
`A ⧸ p`, `B ⧸ Q` and `C ⧸ P` form a tower of algebras for the `Ideal.LiesOver` algebra structures.

## Main results

* `Ideal.algebraMap_mem_iff_dvd_of_liesOver`: `algebraMap R S m ∈ Q ↔ a ∣ m`.
* `Ideal.natCard_quotient_under_of_liesOver`: `Nat.card (ℤ ⧸ Q ∩ ℤ) = n` for `Q` over `(n)`.
* `Ideal.Quotient.isScalarTower_quotient_of_liesOver`: `A ⧸ p → B ⧸ Q → C ⧸ P` is a tower of
  algebras.
-/

public section

open Ideal

namespace Ideal

/-- An ideal of an `R`-algebra lying over the principal ideal `(a)` meets `R` exactly in the
multiples of `a`: `algebraMap R S m ∈ Q ↔ a ∣ m`. -/
theorem algebraMap_mem_iff_dvd_of_liesOver {R S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] {a : R} (Q : Ideal S) [Q.LiesOver (span {a})] (m : R) :
    algebraMap R S m ∈ Q ↔ a ∣ m :=
  (mem_of_liesOver Q (span {a}) m).symm.trans mem_span_singleton

/-- The base residue ring of an ideal lying over the integer ideal `(n)` has `Nat.card` equal
to `n`: `Nat.card (ℤ ⧸ Q ∩ ℤ) = n` for `Q` over `(n)`. For `n ≠ 0` this says the residue ring has
exactly `n` elements; for `n = 0` the residue ring is `ℤ`, which is infinite, so both sides are
`0` by the `Nat.card` convention.

This is the cardinality that `AlgHom.IsArithFrobAt` raises to over the base `ℤ`, so for `n` a
rational prime `p` it is what turns an abstract Frobenius congruence into the congruence
`φ y ≡ y ^ p`. -/
theorem natCard_quotient_under_of_liesOver {S : Type*} [Ring S] {n : ℕ}
    (Q : Ideal S) [Q.LiesOver (span {(n : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = n := by
  rw [← over_def Q (span {(n : ℤ)}), Int.card_ideal_quot]

/-- The residue rings of a tower of ideals `p ⊆ Q ⊆ P` along a tower of algebras `A → B → C` form
a tower of algebras. -/
theorem Quotient.isScalarTower_quotient_of_liesOver {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (p : Ideal A)
    (Q : Ideal B) (P : Ideal C) [Q.LiesOver p] [P.LiesOver Q] [P.LiesOver p] :
    IsScalarTower (A ⧸ p) (B ⧸ Q) (C ⧸ P) :=
  .of_algebraMap_eq <| by
    rintro ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (IsScalarTower.algebraMap_apply A B C x)

end Ideal

end
