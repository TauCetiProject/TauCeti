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
# Integers and an ideal lying over `(a)`, and towers of residue rings

For an ideal `Q` of a `ℤ`-algebra lying over the integer ideal `(a)` (`Ideal.LiesOver`), two
translations recur. An integer `m` maps into `Q` exactly when `a ∣ m`, which unfolds
`Ideal.mem_of_liesOver` through `Ideal.mem_span_singleton` once; and the base residue ring
`ℤ ⧸ Q ∩ ℤ` is `ℤ ⧸ (a)`, so for `a` a natural prime `p` it has exactly `p` elements.

Together they let arithmetic arguments move between divisibility in `ℤ` and membership in `Q`,
and pin the residue cardinality that `AlgHom.IsArithFrobAt` exponentiates by, without repeating
the translation at each use site.

For a tower of ideals `p ⊆ Q ⊆ P` along a tower of algebras `A → B → C`, the residue rings
`A ⧸ p`, `B ⧸ Q` and `C ⧸ P` form a tower of algebras for the `Ideal.LiesOver` algebra structures.

## Main results

* `Ideal.algebraMap_int_mem_iff_dvd_of_liesOver`: `algebraMap ℤ S m ∈ Q ↔ a ∣ m`.
* `Ideal.natCard_quotient_under_of_liesOver`: `Nat.card (ℤ ⧸ Q ∩ ℤ) = p` for `Q` over `(p)`.
* `Ideal.Quotient.isScalarTower_quotient_of_liesOver`: `A ⧸ p → B ⧸ Q → C ⧸ P` is a tower of
  algebras.
-/

public section

open Ideal

namespace Ideal

/-- An ideal of a `ℤ`-algebra lying over the integer ideal `(a)` meets `ℤ` exactly in the
multiples of `a`: `algebraMap ℤ S m ∈ Q ↔ a ∣ m`. -/
theorem algebraMap_int_mem_iff_dvd_of_liesOver {S : Type*} [Ring S] {a : ℤ}
    (Q : Ideal S) [Q.LiesOver (span {a})] (m : ℤ) :
    algebraMap ℤ S m ∈ Q ↔ a ∣ m :=
  (Ideal.mem_of_liesOver Q (span {a}) m).symm.trans Ideal.mem_span_singleton

/-- The base residue ring of an ideal lying over a rational prime has `p` elements:
`Nat.card (ℤ ⧸ Q ∩ ℤ) = p` for `Q` over `(p)`.

This is the cardinality that `AlgHom.IsArithFrobAt` raises to over the base `ℤ`, so it is what
turns an abstract Frobenius congruence into the congruence `φ y ≡ y ^ p`. -/
theorem natCard_quotient_under_of_liesOver {S : Type*} [Ring S] {p : ℕ}
    (Q : Ideal S) [Q.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  rw [← Ideal.LiesOver.over (P := Q) (p := span {(p : ℤ)})]
  exact Int.card_ideal_quot p

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
