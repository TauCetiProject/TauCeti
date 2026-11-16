/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Residue cardinality for maximal ideals lying over maximal ideals

Let `R → S` be an algebra of commutative rings and let `q` be a maximal ideal of `S` lying over a
maximal ideal `p` of `R`. When `S ⧸ q` is finite, its cardinality is
`Nat.card (R ⧸ p) ^ q.inertiaDeg R` without Mathlib's `[Module.Finite R S]` hypothesis from
`Ideal.cardQuot_pow_inertiaDeg`.

## Main results

* `Ideal.natCard_quotient_eq_pow_inertiaDeg`: `Nat.card (S ⧸ q) = Nat.card (R ⧸ p) ^ q.inertiaDeg R`
  for maximal ideals `q ∣ p` with `Finite (S ⧸ q)`.
-/

public section

namespace Ideal

/-- For a maximal ideal `q` of `S` lying over a maximal ideal `p` of `R` with `S ⧸ q` finite, the
residue field `S ⧸ q` has `Nat.card (R ⧸ p) ^ q.inertiaDeg R` elements. Unlike
`Ideal.cardQuot_pow_inertiaDeg`, no `Module.Finite R S` assumption is needed. -/
theorem natCard_quotient_eq_pow_inertiaDeg {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [p.IsMaximal] [q.IsMaximal] [q.LiesOver p] [Finite (S ⧸ q)] :
    Nat.card (S ⧸ q) = Nat.card (R ⧸ p) ^ q.inertiaDeg R := by
  let _ : Field (R ⧸ p) := Ideal.Quotient.field p
  have : Finite (R ⧸ p) := .of_injective _ (FaithfulSMul.algebraMap_injective (R ⧸ p) (S ⧸ q))
  let _ : Fintype (R ⧸ p) := .ofFinite _
  let _ : Fintype (S ⧸ q) := .ofFinite _
  rw [Ideal.inertiaDeg_eq_of_isMaximal p q, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank

end Ideal
