/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.IntegralDomain
import TauCeti.RingTheory.Ideal.LiesOver

/-!
# Inertia degree and residue cardinality without ambient module finiteness

Mathlib's `Ideal.cardQuot_pow_inertiaDeg` and `Ideal.absNorm_pow_inertiaDeg` relate the residue
cardinality and absolute ideal norm via the inertia degree `q.inertiaDeg R`, assuming
`[Module.Finite R S]` (and `[Infinite R] [Infinite S]` for `absNorm`). In settings such as
localizations, `S`-integers, or completions, `S` need not be finite as an `R`-module, while the
residue ring `S ⧸ q` is still finite.

This file provides the quotient-finite counterparts `Ideal.cardQuot_pow_inertiaDeg_of_finite` and
`Ideal.absNorm_pow_inertiaDeg_of_finite` under `[Finite (S ⧸ q)]`.

## Main results

* `Ideal.cardQuot_pow_inertiaDeg_of_finite`: `p.cardQuot ^ q.inertiaDeg R = q.cardQuot` when
  `S ⧸ q` is finite.
* `Ideal.absNorm_pow_inertiaDeg_of_finite`: `p.absNorm ^ q.inertiaDeg R = q.absNorm` for nonzero
  ideals `p` and `q` when `S ⧸ q` is finite.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (q : Ideal S)

/-- **Quotient-cardinality formula for the inertia degree** assuming only that `S ⧸ q` is finite,
without assuming `[Module.Finite R S]`. -/
theorem cardQuot_pow_inertiaDeg_of_finite [q.IsPrime] [q.LiesOver p] [Finite (S ⧸ q)] :
    p.cardQuot ^ q.inertiaDeg R = q.cardQuot := by
  have _ : p.IsPrime := isPrime_of_liesOver q p
  have _ : Finite (R ⧸ p) := finite_quotient_of_liesOver p q
  have _ : q.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (S ⧸ q))
  have _ : p.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R ⧸ p))
  let _ : Field (R ⧸ p) := Quotient.field p
  have _ : Module.Finite (R ⧸ p) (S ⧸ q) := Module.Finite.of_finite
  rw [inertiaDeg_eq_of_isMaximal p q]
  exact Module.natCard_eq_pow_finrank.symm

/-- **Absolute-norm formula for the inertia degree** for nonzero ideals `p` and `q` assuming only
that `S ⧸ q` is finite, without assuming `[Module.Finite R S]`, `[Infinite R]`, or `[Infinite S]`.
-/
theorem absNorm_pow_inertiaDeg_of_finite [IsDedekindDomain R] [IsDedekindDomain S]
    [q.IsPrime] [q.LiesOver p] [Finite (S ⧸ q)] (hp : p ≠ ⊥) (hq : q ≠ ⊥) :
    p.absNorm ^ q.inertiaDeg R = q.absNorm := by
  rw [absNorm_of_ne_bot hp, absNorm_of_ne_bot hq, cardQuot_pow_inertiaDeg_of_finite p q]

end Ideal
