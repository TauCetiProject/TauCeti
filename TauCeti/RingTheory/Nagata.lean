/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import TauCeti.RingTheory.Japanese

import Mathlib.RingTheory.Finiteness.Quotient

/-!
# Nagata rings

A commutative ring `R` is *Nagata* if it is Noetherian and `R ⧸ p` is a Japanese domain for every
prime ideal `p` of `R` (Stacks, Definition 10.162.1 (032R)). Nagata rings are the rings over which
normalization is well behaved: the normalization of an integral scheme whose affine opens have
Nagata section rings, in a finite extension of its function field, is finite (Stacks, Lemma 29.54.14
(0AVK)). Quasi-excellent rings, for instance complete Noetherian local rings and algebras of finite
type over a field or over `ℤ`, are Nagata (Stacks, Lemma 15.53.5 (07QV)); this file develops the
definition and its elementary permanence properties and examples.

## Main definitions and results

* `TauCeti.Ring.IsNagata R`: the ring `R` is Nagata.
* `TauCeti.Ring.IsNagata.of_finite`: a finite algebra over a Nagata ring is Nagata (Stacks,
  Lemma 10.162.5 (032T)). In particular quotients of Nagata rings are Nagata
  (`TauCeti.Ring.IsNagata.quotient`), and being Nagata is invariant under ring isomorphisms.
* `TauCeti.Ring.IsNagata.isJapanese`: a Nagata domain is Japanese.
* `TauCeti.Ring.IsNagata.of_krullDimLE_zero`: a Noetherian ring of Krull dimension zero, such as
  a field or an Artinian ring, is Nagata.
* `TauCeti.Ring.isNagata_iff_isJapanese`: a Noetherian domain of Krull dimension at most one is
  Nagata if and only if it is Japanese (Stacks, Example 10.162.17 (09E1) for discrete valuation
  rings). Hence `ℤ`, and every Dedekind domain whose fraction field is perfect, is Nagata.

## Implementation notes

The rules producing `IsNagata` from `IsNoetherianRing` and dimension hypotheses are theorems rather
than instances: as `IsNagata` extends `IsNoetherianRing`, such instances would make every search for
`IsNoetherianRing` or `IsJapanese` cycle through `IsNagata`. Fields are the exception, with their
own instance.

## References

* [Stacks Project, Section 10.162 (032Q)](https://stacks.math.columbia.edu/tag/032Q)
-/

public section

universe u v

namespace TauCeti.Ring

/-- A commutative ring `R` is *Nagata* if it is Noetherian and the quotient `R ⧸ p` by every prime
ideal `p` is a Japanese domain. Stacks, Definition 10.162.1 (032R). -/
class IsNagata (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  isJapanese_quotient (p : Ideal R) [p.IsPrime] : IsJapanese (R ⧸ p)

attribute [instance] IsNagata.isJapanese_quotient

variable {R : Type u} [CommRing R]

namespace IsNagata

variable (R) in
/-- A finite algebra over a Nagata ring is Nagata. Stacks, Lemma 10.162.5 (032T). -/
theorem of_finite (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsNagata R] :
    IsNagata S where
  toIsNoetherian := IsNoetherianRing.of_finite R S
  -- For a prime `q` of `S`, the domain `S ⧸ q` is a finite extension of `R ⧸ (q ∩ R)`.
  isJapanese_quotient q _ :=
    have : FaithfulSMul (R ⧸ q.under R) (S ⧸ q) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
    IsJapanese.of_finite (R ⧸ q.under R) (S ⧸ q)

/-- A quotient of a Nagata ring is Nagata. -/
instance quotient [IsNagata R] (I : Ideal R) : IsNagata (R ⧸ I) :=
  of_finite R (R ⧸ I)

/-- Being Nagata is invariant under ring isomorphisms. -/
theorem _root_.RingEquiv.isNagata {S : Type v} [CommRing S] [IsNagata R] (e : R ≃+* S) :
    IsNagata S :=
  let : Algebra R S := e.toRingHom.toAlgebra
  have : Module.Finite R S := RingHom.Finite.of_surjective _ e.surjective
  of_finite R S

/-- A Nagata domain is Japanese. -/
instance (priority := 100) isJapanese [IsDomain R] [IsNagata R] : IsJapanese R :=
  (RingEquiv.quotientBot R).isJapanese

/-- A Noetherian ring of Krull dimension zero, for instance an Artinian ring or the zero ring, is
Nagata. -/
theorem of_krullDimLE_zero [IsNoetherianRing R] [Ring.KrullDimLE 0 R] : IsNagata R where
  -- Every prime ideal is maximal, so every prime quotient is a field.
  isJapanese_quotient p _ :=
    let : Field (R ⧸ p) := Ideal.Quotient.field p
    inferInstance

/-- A field is Nagata. -/
instance of_field (k : Type u) [Field k] : IsNagata k :=
  of_krullDimLE_zero

/-- A Noetherian Japanese domain of Krull dimension at most one is Nagata. -/
theorem of_isJapanese [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsJapanese R] :
    IsNagata R where
  -- The quotient by the zero ideal is `R` itself, and the quotients by nonzero primes are fields.
  isJapanese_quotient p _ := by
    rcases eq_or_ne p ⊥ with rfl | hp
    · exact (RingEquiv.quotientBot R).symm.isJapanese
    · have := Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hp
      let : Field (R ⧸ p) := Ideal.Quotient.field p
      infer_instance

end IsNagata

/-- A Noetherian domain of Krull dimension at most one, for instance a Dedekind domain or a
discrete valuation ring, is Nagata if and only if it is Japanese. Stacks, Example 10.162.17 (09E1),
for discrete valuation rings. -/
theorem isNagata_iff_isJapanese [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] :
    IsNagata R ↔ IsJapanese R :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ .of_isJapanese⟩

end TauCeti.Ring
