/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import TauCeti.RingTheory.Nagata

import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.NoetherNormalization
import TauCeti.RingTheory.IntegralClosure.MvPolynomial

/-!
# Universally Japanese rings

A commutative ring `R` is *universally Japanese* if every domain of finite type over `R` is
Japanese (Stacks, Definition 10.162.1 (032R)). Unlike the Nagata condition, this asks nothing of
`R` itself beyond its finite-type domains, and in particular does not ask `R` to be Noetherian.
For Noetherian rings the two notions agree (Stacks, Proposition 10.162.15 (0334)); this file
proves the direction from universally Japanese to Nagata. Combined with the stability of the
universally Japanese property under finite-type algebras, this shows that every algebra of finite
type over a Noetherian universally Japanese ring is Nagata.

The basic example is a field. By Noether normalization, a domain of finite type over a field `k`
is a finite extension of a polynomial ring `k[X_1, …, X_r]`, which is Japanese
(`TauCeti.Ring.IsJapanese.mvPolynomial`), and finite extension domains of Japanese domains are
Japanese (`TauCeti.Ring.IsJapanese.of_finite`). Hence algebras of finite type over a field are
Nagata.

## Main definitions and results

* `TauCeti.Ring.IsUniversallyJapanese R`: the ring `R` is universally Japanese.
* `TauCeti.Ring.IsUniversallyJapanese.isJapanese`: a domain of finite type over a universally
  Japanese ring, in any universe, is Japanese.
* `TauCeti.Ring.IsUniversallyJapanese.of_finiteType`: an algebra of finite type over a universally
  Japanese ring is universally Japanese (Stacks, Lemma 10.162.4 (032S)); in particular being
  universally Japanese is invariant under ring isomorphisms
  (`RingEquiv.isUniversallyJapanese`).
* `TauCeti.Ring.IsUniversallyJapanese.isNagata`: a Noetherian universally Japanese ring is Nagata
  (one direction of Stacks, Proposition 10.162.15 (0334)), and
  `TauCeti.Ring.IsUniversallyJapanese.isNagata_of_finiteType`: so is every algebra of finite type
  over it, for instance every algebra of finite type over a field.
* `TauCeti.Ring.IsUniversallyJapanese.of_field`: a field is universally Japanese (Stacks,
  Proposition 10.162.16 (0335), part (1)).
* `TauCeti.Ring.IsUniversallyJapanese.of_forall_isIdempotentElem`: a ring all of whose elements
  are idempotent, such as a Boolean ring, is universally Japanese. Such a ring need not be
  Noetherian, so universally Japanese rings need not be Nagata.

## References

* [Stacks Project, Section 10.162 (032Q)](https://stacks.math.columbia.edu/tag/032Q)
-/

public section

universe u v

namespace TauCeti.Ring

/-- A commutative ring `R` is *universally Japanese* if every domain of finite type over `R` is
Japanese. Stacks, Definition 10.162.1 (032R). The definition quantifies over algebras in the
universe of `R`; `IsUniversallyJapanese.isJapanese` gives the property in every universe. -/
class IsUniversallyJapanese (R : Type u) [CommRing R] : Prop where
  isJapanese_of_finiteType (S : Type u) [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.FiniteType R S] : IsJapanese S

variable {R : Type u} [CommRing R]

namespace IsUniversallyJapanese

variable (R) in
/-- A domain of finite type over a universally Japanese ring is Japanese. -/
theorem isJapanese (S : Type v) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]
    [IsUniversallyJapanese R] : IsJapanese S := by
  -- `S` is isomorphic to a quotient of a polynomial ring over `R`, which lies in the universe
  -- of `R`.
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have : IsDomain (MvPolynomial (Fin n) R ⧸ RingHom.ker f) := e.toMulEquiv.isDomain
  have := isJapanese_of_finiteType (R := R) (MvPolynomial (Fin n) R ⧸ RingHom.ker f)
  exact e.toRingEquiv.isJapanese

/-- A universally Japanese domain is Japanese. -/
instance (priority := 100) isJapanese_self [IsDomain R] [IsUniversallyJapanese R] :
    IsJapanese R :=
  isJapanese R R

variable (R) in
/-- An algebra of finite type over a universally Japanese ring is universally Japanese. Stacks,
Lemma 10.162.4 (032S). -/
theorem of_finiteType (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [IsUniversallyJapanese R] : IsUniversallyJapanese S where
  isJapanese_of_finiteType T _ _ _ _ :=
    let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
    have : IsScalarTower R S T := .of_algebraMap_eq' rfl
    have : Algebra.FiniteType R T := .trans (S := S) ‹_› ‹_›
    isJapanese R T

/-- Being universally Japanese is invariant under ring isomorphisms. -/
theorem _root_.RingEquiv.isUniversallyJapanese {S : Type v} [CommRing S]
    [IsUniversallyJapanese R] (e : R ≃+* S) : IsUniversallyJapanese S :=
  let : Algebra R S := e.toRingHom.toAlgebra
  have : Algebra.FiniteType R S := .of_surjective (Algebra.ofId R S) e.surjective
  of_finiteType R S

/-- A Noetherian universally Japanese ring is Nagata: each quotient by a prime ideal is a domain
of finite type over it. This is one direction of Stacks, Proposition 10.162.15 (0334). -/
theorem isNagata [IsNoetherianRing R] [IsUniversallyJapanese R] : IsNagata R where
  isJapanese_quotient p _ := isJapanese R (R ⧸ p)

variable (R) in
/-- An algebra of finite type over a Noetherian universally Japanese ring is Nagata. -/
theorem isNagata_of_finiteType (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [IsNoetherianRing R] [IsUniversallyJapanese R] : IsNagata S :=
  have := Algebra.FiniteType.isNoetherianRing R S
  have := of_finiteType R S
  isNagata

/-- A field is universally Japanese: by Noether normalization, a domain of finite type over a
field `k` is a finite extension of a polynomial ring over `k`, which is Japanese. Stacks,
Proposition 10.162.16 (0335), part (1). -/
instance of_field (k : Type u) [Field k] : IsUniversallyJapanese k where
  isJapanese_of_finiteType S _ _ _ _ := by
    obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k S
    let : Algebra (MvPolynomial (Fin s) k) S := g.toRingHom.toAlgebra
    have : Module.Finite (MvPolynomial (Fin s) k) S := RingHom.finite_algebraMap.mp hfin
    have : FaithfulSMul (MvPolynomial (Fin s) k) S :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
    exact IsJapanese.of_finite (MvPolynomial (Fin s) k) S

/-- A ring in which every element is idempotent, such as a Boolean ring, is universally Japanese.
Every idempotent of a domain is `0` or `1`, so a domain of finite type over such a ring has
characteristic two and is of finite type over the field `ZMod 2`. Such a ring need not be
Noetherian, for instance the ring of all `ZMod 2`-valued sequences; so being universally Japanese
does not imply being Nagata without the Noetherian hypothesis of `isNagata`. -/
theorem of_forall_isIdempotentElem (h : ∀ r : R, IsIdempotentElem r) :
    IsUniversallyJapanese R where
  isJapanese_of_finiteType S _ _ _ _ := by
    have hR (r : R) : algebraMap R S r = 0 ∨ algebraMap R S r = 1 :=
      IsIdempotentElem.iff_eq_zero_or_one.mp ((h r).map (algebraMap R S))
    -- In particular `2 = 0` in `S`, as `2 = 1` would force `1 = 0`.
    have h2 : (2 : S) = 0 := by
      have := hR 2
      rw [map_ofNat] at this
      refine this.resolve_right fun h₂ ↦ one_ne_zero (α := S) ?_
      linear_combination h₂
    have : CharP S 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    let : Algebra (ZMod 2) S := ZMod.algebra S 2
    -- The generators of `S` over `R` generate it over `ZMod 2`, as `R` maps into `{0, 1}`.
    obtain ⟨t, ht⟩ := ‹Algebra.FiniteType R S›.out
    have : Algebra.FiniteType (ZMod 2) S := by
      refine ⟨t, Algebra.eq_top_iff.mpr fun x ↦ ?_⟩
      have hx : x ∈ Algebra.adjoin R (t : Set S) := ht ▸ Algebra.mem_top
      induction hx using Algebra.adjoin_induction with
      | mem x hx => exact Algebra.subset_adjoin hx
      | algebraMap r => rcases hR r with h | h <;> rw [h]; exacts [zero_mem _, one_mem _]
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy
    exact isJapanese (ZMod 2) S

end IsUniversallyJapanese

end TauCeti.Ring
