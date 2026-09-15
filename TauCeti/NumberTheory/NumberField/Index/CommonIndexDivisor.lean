/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import TauCeti.NumberTheory.NumberField.Index.Exponent

/-!
# Common index divisors

A prime `p` is a *common index divisor* of a number field `K` when it divides the index
`[𝓞 K : ℤ[θ]]` of **every** integral primitive element `θ`. Such a prime obstructs monogenicity:
`𝓞 K = ℤ[θ]` would force `index θ = 1`.

The obstruction is a counting argument. Kummer–Dedekind puts the primes of `𝓞 K` above `p` in
bijection with the distinct monic irreducible factors of `minpoly ℤ θ` modulo `p`, matching the
residue degree of a prime with the degree of its factor — but only for a `θ` whose conductor
exponent is prime to `p`. So if `p` has more primes of residue degree `d` than there are monic
irreducible polynomials of degree `d` available over `𝔽_p`, no `θ` can satisfy that hypothesis,
and then `p` divides `exponent θ`, hence `index θ`.

## Main definitions

* `TauCeti.NumberField.IsCommonIndexDivisor`: `p` divides the index of every integral primitive
  element.
* `TauCeti.NumberField.primesOverOfInertiaDeg`: the primes above `p` of a fixed residue degree.

## Main results

* `TauCeti.NumberField.ncard_primesOverOfInertiaDeg_le`: the Kummer–Dedekind counting bound.
* `TauCeti.NumberField.isCommonIndexDivisor_of_card_lt_ncard`: the counting obstruction.

The converse is Hensel's criterion — the common index divisors are exactly the primes whose
splitting type is not realizable modulo `p` — and is deliberately not proved here.

## References

* [J. Neukirch, *Algebraic number theory*][neukirch1999], III §2 Exercise 1.
-/

public section

open scoped NumberField
open Ideal Polynomial RingOfIntegers NumberField.Ideal

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- `p` is a **common index divisor** of `K` when it divides the index `[𝓞 K : ℤ[θ]]` of every
integral primitive element `θ` of `K`.

A common index divisor obstructs monogenicity. If `K` admits no integral primitive element the
condition holds vacuously, so the predicate carries content only when such a `θ` exists. -/
def IsCommonIndexDivisor (p : ℕ) (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ θ : IntegralPrimitiveElement K, p ∣ θ.index

variable (K) in
/-- The primes of `𝓞 K` above `p` whose residue degree over `ℤ` is `d`. -/
def primesOverOfInertiaDeg (d : ℕ) : Set ((span {(p : ℤ)}).primesOver (𝓞 K)) :=
  {Q | (Q : Ideal (𝓞 K)).inertiaDeg ℤ = d}

/-- The Kummer–Dedekind bijection sends a prime above `p` of residue degree `d` to a monic
irreducible factor of `minpoly ℤ θ` modulo `p` of degree `d`. -/
private theorem mem_filter_monicFactorsMod_of_mem_primesOverOfInertiaDeg {θ : 𝓞 K}
    (hp : ¬ p ∣ exponent θ) {d : ℕ}
    (Q : (span {(p : ℤ)}).primesOver (𝓞 K))
    (hQ : Q ∈ primesOverOfInertiaDeg K p d) :
    ((primesOverSpanEquivMonicFactorsMod hp Q : (ZMod p)[X])) ∈
      (monicFactorsMod θ p).filter fun R => R.natDegree = d := by
  classical
  refine Finset.mem_filter.mpr ⟨(primesOverSpanEquivMonicFactorsMod hp Q).2, ?_⟩
  -- The degree lemma is stated at `.symm`; rewrite `Q` as `.symm (e Q)` to apply it.
  have h := inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp
    (primesOverSpanEquivMonicFactorsMod hp Q).2
  rw [Subtype.coe_eta, Equiv.symm_apply_apply] at h
  exact h ▸ hQ

/-- **The Kummer–Dedekind counting bound.** For a `θ` whose conductor exponent is prime to `p`,
the primes of `𝓞 K` above `p` with residue degree `d` are no more numerous than the degree-`d`
monic irreducible factors of `minpoly ℤ θ` modulo `p`. -/
theorem ncard_primesOverOfInertiaDeg_le {θ : 𝓞 K} (hp : ¬ p ∣ exponent θ) (d : ℕ) :
    (primesOverOfInertiaDeg K p d).ncard ≤
      ((monicFactorsMod θ p).filter fun Q => Q.natDegree = d).card := by
  classical
  have hinj : Set.InjOn
      (fun Q => (primesOverSpanEquivMonicFactorsMod hp Q : (ZMod p)[X]))
      (primesOverOfInertiaDeg K p d) := fun _ _ _ _ h =>
    (primesOverSpanEquivMonicFactorsMod hp).injective (Subtype.ext h)
  rw [← Set.ncard_coe_finset ((monicFactorsMod θ p).filter fun Q => Q.natDegree = d)]
  exact Set.ncard_le_ncard_of_injOn _
    (mem_filter_monicFactorsMod_of_mem_primesOverOfInertiaDeg p hp) hinj
    (Finset.finite_toSet _)

/-- **The counting obstruction.** If every integral primitive element offers at most `N` monic
irreducible factors of degree `d`, while `p` has more than `N` primes of residue degree `d`, then
`p` divides the index of every integral primitive element.

The bound `N` is supplied by the caller: over `𝔽_p` the monic irreducibles of degree `d` are
finite in number, so such an `N` always exists, but this statement does not need its value. -/
theorem isCommonIndexDivisor_of_card_lt_ncard {d N : ℕ}
    (hN : ∀ θ : 𝓞 K, ((monicFactorsMod θ p).filter fun Q => Q.natDegree = d).card ≤ N)
    (hlt : N < (primesOverOfInertiaDeg K p d).ncard) :
    IsCommonIndexDivisor p K := by
  intro θ
  by_contra hdvd
  -- A `θ` escaping `p` in the index also escapes it in the conductor exponent.
  have hexp : ¬ p ∣ exponent (θ : 𝓞 K) := fun h =>
    hdvd ((IntegralPrimitiveElement.dvd_index_iff_dvd_exponent θ).mpr h)
  exact absurd (hlt.trans_le (ncard_primesOverOfInertiaDeg_le p hexp d)) (not_lt.mpr (hN θ))

end TauCeti.NumberField
