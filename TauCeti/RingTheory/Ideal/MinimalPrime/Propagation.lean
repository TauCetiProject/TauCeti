/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import TauCeti.RingTheory.KrullDimension.Quotient

/-!
# Propagating a property along the minimal primes of an ideal

Let `R` be a commutative ring, `𝔰` an ideal of `R` and `D₁` a natural number. Write
`dim 𝔭 = dim (R ⧸ 𝔭)`. The minimal primes of `𝔰` are its *components*, and two components `P, Q`
are *adjacent* when `dim (R ⧸ (P + Q)) ≥ D₁`. This file proves that a property of primes
(membership in a set `Good ⊆ Spec R`) propagates from one prime of large dimension to every
minimal prime of `R` in a set `TI`, provided the components are connected by chains of
adjacencies, and that two local propagation statements hold at a supply of *nice* primes: one for
nice primes in `TI` (in the application, primes of irreducible type), and one, along chains of
*links*, for nice primes in a set `TE` (primes of reducible type). Two nice primes of `TE` are
linked when some *thick* component lies in both.

This is the combinatorial core of the propagation of modularity from one irreducible component of
the spectrum of a deformation ring to all of them, along components that meet in large dimension
(the key proposition of Skinner and Wiles in the residually reducible case): `Good` is the set of
pro-modular primes, and the two local statements come from patching at the nice primes.

## Main results

* `TauCeti.mem_of_mem_minimalPrimes_of_propagation`: if some good prime of `TI` has dimension at
  least `D₁`, then every minimal prime of `R` lying in `TI` is good.

## References

* C. Skinner and A. Wiles, *Residually reducible representations and modular forms*, Publ. Math.
  IHÉS 89 (1999).
* The formal proof of the Riemann hypothesis by L. Alpöge (2026), whose propagation statement
  `UpperTheory.V.Pr.locProp` has these hypotheses and whose invariant along the chains of
  adjacent components is the one used here.
-/

public section

open PrimeSpectrum

namespace TauCeti

variable {R : Type*} [CommRing R] {TI TE Good Nice Thick : Set (PrimeSpectrum R)} {𝔰 : Ideal R}
  {D₁ : ℕ} {L : PrimeSpectrum R → PrimeSpectrum R → Prop}

/-- A nice prime of `TE` reached, along a chain for `L`, from a nice prime of `TE` that has a good
generization in `TI`. -/
private def Reached (TI TE Good Nice : Set (PrimeSpectrum R))
    (L : PrimeSpectrum R → PrimeSpectrum R → Prop) (n : PrimeSpectrum R) : Prop :=
  n ∈ Nice ∧ n ∈ TE ∧ ∃ n₀ ∈ Nice, n₀ ∈ TE ∧ (∃ 𝔭 ≤ n₀, 𝔭 ∈ TI ∧ 𝔭 ∈ Good) ∧
    Relation.ReflTransGen L n₀ n

/-- The invariant carried along chains of adjacent components: the component is good and in
`TI`, or it is thick and lies in a reached prime. -/
private def PropagationInv (TI TE Good Nice Thick : Set (PrimeSpectrum R))
    (L : PrimeSpectrum R → PrimeSpectrum R → Prop) (Q : PrimeSpectrum R) : Prop :=
  Q ∈ Good ∧ Q ∈ TI ∨ Q ∈ Thick ∧ ∃ n, Reached TI TE Good Nice L n ∧ Q ≤ n

/-- A prime in `TI` below a reached prime is good. -/
private theorem mem_of_le_reached
    (hP23 : ∀ p q, p ∈ Nice → p ∈ TE → q ∈ Nice → q ∈ TE → Relation.ReflTransGen L p q →
      (∃ 𝔭 ≤ p, 𝔭 ∈ TI ∧ 𝔭 ∈ Good) → ∀ 𝔮 ≤ q, 𝔮 ∈ TI → 𝔮 ∈ Good)
    {n 𝔮 : PrimeSpectrum R} (hn : Reached TI TE Good Nice L n) (h𝔮n : 𝔮 ≤ n) (h𝔮 : 𝔮 ∈ TI) :
    𝔮 ∈ Good := by
  obtain ⟨hnN, hnE, n₀, hN₀, hE₀, hgen, hchain⟩ := hn
  exact hP23 n₀ n hN₀ hE₀ hnN hnE hchain hgen 𝔮 h𝔮n h𝔮

/-- A component in `TI` or thick, below a reached prime, satisfies the invariant. -/
private theorem propagationInv_of_le_reached
    (hP23 : ∀ p q, p ∈ Nice → p ∈ TE → q ∈ Nice → q ∈ TE → Relation.ReflTransGen L p q →
      (∃ 𝔭 ≤ p, 𝔭 ∈ TI ∧ 𝔭 ∈ Good) → ∀ 𝔮 ≤ q, 𝔮 ∈ TI → 𝔮 ∈ Good)
    {Q n : PrimeSpectrum R} (hQ : Q ∈ TI ∨ Q ∈ Thick) (hn : Reached TI TE Good Nice L n)
    (hQn : Q ≤ n) : PropagationInv TI TE Good Nice Thick L Q := by
  by_cases hQI : Q ∈ TI
  · exact .inl ⟨mem_of_le_reached hP23 hn hQn hQI, hQI⟩
  · exact .inr ⟨hQ.resolve_left hQI, n, hn, hQn⟩

/-- A component below a good prime `𝔮` of dimension at least `D₁` which has a good generization
in `TI` satisfies the invariant. -/
private theorem propagationInv_of_le_mem
    (hGood : ∀ ⦃𝔭 𝔮 : PrimeSpectrum R⦄, 𝔭 ∈ Good → 𝔭 ≤ 𝔮 → 𝔮 ∈ Good)
    (hTI : ∀ ⦃𝔭 𝔮 : PrimeSpectrum R⦄, 𝔮 ∈ TI → 𝔭 ≤ 𝔮 → 𝔭 ∈ TI)
    (hNice : ∀ n ∈ Nice, n ∈ TI ∨ n ∈ TE)
    (hGoodNice : ∀ 𝔭 ∈ Good, (D₁ : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔭.asIdeal) →
      ∃ n ∈ Nice, 𝔭 ≤ n)
    (hThickNice : ∀ 𝔭 : PrimeSpectrum R, (D₁ : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔭.asIdeal) →
      ∀ Q ∈ Thick, Q.asIdeal ∈ 𝔰.minimalPrimes → Q ≤ 𝔭 → ∃ n ∈ Nice, n ∈ TE ∧ 𝔭 ≤ n)
    (hP1 : ∀ n ∈ Nice, n ∈ TI → n ∈ Good → ∀ 𝔭 ≤ n, 𝔭 ∈ Good)
    (hP23 : ∀ p q, p ∈ Nice → p ∈ TE → q ∈ Nice → q ∈ TE → Relation.ReflTransGen L p q →
      (∃ 𝔭 ≤ p, 𝔭 ∈ TI ∧ 𝔭 ∈ Good) → ∀ 𝔮 ≤ q, 𝔮 ∈ TI → 𝔮 ∈ Good)
    {Q 𝔮 𝔭 : PrimeSpectrum R} (hQc : Q.asIdeal ∈ 𝔰.minimalPrimes) (hQ : Q ∈ TI ∨ Q ∈ Thick)
    (hQ𝔮 : Q ≤ 𝔮) (h𝔮 : 𝔮 ∈ Good) (hdim : (D₁ : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔮.asIdeal))
    (h𝔭𝔮 : 𝔭 ≤ 𝔮) (h𝔭 : 𝔭 ∈ TI) (h𝔭G : 𝔭 ∈ Good) :
    PropagationInv TI TE Good Nice Thick L Q := by
  obtain ⟨n, hnN, h𝔮n⟩ := hGoodNice 𝔮 h𝔮 hdim
  rcases hNice n hnN with hnI | hnE
  · by_cases hQI : Q ∈ TI
    · exact .inl ⟨hP1 n hnN hnI (hGood h𝔮 h𝔮n) Q (hQ𝔮.trans h𝔮n), hQI⟩
    -- `Q` is thick, and `𝔮` is a good generization of `n`, hence in `TI`.
    obtain ⟨n', hn'N, hn'E, h𝔮n'⟩ := hThickNice 𝔮 hdim Q (hQ.resolve_left hQI) hQc hQ𝔮
    exact .inr ⟨hQ.resolve_left hQI, n',
      ⟨hn'N, hn'E, n', hn'N, hn'E, ⟨𝔮, h𝔮n', hTI hnI h𝔮n, h𝔮⟩, .refl⟩, hQ𝔮.trans h𝔮n'⟩
  · exact propagationInv_of_le_reached hP23 hQ
      ⟨hnN, hnE, n, hnN, hnE, ⟨𝔭, h𝔭𝔮.trans h𝔮n, h𝔭, h𝔭G⟩, .refl⟩ (hQ𝔮.trans h𝔮n)

/-- **Propagation along components.** Let `R` be a commutative ring, `TI, TE, Good, Nice, Thick`
sets of primes of `R`, `𝔰` an ideal of `R` and `D₁` a natural number. Call the minimal primes of
`𝔰` *components*, two components `P, Q` *adjacent* when `dim (R ⧸ (P + Q)) ≥ D₁`, and two nice
primes of `TE` *linked* when some thick component lies in both. Assume that

* `Good` is stable under specialization and `TI` under generization;
* every nice prime lies in `TI` or in `TE`;
* every good prime `𝔭` with `dim (R ⧸ 𝔭) ≥ D₁` lies in a nice prime;
* every prime `𝔭` with `dim (R ⧸ 𝔭) ≥ D₁` containing a thick component lies in a nice prime of
  `TE`;
* the minimal primes of `R` lying in `TI` are components;
* any two components are joined by a chain of adjacent components;
* every component lies in `TI` or is thick;
* (P1) every generization of a good nice prime of `TI` is good;
* (P23) if nice primes `p, q` of `TE` are joined by a chain of links and some generization of `p` in
  `TI` is good, then every generization of `q` in `TI` is good.

If some good prime of `TI` has `dim (R ⧸ 𝔭) ≥ D₁`, then every minimal prime of `R` lying in `TI`
is good. -/
theorem mem_of_mem_minimalPrimes_of_propagation
    (hGood : ∀ ⦃𝔭 𝔮 : PrimeSpectrum R⦄, 𝔭 ∈ Good → 𝔭 ≤ 𝔮 → 𝔮 ∈ Good)
    (hTI : ∀ ⦃𝔭 𝔮 : PrimeSpectrum R⦄, 𝔮 ∈ TI → 𝔭 ≤ 𝔮 → 𝔭 ∈ TI)
    (hNice : ∀ n ∈ Nice, n ∈ TI ∨ n ∈ TE)
    (hGoodNice : ∀ 𝔭 ∈ Good, (D₁ : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔭.asIdeal) →
      ∃ n ∈ Nice, 𝔭 ≤ n)
    (hThickNice : ∀ 𝔭 : PrimeSpectrum R, (D₁ : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔭.asIdeal) →
      ∀ Q ∈ Thick, Q.asIdeal ∈ 𝔰.minimalPrimes → Q ≤ 𝔭 → ∃ n ∈ Nice, n ∈ TE ∧ 𝔭 ≤ n)
    (hmin : ∀ 𝔭 ∈ TI, 𝔭.asIdeal ∈ minimalPrimes R → 𝔭.asIdeal ∈ 𝔰.minimalPrimes)
    (hchain : ∀ P Q : PrimeSpectrum R, P.asIdeal ∈ 𝔰.minimalPrimes → Q.asIdeal ∈ 𝔰.minimalPrimes →
      Relation.ReflTransGen (fun P Q : PrimeSpectrum R ↦ P.asIdeal ∈ 𝔰.minimalPrimes ∧
        Q.asIdeal ∈ 𝔰.minimalPrimes ∧
        (D₁ : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (P.asIdeal ⊔ Q.asIdeal))) P Q)
    (hcomp : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ 𝔰.minimalPrimes → Q ∈ TI ∨ Q ∈ Thick)
    (hP1 : ∀ n ∈ Nice, n ∈ TI → n ∈ Good → ∀ 𝔭 ≤ n, 𝔭 ∈ Good)
    (hP23 : ∀ p q, p ∈ Nice → p ∈ TE → q ∈ Nice → q ∈ TE →
      Relation.ReflTransGen (fun a b : PrimeSpectrum R ↦ a ∈ Nice ∧ a ∈ TE ∧ b ∈ Nice ∧ b ∈ TE ∧
        ∃ Q ∈ Thick, Q.asIdeal ∈ 𝔰.minimalPrimes ∧ Q ≤ a ∧ Q ≤ b) p q →
      (∃ 𝔭 ≤ p, 𝔭 ∈ TI ∧ 𝔭 ∈ Good) → ∀ 𝔮 ≤ q, 𝔮 ∈ TI → 𝔮 ∈ Good)
    (h₀ : ∃ 𝔭 ∈ TI, 𝔭 ∈ Good ∧ (D₁ : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔭.asIdeal))
    {𝔭 : PrimeSpectrum R} (h𝔭 : 𝔭 ∈ TI) (h𝔭min : 𝔭.asIdeal ∈ minimalPrimes R) : 𝔭 ∈ Good := by
  -- Start: a minimal prime `Q₀` of `R` below the given good prime `𝔭₀` satisfies the invariant.
  obtain ⟨𝔭₀, h𝔭₀I, h𝔭₀G, h𝔭₀dim⟩ := h₀
  obtain ⟨q, hq, hq𝔭₀⟩ := Ideal.exists_minimalPrimes_le (J := 𝔭₀.asIdeal) bot_le
  let Q₀ : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have hQ₀I : Q₀ ∈ TI := hTI h𝔭₀I hq𝔭₀
  have hQ₀c := hmin Q₀ hQ₀I hq
  -- The links between nice primes of `TE`.
  set L : PrimeSpectrum R → PrimeSpectrum R → Prop := fun a b ↦ a ∈ Nice ∧ a ∈ TE ∧ b ∈ Nice ∧
    b ∈ TE ∧ ∃ Q ∈ Thick, Q.asIdeal ∈ 𝔰.minimalPrimes ∧ Q ≤ a ∧ Q ≤ b
  have hinv₀ : PropagationInv TI TE Good Nice Thick L Q₀ :=
    propagationInv_of_le_mem hGood hTI hNice hGoodNice hThickNice hP1 hP23 hQ₀c (.inl hQ₀I) hq𝔭₀
      h𝔭₀G h𝔭₀dim le_rfl h𝔭₀I h𝔭₀G
  -- Step: the invariant passes from a component to an adjacent one.
  have hstep (Q Q' : PrimeSpectrum R) (hQc : Q.asIdeal ∈ 𝔰.minimalPrimes)
      (hQ'c : Q'.asIdeal ∈ 𝔰.minimalPrimes)
      (hdim : (D₁ : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (Q.asIdeal ⊔ Q'.asIdeal)))
      (hQ : PropagationInv TI TE Good Nice Thick L Q) :
      PropagationInv TI TE Good Nice Thick L Q' := by
    obtain ⟨𝔮, h𝔮, hdim𝔮⟩ := exists_le_and_le_ringKrullDim_quotient hdim
    have hQ𝔮 : Q ≤ 𝔮 := le_sup_left.trans h𝔮
    have hQ'𝔮 : Q' ≤ 𝔮 := le_sup_right.trans h𝔮
    rcases hQ with ⟨hG, hI⟩ | ⟨hT, n₁, ⟨hN₁, hE₁, n₀, hN₀, hE₀, hgen, hchain₁⟩, hQn₁⟩
    · exact propagationInv_of_le_mem hGood hTI hNice hGoodNice hThickNice hP1 hP23 hQ'c
        (hcomp Q' hQ'c) hQ'𝔮 (hGood hG hQ𝔮) hdim𝔮 hQ𝔮 hI hG
    -- `Q` is thick and lies in `n₁`; the prime `𝔮` contains it, so lies in a nice `n` of `TE`
    -- linked to `n₁` through `Q`.
    obtain ⟨n, hnN, hnE, h𝔮n⟩ := hThickNice 𝔮 hdim𝔮 Q hT hQc hQ𝔮
    exact propagationInv_of_le_reached hP23 (hcomp Q' hQ'c)
      ⟨hnN, hnE, n₀, hN₀, hE₀, hgen,
        hchain₁.tail ⟨hN₁, hE₁, hnN, hnE, Q, hT, hQc, hQn₁, hQ𝔮.trans h𝔮n⟩⟩ (hQ'𝔮.trans h𝔮n)
  have hinv := Relation.ReflTransGen.rec (motive := fun Q _ ↦ PropagationInv TI TE Good Nice Thick
    L Q) hinv₀ (fun _ hadj ih ↦ hstep _ _ hadj.1 hadj.2.1 hadj.2.2 ih)
    (hchain Q₀ 𝔭 hQ₀c (hmin 𝔭 h𝔭 h𝔭min))
  -- End: a component in `TI` satisfying the invariant is good.
  rcases hinv with ⟨hG, -⟩ | ⟨-, n, hn, h𝔭n⟩
  exacts [hG, mem_of_le_reached hP23 hn h𝔭n h𝔭]

end TauCeti
