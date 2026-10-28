/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import TauCeti.Order.Catenary

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Catenary rings

A commutative ring `R` is *catenary* if for every pair of primes `p ⊆ q` the strict chains of
primes from `p` to `q` have bounded length and all saturated chains of primes from `p` to `q` have
the same length (Stacks, Definition 10.105.1 (00NI)). No Noetherian, local or dimension hypothesis
is imposed. Catenarity is the dimension-theoretic part of excellence: an excellent ring is a
quasi-excellent ring all of whose finite type algebras are catenary.

The predicate is the order-theoretic `TauCeti.Order.IsCatenary` of the prime spectrum, so it
transports along the order isomorphisms that Mathlib provides between prime spectra.

## Main definitions and results

* `TauCeti.Excellence.IsCatenary R`: the ring `R` is catenary.
* `RingHom.isCatenary_of_surjective`: a quotient of a catenary ring is catenary
  (Stacks, Lemma 10.105.7 (00NK)); in particular catenarity is invariant under ring isomorphism.
* `Submonoid.isCatenary_of_isLocalization`: a localization of a catenary ring is catenary
  (Stacks, Lemma 10.105.4 (00NJ)).
* `TauCeti.Excellence.isCatenary_iff_forall_isMaximal`: a ring is catenary if and only if its
  localizations at all maximal ideals are (Stacks, Lemma 10.105.6 (0AUN)); equivalently, its
  localizations at all prime ideals are (`TauCeti.Excellence.isCatenary_iff_forall_isPrime`).
* A ring of Krull dimension at most one, such as a field, `ℤ` or a Dedekind domain, is catenary.
* `PrimeSpectrum.krullDim_Icc`: the Krull dimension of the interval `[p, q]` of `Spec R` is the
  height of `q / p` in `R / p`.
* `TauCeti.Excellence.isCatenary_iff_height_add`: a ring is catenary if and only if, for primes
  `p ⊆ q ⊆ r`, the heights `ht (q / p)` are finite and `ht (r / p) = ht (q / p) + ht (r / q)`;
  for Noetherian rings the finiteness is automatic
  (`TauCeti.Excellence.isCatenary_iff_height_add_of_isNoetherianRing`).
-/

public section

namespace TauCeti.Excellence

/-- A commutative ring `R` is *catenary* if for all primes `p ⊆ q` of `R` the strict chains of
primes `p = p₀ ⊊ p₁ ⊊ ⋯ ⊊ pₙ = q` have bounded length, and any two saturated chains of primes from
`p` to `q` (no prime lying strictly between consecutive members) have the same length.
Stacks, Definition 10.105.1 (00NI). -/
abbrev IsCatenary (R : Type*) [CommSemiring R] : Prop :=
  Order.IsCatenary (PrimeSpectrum R)

end TauCeti.Excellence

namespace RingHom

variable {R S : Type*}

/-- A ring receiving a surjection from a catenary ring is catenary: the primes of `S` are the
primes of `R` containing the kernel, an upper set of `Spec R`. Stacks, Lemma 10.105.7 (00NK). -/
theorem isCatenary_of_surjective [CommRing R] [CommRing S] [TauCeti.Excellence.IsCatenary R]
    (f : R →+* S) (hf : Function.Surjective f) : TauCeti.Excellence.IsCatenary S :=
  have : (PrimeSpectrum.zeroLocus (RingHom.ker f : Set R)).OrdConnected :=
    IsUpperSet.ordConnected fun _ _ hpq hp => by
      rw [PrimeSpectrum.mem_zeroLocus] at hp ⊢
      exact hp.trans (SetLike.coe_subset_coe.2 hpq)
  (Ideal.primeSpectrumOrderIsoZeroLocusOfSurj f hf rfl).isCatenary

end RingHom

namespace RingEquiv

variable {R S : Type*}

/-- Catenarity is invariant under ring isomorphism. -/
theorem isCatenary [CommSemiring R] [CommSemiring S] [TauCeti.Excellence.IsCatenary R]
    (e : R ≃+* S) : TauCeti.Excellence.IsCatenary S :=
  (PrimeSpectrum.comapEquiv e).symm.isCatenary

end RingEquiv

namespace Ideal

variable {R : Type*}

/-- A quotient of a catenary ring is catenary. Stacks, Lemma 10.105.7 (00NK). -/
instance isCatenary_quotient [CommRing R] [TauCeti.Excellence.IsCatenary R] (I : Ideal R) :
    TauCeti.Excellence.IsCatenary (R ⧸ I) :=
  (Ideal.Quotient.mk I).isCatenary_of_surjective Ideal.Quotient.mk_surjective

end Ideal


namespace Submonoid

variable {R S : Type*}

/-- A localization of a catenary ring is catenary: the primes of `S` are the primes of `R`
disjoint from `M`, a lower set of `Spec R`. Stacks, Lemma 10.105.4 (00NJ). -/
theorem isCatenary_of_isLocalization [CommSemiring R] [CommSemiring S] [Algebra R S]
    [TauCeti.Excellence.IsCatenary R] (M : Submonoid R) [IsLocalization M S] :
    TauCeti.Excellence.IsCatenary S :=
  have : {p : PrimeSpectrum R | Disjoint (M : Set R) p.asIdeal}.OrdConnected :=
    IsLowerSet.ordConnected fun _ _ hqp hp => hp.mono_right (SetLike.coe_subset_coe.2 hqp)
  -- `IsLocalization.primeSpectrumOrderIso` lands in the subtype of this order-connected set.
  have : TauCeti.Order.IsCatenary {p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal} :=
    Set.isCatenary {p : PrimeSpectrum R | Disjoint (M : Set R) p.asIdeal}
  (IsLocalization.primeSpectrumOrderIso M S).isCatenary

/-- A localization of a catenary ring is catenary. Stacks, Lemma 10.105.4 (00NJ). -/
instance isCatenary_localization [CommSemiring R] [TauCeti.Excellence.IsCatenary R]
    (M : Submonoid R) : TauCeti.Excellence.IsCatenary (Localization M) :=
  M.isCatenary_of_isLocalization

end Submonoid

namespace PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- The Krull dimension of the interval `[p, q]` of prime ideals of `R` is the height of the
prime ideal `q / p` of `R / p`. -/
theorem krullDim_Icc {p q : PrimeSpectrum R} (hpq : p ≤ q) :
    Order.krullDim (Set.Icc p q) = (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  let e := p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  have hmem {x : PrimeSpectrum R} : x ∈ zeroLocus (p.asIdeal : Set R) ↔ p ≤ x :=
    (mem_zeroLocus _ _).trans SetLike.coe_subset_coe
  let Q := e.symm ⟨q, hmem.2 hpq⟩
  -- By construction, the inverse of `e` sends `q` to its image `q / p` in `R / p`.
  have hQ : Q.asIdeal = q.asIdeal.map (Ideal.Quotient.mk p.asIdeal) := rfl
  -- The primes of `R / p` below `q / p` correspond to the primes of `R` between `p` and `q`.
  let f : Set.Icc p q ≃o Set.Iic Q :=
    { toFun x := ⟨e.symm ⟨x, hmem.2 (Set.mem_Icc.1 x.2).1⟩,
        e.symm.monotone (Subtype.mk_le_mk.2 (Set.mem_Icc.1 x.2).2)⟩
      invFun y := ⟨e y, hmem.1 (e y).2, Subtype.coe_le_coe.2 ((e.monotone y.2).trans_eq
        (by simp [Q]) : e y ≤ ⟨q, hmem.2 hpq⟩)⟩
      left_inv x := by simp
      right_inv y := by simp
      map_rel_iff' := e.symm.le_iff_le }
  rw [← hQ, height_eq_orderHeight, Order.height_eq_krullDim_Iic, Order.krullDim_eq_of_orderIso f]

end PrimeSpectrum

namespace TauCeti.Excellence

/-- A ring is catenary if and only if its localizations at all maximal ideals are catenary. A
chain of primes ending at `q` consists of primes contained in a maximal ideal `m ⊇ q`, and these
are the primes of `R_m`. Stacks, Lemma 10.105.6 (0AUN). -/
theorem isCatenary_iff_forall_isMaximal {R : Type*} [CommSemiring R] :
    IsCatenary R ↔ ∀ (m : Ideal R) [m.IsMaximal], IsCatenary (Localization.AtPrime m) := by
  refine ⟨fun _ m _ => inferInstance, fun h =>
    Order.IsCatenary.of_forall_exists_ordConnected fun p q hpq => ?_⟩
  obtain ⟨m, hm, hqm⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
  exact ⟨Set.Iic ⟨m, hm.isPrime⟩, Set.ordConnected_Iic, hpq.trans hqm, hqm,
    (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime m) m).symm.isCatenary⟩

/-- A ring is catenary if and only if its quotients by all minimal primes are catenary. A chain of
primes starting at `p` consists of primes containing a minimal prime `p₀ ⊆ p`, and these are the
primes of `R ⧸ p₀`. No Noetherian hypothesis is needed. Stacks, Lemma 10.105.8 (0AUP). -/
theorem isCatenary_iff_forall_minimalPrimes {R : Type*} [CommRing R] :
    IsCatenary R ↔ ∀ p ∈ minimalPrimes R, IsCatenary (R ⧸ p) := by
  refine ⟨fun _ p _ => inferInstance, fun h =>
    Order.IsCatenary.of_forall_exists_ordConnected fun p q hpq => ?_⟩
  obtain ⟨p₀, hp₀, hp₀p⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ p.asIdeal)
  have := h p₀ hp₀
  have : (PrimeSpectrum.zeroLocus (p₀ : Set R)).OrdConnected :=
    IsUpperSet.ordConnected fun _ _ hpq hp => by
      rw [PrimeSpectrum.mem_zeroLocus] at hp ⊢
      exact hp.trans (SetLike.coe_subset_coe.2 hpq)
  exact ⟨_, this, (PrimeSpectrum.mem_zeroLocus _ _).2 hp₀p,
    (PrimeSpectrum.mem_zeroLocus _ _).2 (hp₀p.trans hpq),
    (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p₀).symm.isCatenary⟩

/-- A ring is catenary if and only if its localizations at all prime ideals are catenary.
Stacks, Lemma 10.105.6 (0AUN). -/
theorem isCatenary_iff_forall_isPrime {R : Type*} [CommSemiring R] :
    IsCatenary R ↔ ∀ (q : Ideal R) [q.IsPrime], IsCatenary (Localization.AtPrime q) :=
  ⟨fun _ _ _ => inferInstance, fun h => isCatenary_iff_forall_isMaximal.2 fun m _ => h m⟩

/-- A ring is catenary if and only if, for all primes `p ⊆ q ⊆ r`, the height of `q / p` in `R / p`
is finite and heights are additive: `ht (r / p) = ht (q / p) + ht (r / q)`. This is the
characterisation of catenary spaces by additivity of codimension (Stacks, Lemma 5.11.6 (02I6))
applied to `Spec R`, using that `R` is catenary if and only if `Spec R` is (Stacks, Lemma 10.105.2
(02IH)). -/
theorem isCatenary_iff_height_add {R : Type*} [CommRing R] :
    IsCatenary R ↔ (∀ p q : PrimeSpectrum R, p ≤ q →
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height ≠ ⊤) ∧
      ∀ p q r : PrimeSpectrum R, p ≤ q → q ≤ r →
        (r.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height =
          (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height +
            (r.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).height := by
  rw [IsCatenary, Order.isCatenary_iff_krullDim_Icc_add]
  refine and_congr (forall₃_congr fun p q hpq => ?_)
    (forall_congr' fun p => forall₄_congr fun q r hpq hqr => ?_)
  · rw [PrimeSpectrum.krullDim_Icc hpq, ← WithBot.coe_top, Ne, Ne, WithBot.coe_inj]
  · rw [PrimeSpectrum.krullDim_Icc (hpq.trans hqr), PrimeSpectrum.krullDim_Icc hpq,
      PrimeSpectrum.krullDim_Icc hqr, ← WithBot.coe_add, WithBot.coe_inj]

/-- A Noetherian ring is catenary if and only if, for all primes `p ⊆ q ⊆ r`, the heights of the
quotient primes are additive: `ht (r / p) = ht (q / p) + ht (r / q)`. The finiteness required by
`isCatenary_iff_height_add` is automatic, prime ideals of a Noetherian ring having finite height.
Stacks, Lemma 10.105.2 (02IH) and Topology, Lemma 5.11.6 (02I6). -/
theorem isCatenary_iff_height_add_of_isNoetherianRing {R : Type*} [CommRing R]
    [IsNoetherianRing R] :
    IsCatenary R ↔ ∀ p q r : PrimeSpectrum R, p ≤ q → q ≤ r →
      (r.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height =
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height +
          (r.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).height := by
  rw [isCatenary_iff_height_add, and_iff_right_iff_imp]
  intro _ p q hpq
  have : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  exact Ideal.height_ne_top_of_isPrime

example : IsCatenary ℤ := inferInstance

example (K : Type*) [Field K] : IsCatenary K := inferInstance

end TauCeti.Excellence
