/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Heights near the image of a going-down map

Going down does not lower heights: it lifts every chain of primes of `A` ending at `P ∩ A` to a
chain of the same length ending at a prime `P` of `B`, so `ht (P ∩ A) ≤ ht P`, and the same holds
for every ideal `P` by passing to its minimal primes
(`Ideal.height_under_le_height_of_hasGoingDown`). Now let `B` be a finitely presented
`A`-algebra satisfying going down, for instance a flat one. Chevalley's theorem makes the image of
`Spec B → Spec A` constructible, and going down makes it stable under generalization, so it is
open. Hence every prime of `A` under a prime of `B` has a basic open neighbourhood on which all
heights are at most `dim B`
(`TauCeti.exists_notMem_forall_height_le_ringKrullDim_of_hasGoingDown`).
-/

public section

namespace TauCeti

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Going down does not lower heights: every ideal `P` of `B` has height at least that of
`P ∩ A`. -/
theorem _root_.Ideal.height_under_le_height_of_hasGoingDown [Algebra.HasGoingDown A B]
    (P : Ideal B) : (P.under A).height ≤ P.height := by
  -- It suffices to treat the minimal primes `Q` of `P`, which lie over primes containing `P ∩ A`.
  rw [P.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun Q hQ ↦ ?_
  have := hQ.1.1
  have hPQ : P.under A ≤ Q.under A := by
    rw [Ideal.under_def, Ideal.under_def]
    exact Ideal.comap_mono hQ.1.2
  refine (Ideal.height_mono hPQ).trans ?_
  rw [PrimeSpectrum.height_eq_orderHeight (⟨Q.under A, inferInstance⟩ : PrimeSpectrum A),
    PrimeSpectrum.height_eq_orderHeight (⟨Q, ‹_›⟩ : PrimeSpectrum B)]
  -- Going down lifts a chain of primes ending at `Q ∩ A` to a chain of the same length ending
  -- at `Q`.
  refine Order.height_le fun l hl ↦ ?_
  have : Q.LiesOver l.last.asIdeal := ⟨by rw [hl]⟩
  obtain ⟨L, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q
  rw [← hlen, ← hlast]
  exact Order.length_le_height_last

/-- Near a prime of `A` under a prime `Q` of a finitely presented `A`-algebra `B` which satisfies
going down, every prime of `A` has height at most `dim B`: the image of `Spec B → Spec A` is an
open neighbourhood of `Q ∩ A`, and going down does not lower heights. -/
theorem exists_notMem_forall_height_le_ringKrullDim_of_hasGoingDown [Algebra.HasGoingDown A B]
    [Algebra.FinitePresentation A B] (Q : Ideal B) [Q.IsPrime] :
    ∃ a ∉ Q.comap (algebraMap A B), ∀ p : Ideal A, p.IsPrime → a ∉ p →
      (Ideal.height p : WithBot ℕ∞) ≤ ringKrullDim B := by
  have hopen := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    (R := A) (S := B) _ isOpen_univ
  rw [Set.image_univ] at hopen
  obtain ⟨_, ⟨a, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_range_self ⟨Q, inferInstance⟩) hopen
  refine ⟨a, ha, fun p hp hap ↦ ?_⟩
  obtain ⟨P, hP⟩ := hle ((PrimeSpectrum.mem_basicOpen a ⟨p, hp⟩).mpr hap)
  have hPp : P.asIdeal.under A = p := by
    rw [Ideal.under_def, ← PrimeSpectrum.comap_asIdeal, hP]
  rw [← hPp]
  exact (WithBot.coe_le_coe.mpr (Ideal.height_under_le_height_of_hasGoingDown P.asIdeal)).trans
    Ideal.height_le_ringKrullDim_of_isPrime

end TauCeti
