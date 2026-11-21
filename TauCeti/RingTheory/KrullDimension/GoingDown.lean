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

Let `B` be a finitely presented algebra of Krull dimension at most `n` over `A` satisfying going
down, for instance a flat one. By Chevalley's theorem the image of `Spec B → Spec A` is open, and
over it heights do not drop: going down lifts every chain of primes of `A` ending at `p` to a
chain of the same length ending at a prime `P` of `B` over `p`, so `ht p ≤ ht P`. Hence every
prime of `A` under a prime of `B` has a basic open neighbourhood on which all heights are at most
`n` (`TauCeti.exists_notMem_forall_height_le_of_hasGoingDown_of_ringKrullDim_le`).
-/

public section

namespace TauCeti

/-- Near a prime of `A` under a prime `Q` of a finitely presented `A`-algebra `B` which satisfies
going down and has Krull dimension at most `n`, every prime of `A` has height at most `n`: the
image of `Spec B → Spec A` is an open neighbourhood of `Q ∩ A`, and going down does not lower
heights. -/
theorem exists_notMem_forall_height_le_of_hasGoingDown_of_ringKrullDim_le {A B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.HasGoingDown A B]
    [Algebra.FinitePresentation A B] {n : ℕ} (hdim : ringKrullDim B ≤ n) (Q : Ideal B)
    [Q.IsPrime] :
    ∃ a ∉ Q.comap (algebraMap A B), ∀ p : Ideal A, p.IsPrime → a ∉ p → Ideal.height p ≤ n := by
  have hopen := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    (R := A) (S := B) _ isOpen_univ
  rw [Set.image_univ] at hopen
  obtain ⟨_, ⟨a, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_range_self ⟨Q, inferInstance⟩) hopen
  refine ⟨a, ha, fun p hp hap ↦ ?_⟩
  obtain ⟨P, hP⟩ := hle ((PrimeSpectrum.mem_basicOpen a ⟨p, hp⟩).mpr hap)
  have hPn : P.asIdeal.height ≤ n :=
    WithBot.coe_le_coe.mp (Ideal.height_le_ringKrullDim_of_isPrime.trans hdim)
  rw [show p = (⟨p, hp⟩ : PrimeSpectrum A).asIdeal from rfl, PrimeSpectrum.height_eq_orderHeight]
  -- Going down lifts a chain of primes ending at `p` to a chain of the same length ending at `P`.
  refine Order.height_le fun l hl ↦ ?_
  have : P.asIdeal.LiesOver l.last.asIdeal := ⟨by rw [hl, ← hP]; rfl⟩
  obtain ⟨L, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P.asIdeal
  rw [← hlen]
  refine Order.length_le_height_last.trans ?_
  rw [hlast, ← PrimeSpectrum.height_eq_orderHeight]
  exact hPn

end TauCeti
