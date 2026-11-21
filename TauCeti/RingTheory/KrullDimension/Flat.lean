/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Heights near the image of a flat map

Let `B` be a flat, finitely presented algebra of Krull dimension at most `n` over a Noetherian ring
`A`. Flat maps satisfy going down, so by Chevalley's theorem the image of
`Spec B → Spec A` is open, and over it heights do not drop:
`ht p ≤ ht P` for a prime `P` of `B` over `p`. Hence every prime of `A` under a prime of `B` has a
basic open neighbourhood on which all heights are at most `n`
(`TauCeti.exists_notMem_forall_height_le_of_flat`).
-/

public section

namespace TauCeti

/-- Let `A` be Noetherian. Near a prime of `A` under a prime `Q` of a flat, finitely presented
`A`-algebra `B` of Krull dimension at most `n`, every prime of `A` has height at most `n`: the
image of `Spec B → Spec A` is an open neighbourhood of `Q ∩ A`, and flat maps do not lower
heights. -/
theorem exists_notMem_forall_height_le_of_flat {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] [Algebra.FinitePresentation A B] [IsNoetherianRing A] {n : ℕ}
    (hdim : ringKrullDim B ≤ n) (Q : Ideal B) [Q.IsPrime] :
    ∃ a ∉ Q.comap (algebraMap A B), ∀ p : Ideal A, p.IsPrime → a ∉ p → Ideal.height p ≤ n := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hopen := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    (R := A) (S := B) _ isOpen_univ
  rw [Set.image_univ] at hopen
  obtain ⟨_, ⟨a, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_range_self ⟨Q, inferInstance⟩) hopen
  refine ⟨a, ha, fun p hp hap ↦ ?_⟩
  obtain ⟨P, hP⟩ := hle ((PrimeSpectrum.mem_basicOpen a ⟨p, hp⟩).mpr hap)
  have : P.asIdeal.LiesOver p := ⟨congrArg PrimeSpectrum.asIdeal hP.symm⟩
  have hPp := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P.asIdeal
  have hPn : (P.asIdeal.height : WithBot ℕ∞) ≤ n :=
    Ideal.height_le_ringKrullDim_of_isPrime.trans hdim
  exact (le_self_add.trans_eq hPp.symm).trans (WithBot.coe_le_coe.mp hPn)

end TauCeti
