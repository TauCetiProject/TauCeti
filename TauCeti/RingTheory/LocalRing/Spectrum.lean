/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.RingTheory.Depth.Basic

/-!
# Density away from the closed point of a local spectrum

The complement of the closed point of the spectrum of a local ring is dense exactly when the
ring has positive Krull dimension. In particular it is dense for a Noetherian local ring of
positive depth. Neither reducedness nor irreducibility is needed.

This supplies the density hypothesis for restricting finite étale covers to the complement of
the closed point. The corresponding open inclusion is dominant by
`AlgebraicGeometry.Opens.isDominant_ι`.

## References

* The Stacks Project, Section 58.20 (0BM7), finite étale covers of punctured spectra.
-/

public section

open IsLocalRing

namespace TauCeti.IsLocalRing

variable {R : Type*}

/-- The complement of the closed point of a local spectrum is dense exactly when the ring has
positive Krull dimension. This holds even for commutative semirings, without Noetherianity or
reducedness. -/
theorem dense_compl_closedPoint_iff [CommSemiring R] [IsLocalRing R] :
    Dense ({closedPoint R}ᶜ : Set (PrimeSpectrum R)) ↔ 0 < ringKrullDim R := by
  rw [dense_compl_singleton_iff_not_open, ← not_le]
  apply not_congr
  constructor
  · intro h
    have htop : (⟨{closedPoint R}, h⟩ : TopologicalSpace.Opens (PrimeSpectrum R)) = ⊤ :=
      (closedPoint_mem_iff _).mp (Set.mem_singleton _)
    apply (Ring.krullDimLE_iff (n := 0)).mp
    rw [Ring.krullDimLE_zero_iff]
    intro p hp
    have heq : (⟨p, hp⟩ : PrimeSpectrum R) = closedPoint R := by
      apply Set.mem_singleton_iff.mp
      have hmem : (⟨p, hp⟩ : PrimeSpectrum R) ∈
          (⟨{closedPoint R}, h⟩ : TopologicalSpace.Opens (PrimeSpectrum R)) := by
        rw [htop]
        trivial
      exact hmem
    have hp_eq : p = maximalIdeal R := congrArg PrimeSpectrum.asIdeal heq
    rw [hp_eq]
    exact maximalIdeal.isMaximal R
  · intro hdim
    have hdim' : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr hdim
    have hsingleton : ({closedPoint R} : Set (PrimeSpectrum R)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro p
      apply Set.mem_singleton_iff.mpr
      apply PrimeSpectrum.ext
      exact eq_maximalIdeal (Ring.krullDimLE_zero_iff.mp hdim' p.asIdeal p.isPrime)
    rw [hsingleton]
    exact isOpen_univ

/-- Positive depth makes the complement of the closed point dense, including for nonreduced
Noetherian local rings. -/
theorem dense_compl_closedPoint_of_one_le_depth [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdepth : 1 ≤ depth (ModuleCat.of R R)) :
    Dense ({closedPoint R}ᶜ : Set (PrimeSpectrum R)) := by
  apply dense_compl_closedPoint_iff.mpr
  have hle : (depth (ModuleCat.of R R) : WithBot ℕ∞) ≤ ringKrullDim R := by
    simpa only [Module.supportDim_self_eq_ringKrullDim] using
      (depth_le_supportDim (R := R) (M := R))
  have hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R :=
    le_trans (by exact_mod_cast hdepth) hle
  exact lt_of_lt_of_le (by norm_num) hdim

end TauCeti.IsLocalRing
