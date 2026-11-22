/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import TauCeti.RingTheory.Ideal.GoingUp
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Finite
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Adic topologies on finite local algebras

For a module-finite algebra `R → S` of commutative local rings, some positive power of the maximal
ideal `𝔪_S` lies in `𝔪_R S` (`TauCeti.IsLocalRing.exists_maximalIdeal_pow_le_map`) while
`𝔪_R S ≤ 𝔪_S`, so the two filtrations by ideal powers are cofinal and induce the same adic
topology on `S` (`IsLocalRing.maximalIdeal_adicTopology_eq_map`), without any Noetherian hypothesis.

## Main results

* `IsLocalRing.maximalIdeal_adicTopology_eq_map`: for a finite local algebra `R → S`, the
  intrinsic maximal-ideal-adic topology coincides with the coefficient-induced adic topology.
-/

public section

/-- For a finite local algebra `R → S`, the intrinsic `𝔪_S`-adic topology coincides with the
`(𝔪_R S)`-adic topology induced from the coefficients. -/
theorem IsLocalRing.maximalIdeal_adicTopology_eq_map (R S : Type*)
    [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    (IsLocalRing.maximalIdeal S).adicTopology =
      ((IsLocalRing.maximalIdeal R).map (algebraMap R S)).adicTopology := by
  let := (IsLocalRing.maximalIdeal S).adicTopology
  obtain ⟨N, -, hN⟩ := TauCeti.IsLocalRing.exists_maximalIdeal_pow_le_map (R := R) (S := S)
  refine (IsAdic.isAdic_iff_isOpen_and_exists_pow_le (I := IsLocalRing.maximalIdeal S)
    (J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)) rfl).mpr ⟨?_, 1, ?_⟩
  · have : IsTopologicalRing S := (IsLocalRing.maximalIdeal S).nonarchimedean.toIsTopologicalRing
    exact Submodule.isOpen_mono hN (IsAdic.isOpen_pow (I := IsLocalRing.maximalIdeal S) rfl N)
  · rw [pow_one, Ideal.map_le_iff_le_comap]
    exact (Ideal.comap_eq_maximalIdeal_of_isIntegral (IsLocalRing.maximalIdeal S)).ge
