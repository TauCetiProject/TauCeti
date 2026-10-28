/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Topology.Algebra.Polynomial.RootLocus
import TauCeti.NumberTheory.LocalField.IntegerRing.Basic
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology
import TauCeti.Topology.Algebra.ValuativeRel.AdicTopology
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Measurable coefficient loci for roots in valuation balls

For an extension `L / K` of nonarchimedean local fields, the coefficient vectors of monic
polynomials with a root in a fixed closed ball of `𝒪[L]` form a closed set. These sets are
therefore measurable, including at inseparable polynomials. Their indicators are the summands
in the finite ball decomposition of root counts used in Serre's mass-formula integral.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3.
-/

public section

open ValuativeRel IsDiscreteValuationRing Polynomial

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- The monic coefficient vectors with a root in a fixed closed valuation ball of the ring of
integers of an extension of local fields form a closed set. -/
theorem isClosed_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal
    (n r : ℕ) (c : 𝒪[L]) :
    IsClosed {a : Fin n → K | ∃ z : 𝒪[L],
      aeval (z : L) (TauCeti.Polynomial.monicOfCoeff a) = 0 ∧
        (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)} := by
  have := finite_of_valuativeExtension K L
  have hb : IsCompact {z : 𝒪[L] | (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)} := by
    simp only [← IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]
    exact (((isAdic_maximalIdeal L).isClosed_pow r).preimage
      (continuous_id.sub continuous_const)).isCompact
  convert TauCeti.Polynomial.isClosed_setOf_exists_aeval_monicOfCoeff_eq_zero
    (continuous_algebraMap_of_valuativeExtension K L) (hb.image continuous_subtype_val) n using 1
  ext a
  simp [and_comm]

/-- The coefficient locus for a root in a fixed closed valuation ball is measurable for any
measurable structure containing the open subsets of coefficient space. -/
theorem measurableSet_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal
    {n : ℕ} [MeasurableSpace (Fin n → K)] [OpensMeasurableSpace (Fin n → K)]
    (r : ℕ) (c : 𝒪[L]) :
    MeasurableSet {a : Fin n → K | ∃ z : 𝒪[L],
      aeval (z : L) (TauCeti.Polynomial.monicOfCoeff a) = 0 ∧
        (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)} :=
  (isClosed_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal n r c).measurableSet

end TauCeti
