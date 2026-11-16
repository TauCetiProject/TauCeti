/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Lebesgue.Support
public import TauCeti.Probability.Renewal.Lattice.Blackwell
public import TauCeti.Analysis.SpecificLimits.LatticeIncrements

/-!
# Vanishing renewal increments for infinite-mean lattice laws

For an infinite-mean lattice interarrival law, the expected number of arrivals in any
fixed bounded window tends to zero. Observation times need not lie on the lattice.
The greatest span exists for every nondegenerate lattice law; the lattice Blackwell
theorem gives vanishing increments on that grid, and monotonicity controls windows
between grid points. This is the local estimate needed for escape of the excess life.
Zero increments are allowed.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

/-- For a lattice law of infinite extended mean, every fixed-window renewal-function
increment tends to zero, at arbitrary nonnegative observation times. The law may have
an atom at zero. No particular lattice span is specified. -/
theorem IsLattice.tendsto_renewalFunction_add_sub_of_mean_eq_top
    {F : Measure ℝ≥0} [IsProbabilityMeasure F] (hF : F.IsLattice)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ (F.renewalFunction (t + x)).toReal -
      (F.renewalFunction t).toReal) atTop (𝓝 0) := by
  have hzero := F.measure_singleton_lt_one_of_lintegral_pos (f := fun u ↦ (u : ℝ≥0∞))
    (a := 0) (by simp) (hmean ▸ ENNReal.zero_lt_top)
  obtain ⟨a, hmax⟩ := hF.exists_isGreatest_of_measure_zero_lt_one hzero
  have hgrid : Tendsto (fun n : ℕ ↦ (F.renewalFunction (a * (n + 1))).toReal -
      (F.renewalFunction (a * n)).toReal) atTop (𝓝 0) := by
    simpa only [hmean, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero,
      Nat.cast_add, Nat.cast_one, mul_comm] using
      hmax.1.tendsto_renewalFunction_succ_mul_sub hmax
  exact (F.monotone_toReal_renewalFunction hzero).tendsto_sub_add_of_tendsto_sub_lattice
    hmax.1.pos hgrid x

end MeasureTheory.Measure
