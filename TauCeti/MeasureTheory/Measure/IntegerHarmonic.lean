/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecificLimits.HarmonicSequence
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite harmonic measures on the integers

A finite measure on `ℤ` cannot be the average of its translates by `1` and `-1`
unless it is zero. Indeed, its singleton masses satisfy the discrete midpoint
identity, while their restrictions to every rightward ray tend to zero by
summability. This is the obstruction to an invariant probability for symmetric
nearest-neighbor random walk on the integers.

See J. R. Norris, *Markov Chains* (1997), §1.6, for the symmetric-walk example.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory.Measure

/-- The only finite measure on `ℤ` equal to the average of its two unit translates is zero.
Finiteness is essential: counting measure satisfies the same balance identity. -/
theorem eq_zero_of_eq_average_int_translates (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : μ = (2 : ℝ≥0∞)⁻¹ • μ.map (fun z => z + 1) +
      (2 : ℝ≥0∞)⁻¹ • μ.map (fun z => z - 1)) : μ = 0 := by
  have hmass (z : ℤ) :
      μ.real {z - 1} + μ.real {z + 1} = μ.real {z} + μ.real {z} := by
    have hp : (fun x : ℤ => x + 1) ⁻¹' {z} = {z - 1} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      omega
    have hm : (fun x : ℤ => x - 1) ⁻¹' {z} = {z + 1} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      omega
    have h := congrArg (fun ν : Measure ℤ => ν.real {z}) hμ
    rw [measureReal_add_apply
      (by simp [ENNReal.mul_eq_top]) (by simp [ENNReal.mul_eq_top])] at h
    simp only [measureReal_ennreal_smul_apply,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton _), hp, hm] at h
    linarith
  apply ext_of_measureReal_singleton
  intro z
  have hs : Summable (fun n : ℕ => μ.real {z + (n : ℤ)}) :=
    summable_measure_toReal (fun _ => measurableSet_singleton _) (by
      intro i j hij
      apply Set.disjoint_singleton.mpr
      omega)
  have hrec (n : ℕ) :
      μ.real {z + (n : ℤ)} + μ.real {z + ((n + 2 : ℕ) : ℤ)} =
        μ.real {z + ((n + 1 : ℕ) : ℤ)} + μ.real {z + ((n + 1 : ℕ) : ℤ)} := by
    have hp : z + ((n + 1 : ℕ) : ℤ) - 1 = z + (n : ℤ) := by omega
    have hm : z + ((n + 1 : ℕ) : ℤ) + 1 = z + ((n + 2 : ℕ) : ℤ) := by omega
    simpa only [hp, hm] using hmass (z + ((n + 1 : ℕ) : ℤ))
  simpa using hs.tendsto_atTop_zero.eq_zero_of_add_add_two hrec 0

end MeasureTheory.Measure
