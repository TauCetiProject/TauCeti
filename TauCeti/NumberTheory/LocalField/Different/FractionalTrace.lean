/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Basic
public import TauCeti.NumberTheory.LocalField.RealAddValuation
public import TauCeti.RingTheory.DedekindDomain.Different.FractionalTrace

/-!
# Valuation bounds for field traces

For a finite separable extension of nonarchimedean local fields, the different determines
exactly which base-field elements admit a trace preimage of a given minimum valuation.
Comparing the two valuations on the extension field gives a lower bound for the valuation
of a trace with a rounding loss of at most `e - 1` uniformizer steps.

Reference: Serre, *Local Fields*, Chapter III, §3, Proposition 7.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- An element of `K` has a trace preimage of valuation at least `m` exactly when its valuation
is at least `⌊(m + d) / e⌋`. Each valuation assigns one to a uniformizer of its own field. -/
theorem exists_trace_eq_iff_le_realAddValuation [Algebra.IsSeparable K L] (m : ℤ) (y : K) :
    (∃ x : L, ((m : ℝ) : WithTop ℝ) ≤ realAddValuation L x ∧ Algebra.trace K L x = y) ↔
      ((((m + differentExponent K L) / ramificationIndex K L : ℤ) : ℝ) : WithTop ℝ) ≤
        realAddValuation K y := by
  simp only [← mem_maximalIdeal_zpow_iff_le_realAddValuation, differentExponent_def,
    ramificationIndex_eq_ramificationIdx]
  rw [← FractionalIdeal.mem_trace (A := 𝒪[K]), trace_maximalIdeal_zpow]

/-- Measured in the extension field, the valuation of a trace gains at least the different
exponent minus `e - 1`. This includes zero inputs and zero traces, with valuation `⊤`. -/
theorem realAddValuation_add_differentExponent_le_realAddValuation_trace_add (x : L) :
    realAddValuation L x + differentExponent K L ≤
      realAddValuation L (algebraMap K L (Algebra.trace K L x)) +
        (ramificationIndex K L - 1 : ℕ) := by
  rcases eq_or_ne (Algebra.trace K L x) 0 with ht | ht
  · simp [ht]
  have : Algebra.IsSeparable K L := by
    by_contra h
    exact ht (by simp [Algebra.trace_eq_zero_of_not_isSeparable h])
  have hx : x ≠ 0 := fun h ↦ ht (h ▸ map_zero _)
  obtain ⟨m, hm⟩ := exists_int_realAddValuation hx
  obtain ⟨n, hn⟩ := exists_int_realAddValuation ht
  have h := (exists_trace_eq_iff_le_realAddValuation (K := K) (L := L) m _).mp ⟨x, hm.ge, rfl⟩
  rw [hn, WithTop.coe_le_coe] at h
  have he : (0 : ℤ) < ramificationIndex K L := by exact_mod_cast ramificationIndex_pos
  have hdiv : (m + differentExponent K L) / ramificationIndex K L ≤ n := by exact_mod_cast h
  have hlt := (Int.ediv_lt_iff_lt_mul he).mp (Int.lt_add_one_iff.mpr hdiv)
  rw [hm, realAddValuation_algebraMap, hn, WithTop.map_coe]
  norm_cast
  rw [Nat.cast_sub (by omega : 1 ≤ ramificationIndex K L)]
  push_cast
  linarith

end TauCeti
