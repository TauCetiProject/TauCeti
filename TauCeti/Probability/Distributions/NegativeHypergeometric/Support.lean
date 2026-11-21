/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.NegativeHypergeometric.Basic

/-!
# Topological support of the negative hypergeometric distribution

For valid parameters and a positive number `r` of awaited successes, every failure count from
`0` through `N - K` has positive mass. Thus the native negative hypergeometric law has support
`Set.Icc 0 (N - K)`. When `r = 0` its support is the singleton zero, while invalid parameters
give the empty support because the totalized measure is zero.

The real-cast law has the corresponding finite set of nonnegative integer points as its support.
These support formulas distinguish the finite native carrier from the whole real interval between
its endpoints.

## Main results

* `TauCeti.Probability.support_negativeHypergeometricMeasure` gives the exact totalized native
  support.
* `TauCeti.Probability.support_map_cast_negativeHypergeometricMeasure` gives the support after
  casting the count to `ℝ`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- At valid parameters with a positive awaited-success count, the native negative
hypergeometric law has support exactly `0, …, N - K`. -/
theorem support_negativeHypergeometricMeasure_of_pos {N K r : ℕ} (hr : r ≤ K)
    (hK : K ≤ N) (hr0 : 0 < r) :
    (negativeHypergeometricMeasure N K r).support = Icc 0 (N - K) := by
  ext k
  rw [Measure.mem_support_iff_forall]
  constructor
  · intro hk
    have hmass : negativeHypergeometricMeasure N K r {k} ≠ 0 :=
      (hk {k} (by simp)).ne'
    exact mem_Icc.mpr ⟨Nat.zero_le k,
      ((negativeHypergeometricMeasure_singleton_ne_zero_iff hr hK k).mp hmass).1⟩
  · intro hk U hU
    have hmass : 0 < negativeHypergeometricMeasure N K r {k} :=
      pos_iff_ne_zero.mpr <|
        (negativeHypergeometricMeasure_singleton_ne_zero_iff hr hK k).mpr
          ⟨hk.2, Or.inr hr0⟩
    exact hmass.trans_le <| measure_mono <|
      singleton_subset_iff.mpr (mem_of_mem_nhds hU)

/-- The exact native support of every totalized negative hypergeometric law. Valid parameters
with `r = 0` give the singleton zero, valid parameters with `r > 0` give every count through
`N - K`, and invalid parameters give the empty set. -/
@[simp]
theorem support_negativeHypergeometricMeasure (N K r : ℕ) :
    (negativeHypergeometricMeasure N K r).support =
      if r ≤ K ∧ K ≤ N then if r = 0 then {0} else Icc 0 (N - K) else ∅ := by
  by_cases hvalid : r ≤ K ∧ K ≤ N
  · rw [ite_eq_left hvalid]
    by_cases hr0 : r = 0
    · subst r
      rw [ite_eq_left rfl, negativeHypergeometricMeasure_zero_successes hvalid.2,
        Measure.support_dirac, closure_singleton]
    · rw [ite_eq_right hr0, support_negativeHypergeometricMeasure_of_pos hvalid.1 hvalid.2
        (Nat.pos_of_ne_zero hr0)]
  · rw [ite_eq_right hvalid, negativeHypergeometricMeasure_eq_zero_of_invalid hvalid,
      Measure.support_zero]

/-- At valid parameters with a positive awaited-success count, the support of the real-cast law
is the finite set of casts of the possible native counts. -/
theorem support_map_cast_negativeHypergeometricMeasure_of_pos {N K r : ℕ} (hr : r ≤ K)
    (hK : K ≤ N) (hr0 : 0 < r) :
    ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)).support =
      (Nat.cast : ℕ → ℝ) '' Icc 0 (N - K) := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    support_negativeHypergeometricMeasure_of_pos hr hK hr0]
  exact (Set.toFinite (Nat.cast '' Icc 0 (N - K))).isClosed.closure_eq

/-- The exact support of the real-cast totalized negative hypergeometric law. Its positive-wait
valid cases have one support point for each possible native failure count. -/
@[simp]
theorem support_map_cast_negativeHypergeometricMeasure (N K r : ℕ) :
    ((negativeHypergeometricMeasure N K r).map (Nat.cast : ℕ → ℝ)).support =
      if r ≤ K ∧ K ≤ N then
        if r = 0 then {0} else (Nat.cast : ℕ → ℝ) '' Icc 0 (N - K)
      else ∅ := by
  by_cases hvalid : r ≤ K ∧ K ≤ N
  · rw [ite_eq_left hvalid]
    by_cases hr0 : r = 0
    · subst r
      rw [ite_eq_left rfl, negativeHypergeometricMeasure_zero_successes hvalid.2,
        Measure.map_dirac' (by fun_prop), Measure.support_dirac, closure_singleton]
      norm_num
    · rw [ite_eq_right hr0,
        support_map_cast_negativeHypergeometricMeasure_of_pos hvalid.1 hvalid.2
        (Nat.pos_of_ne_zero hr0)]
  · rw [ite_eq_right hvalid, negativeHypergeometricMeasure_eq_zero_of_invalid hvalid,
      Measure.map_zero, Measure.support_zero]

end TauCeti.Probability
