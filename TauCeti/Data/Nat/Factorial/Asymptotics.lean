/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Falling factorials of proportional sequences

A fixed shift of a natural count and each of the fixed offsets in its falling factorial have
vanishing effect after scaling by a denominator tending to infinity. This also applies when
the ratio tends to zero and the numerator itself may stay bounded.
-/

public section

open Filter
open scoped Topology

/-- If `p i / d i → y` and `d i → ∞`, the order-`k` falling factorial of `p i - r`, divided
by `(d i)^k`, tends to `y^k` for each fixed shift `r` and order `k`. -/
theorem Filter.Tendsto.natCast_descFactorial_sub_div_pow {ι 𝕜 : Type*} {l : Filter ι}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    {p : ι → ℕ} {d : ι → 𝕜} {y : 𝕜} (hd : Tendsto d l atTop)
    (hy : Tendsto (fun i ↦ (p i : 𝕜) / d i) l (𝓝 y)) (r k : ℕ) :
    Tendsto (fun i ↦ ((p i - r).descFactorial k : 𝕜) / d i ^ k) l (𝓝 (y ^ k)) := by
  have hoffset (s : ℕ) : Tendsto (fun i ↦ ((p i - s : ℕ) : 𝕜) / d i) l (𝓝 y) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun i ↦ (p i : 𝕜) / d i - (s : 𝕜) / d i) ?_ hy ?_ ?_
    · simpa only [sub_zero] using hy.sub (hd.const_div_atTop (s : 𝕜))
    · filter_upwards [hd.eventually_ge_atTop 0] with i hi
      rw [← sub_div]
      apply div_le_div_of_nonneg_right _ hi
      by_cases hs : s ≤ p i
      · rw [Nat.cast_sub hs]
      · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, sub_nonpos]
        exact_mod_cast (by omega : p i ≤ s)
    · filter_upwards [hd.eventually_ge_atTop 0] with i hi
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ _)) hi
  have hprod := tendsto_finsetProd (Finset.range k) fun j _ ↦ hoffset (r + j)
  rw [Finset.prod_const, Finset.card_range] at hprod
  refine hprod.congr fun i ↦ ?_
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  simp only [Nat.sub_sub]
