/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Exponential bounds for infinite products in normed rings

For `f` with summable norms, the infinite product `∏' i, (1 + f i)` in a normed commutative ring
has norm at most `exp (∑' i, ‖f i‖)`. Each finite partial product is bounded by
`∏ (1 + ‖f i‖) ≤ exp (∑ ‖f i‖)`, and the bound passes to the limit. This is the estimate used to
bound theta products and Siegel functions on the upper half-plane by elementary functions of
`|q|`. More generally, `HasProd.norm_le_exp_of_sum_le` bounds any supplied product from real
exponential bounds on its factors and a common bound on all finite sums of the exponents.
The same argument, from Mathlib's `Finset.norm_prod_one_add_sub_one_le`, bounds the distance
`‖∏' i, (1 + f i) - 1‖` by `exp (∑' i, ‖f i‖) - 1`, which controls such a product near the identity.
-/

public section

open scoped BigOperators

/-- A supplied infinite product has norm at most `exp B` if each factor has norm at most
`exp (b i)` and every finite sum of the real exponents is at most `B`. -/
theorem HasProd.norm_le_exp_of_sum_le {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    {f : ι → R} {a : R} (hf : HasProd f a) {b : ι → ℝ} {B : ℝ}
    (hb : ∀ i, ‖f i‖ ≤ Real.exp (b i))
    (hB : ∀ s : Finset ι, ∑ i ∈ s, b i ≤ B) : ‖a‖ ≤ Real.exp B := by
  refine le_of_tendsto' (Filter.Tendsto.norm hf) fun s ↦ ?_
  have hfinite : ‖∏ i ∈ s, f i‖ ≤ Real.exp (∑ i ∈ s, b i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, Real.exp_add]
      exact (norm_mul_le _ _).trans
        (mul_le_mul (hb i) ih (norm_nonneg _) (Real.exp_pos _).le)
  exact hfinite.trans (Real.exp_le_exp.mpr (hB s))

namespace TauCeti

variable {ι R : Type*} [NormedCommRing R] [NormOneClass R]

/-- In a normed commutative ring, `‖∏' i, (1 + f i)‖ ≤ exp (∑' i, ‖f i‖)` whenever the norms
`‖f i‖` are summable. -/
theorem norm_tprod_one_add_le_exp_tsum {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i)‖ ≤ Real.exp (∑' i, ‖f i‖) := by
  by_cases h : Multipliable fun i ↦ 1 + f i
  · refine h.hasProd.norm_le_exp_of_sum_le (b := fun i ↦ ‖f i‖) ?_ ?_
    · intro i
      calc
        ‖1 + f i‖ ≤ 1 + ‖f i‖ := (norm_add_le _ _).trans_eq (by rw [norm_one])
        _ ≤ Real.exp ‖f i‖ := by simpa only [add_comm] using Real.add_one_le_exp ‖f i‖
    · exact fun s ↦ hf.sum_le_tsum s fun _ _ ↦ norm_nonneg _
  · rw [tprod_eq_one_of_not_multipliable h, norm_one]
    exact Real.one_le_exp (tsum_nonneg fun _ ↦ norm_nonneg _)

/-- In a normed commutative ring, `‖∏' i, (1 + f i) - 1‖ ≤ exp (∑' i, ‖f i‖) - 1` whenever the
norms `‖f i‖` are summable. -/
theorem norm_tprod_one_add_sub_one_le {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i) - 1‖ ≤ Real.exp (∑' i, ‖f i‖) - 1 := by
  by_cases h : Multipliable fun i ↦ 1 + f i
  · refine le_of_tendsto' ((h.hasProd.sub_const 1).norm) fun s ↦ ?_
    exact (s.norm_prod_one_add_sub_one_le f).trans <| sub_le_sub_right
      (Real.exp_le_exp.2 (hf.sum_le_tsum s fun _ _ ↦ norm_nonneg _)) 1
  · rw [tprod_eq_one_of_not_multipliable h, sub_self, norm_zero, sub_nonneg]
    exact Real.one_le_exp (tsum_nonneg fun _ ↦ norm_nonneg _)

end TauCeti
