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

For `f` with summable norms, the infinite product `∏' i, (1 + f i)` in a seminormed commutative ring
has norm at most `exp (∑' i, ‖f i‖)`. Each finite partial product is bounded by
`∏ (1 + ‖f i‖) ≤ exp (∑ ‖f i‖)`, and the bound passes to the limit. This is the estimate used to
bound theta products and Siegel functions on the upper half-plane by elementary functions of
`|q|`. More generally, `HasProd.norm_le_exp_of_sum_le` bounds any supplied product from real
exponential bounds on its factors and a common bound on all finite sums of the exponents.
`TauCeti.norm_tprod_le_exp_of_sum_le` gives the corresponding totalized product bound.
The same argument, from Mathlib's `Finset.norm_prod_one_add_sub_one_le`, bounds the distance
`‖∏' i, (1 + f i) - 1‖` by `exp (∑' i, ‖f i‖) - 1`, which controls such a product near the identity.

Building on Mathlib's `tprod_one_add_ne_zero_of_summable` and `multipliable_one_add_of_summable`
(`Mathlib.Analysis.SpecialFunctions.Log.Summable`), we also record the pointwise vanishing
characterization `TauCeti.tprod_one_add_eq_zero_iff_of_summable`, finiteness of vanishing factors
`TauCeti.finite_one_add_eq_zero_of_summable`, finite-set factor extraction
`TauCeti.tprod_one_add_eq_prod_mul_tprod_compl`, and nonvanishing of the complementary tail
`TauCeti.tprod_one_add_compl_ne_zero_of_summable`.
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
  exact (Finset.le_prod_of_submultiplicative_of_nonneg (norm : R → ℝ) norm_nonneg
    norm_one.le norm_mul_le s f).trans <|
    (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hb i).trans <|
      (Real.exp_sum s b).symm.trans_le (Real.exp_le_exp.mpr (hB s))

namespace TauCeti

section SeminormedCommRing

variable {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]

/-- The totalized infinite product has norm at most `exp B` if each factor has norm at most
`exp (b i)` and every finite sum of the real exponents is at most `B`. -/
theorem norm_tprod_le_exp_of_sum_le {f : ι → R} {b : ι → ℝ} {B : ℝ}
    (hb : ∀ i, ‖f i‖ ≤ Real.exp (b i))
    (hB : ∀ s : Finset ι, ∑ i ∈ s, b i ≤ B) : ‖∏' i, f i‖ ≤ Real.exp B := by
  by_cases h : Multipliable f
  · exact h.hasProd.norm_le_exp_of_sum_le hb hB
  · rw [tprod_eq_one_of_not_multipliable h, norm_one]
    exact Real.one_le_exp (by simpa using hB ∅)

/-- In a seminormed commutative ring, `‖∏' i, (1 + f i)‖ ≤ exp (∑' i, ‖f i‖)` whenever
`‖f i‖` is summable. -/
theorem norm_tprod_one_add_le_exp_tsum {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i)‖ ≤ Real.exp (∑' i, ‖f i‖) := by
  refine norm_tprod_le_exp_of_sum_le (b := fun i ↦ ‖f i‖) ?_ ?_
  · intro i
    calc
      ‖1 + f i‖ ≤ 1 + ‖f i‖ := (norm_add_le _ _).trans_eq (by rw [norm_one])
      _ ≤ Real.exp ‖f i‖ := by simpa only [add_comm] using Real.add_one_le_exp ‖f i‖
  · exact fun s ↦ hf.sum_le_tsum s fun _ _ ↦ norm_nonneg _

end SeminormedCommRing

variable {ι R : Type*} [NormedCommRing R] [NormOneClass R]

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

/-- Under absolute summability of `f`, the product `∏' i, (1 + f i)` in a complete normed
commutative ring with multiplicative norm vanishes if and only if one of its factors vanishes. -/
theorem tprod_one_add_eq_zero_iff_of_summable [NormMulClass R] [CompleteSpace R] {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) :
    (∏' i, (1 + f i)) = 0 ↔ ∃ i, 1 + f i = 0 := by
  refine ⟨fun h ↦ ?_, tprod_of_exists_eq_zero⟩
  by_contra! hne
  exact tprod_one_add_ne_zero_of_summable hne hf h

/-- Under summability of `‖f i‖` in a normed commutative ring with `‖(1 : R)‖ = 1`, only finitely
many factors `1 + f i` can vanish. -/
theorem finite_one_add_eq_zero_of_summable {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) :
    {i | 1 + f i = 0}.Finite := by
  have hev : ∀ᶠ i in Filter.cofinite, 1 + f i ≠ 0 := by
    filter_upwards [hf.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)] with i hi hzero
    have hnorm : ‖f i‖ = 1 := by
      rw [← norm_neg, ← eq_neg_of_add_eq_zero_left hzero, norm_one]
    exact lt_irrefl (1 : ℝ) (hnorm ▸ hi)
  simpa only [Filter.eventually_cofinite, not_not] using hev

/-- Under summability of `‖f i‖` in a complete normed commutative ring, any finite set `s` of
factors splits off from `∏' i, (1 + f i)` leaving the complementary subtype product. -/
theorem tprod_one_add_eq_prod_mul_tprod_compl [CompleteSpace R] {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) (s : Finset ι) :
    (∏' i, (1 + f i)) = (∏ i ∈ s, (1 + f i)) * ∏' i : {i // i ∉ s}, (1 + f i) := by
  have htail : Multipliable fun i : {i // i ∉ s} ↦ 1 + f i :=
    multipliable_one_add_of_summable (hf.subtype _)
  have hsplit := Multipliable.tprod_mul_tprod_compl (s := (s : Set ι)) (f := fun i ↦ 1 + f i)
    Multipliable.of_finite htail
  rw [s.tprod_subtype' (fun i ↦ 1 + f i)] at hsplit
  exact hsplit.symm

/-- Under absolute summability of `f`, extracting a finite set `s` containing all vanishing factors
leaves a nonzero complementary product. -/
theorem tprod_one_add_compl_ne_zero_of_summable [NormMulClass R] [CompleteSpace R] {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) {s : Finset ι} (hs : ∀ i, 1 + f i = 0 → i ∈ s) :
    (∏' i : {i // i ∉ s}, (1 + f i)) ≠ 0 :=
  tprod_one_add_ne_zero_of_summable (fun i hi ↦ i.property (hs i hi)) (hf.subtype _)

end TauCeti
