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
# Sharp and exponential bounds for finite and infinite products in normed rings

For any finite family `u` in a seminormed commutative ring `R`, without any assumption on `‖1‖` or
nonvanishing of factors, expanding `(1 + u a) * P - 1 = (P - 1) + u a * (P - 1) + u a` by induction
yields the sharp majorant
```text
‖∏ i ∈ s, (1 + u i) - 1‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) - 1
```
(`Finset.norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one`), together with the relative
partial-product bound
```text
‖∏ i ∈ s, (1 + u i) - ∏ i ∈ t, (1 + u i)‖ ≤ ‖∏ i ∈ t, (1 + u i)‖ * (∏ i ∈ s \ t, (1 + ‖u i‖) - 1)
```
for `t ⊆ s` (`Finset.norm_prod_one_add_sub_prod_one_add_le`). Passing to the limit when `‖f i‖` is
summable gives both the sharp infinite-product deviation bound
`‖∏' i, (1 + f i) - 1‖ ≤ (∏' i, (1 + ‖f i‖)) - 1` and the exponential bound
`‖∏' i, (1 + f i) - 1‖ ≤ exp (∑' i, ‖f i‖) - 1` in any seminormed commutative ring, as well as the
upper bound `‖∏' i, (1 + f i)‖ ≤ exp (∑' i, ‖f i‖)` when `‖1‖ = 1` and the zero criterion
`∏' i, (1 + f i) = 0 ↔ ∃ i, 1 + f i = 0` in a complete normed commutative ring with multiplicative
norm.

## References

* A. Rainer, *Advanced Complex Analysis*, Proposition 14.2 and Theorem 14.3, pp. 35–36.
-/

public section

namespace Finset

/-- **Sharp finite-product majorant.** For every finite family in a seminormed commutative ring,
`‖∏ i ∈ s, (1 + u i) - 1‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) - 1`, with no hypothesis on `‖1‖` and no
nonvanishing assumption on the factors. This refines `Finset.norm_prod_one_add_sub_one_le`, which
bounds the left-hand side by `exp (∑ i ∈ s, ‖u i‖) - 1` under `[NormOneClass R]`. -/
theorem norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one {ι R : Type*}
    [SeminormedCommRing R] (s : Finset ι) (u : ι → R) :
    ‖∏ i ∈ s, (1 + u i) - 1‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hsplit : (1 + u a) * (∏ i ∈ s, (1 + u i)) - 1 =
        (∏ i ∈ s, (1 + u i) - 1) + u a * (∏ i ∈ s, (1 + u i) - 1) + u a := by ring
    rw [hsplit]
    calc
      ‖(∏ i ∈ s, (1 + u i) - 1) + u a * (∏ i ∈ s, (1 + u i) - 1) + u a‖
        ≤ ‖∏ i ∈ s, (1 + u i) - 1‖ + ‖u a * (∏ i ∈ s, (1 + u i) - 1)‖ + ‖u a‖ :=
          norm_add₃_le
      _ ≤ ‖∏ i ∈ s, (1 + u i) - 1‖ + ‖u a‖ * ‖∏ i ∈ s, (1 + u i) - 1‖ + ‖u a‖ := by
          gcongr
          exact norm_mul_le _ _
      _ ≤ (∏ i ∈ s, (1 + ‖u i‖) - 1) + ‖u a‖ * (∏ i ∈ s, (1 + ‖u i‖) - 1) + ‖u a‖ := by
          gcongr
      _ = (1 + ‖u a‖) * (∏ i ∈ s, (1 + ‖u i‖)) - 1 := by ring

/-- **Relative finite-product estimate.** For nested finite sets `t ⊆ s` in a seminormed
commutative ring, the difference between the partial products on `s` and `t` is bounded by the
norm of the partial product on `t` times the sharp majorant on `s \ t`. -/
theorem norm_prod_one_add_sub_prod_one_add_le {ι R : Type*} [DecidableEq ι]
    [SeminormedCommRing R] {s t : Finset ι} (ht : t ⊆ s) (u : ι → R) :
    ‖∏ i ∈ s, (1 + u i) - ∏ i ∈ t, (1 + u i)‖ ≤
      ‖∏ i ∈ t, (1 + u i)‖ * (∏ i ∈ s \ t, (1 + ‖u i‖) - 1) := by
  have hfac : ∏ i ∈ s, (1 + u i) - ∏ i ∈ t, (1 + u i) =
      (∏ i ∈ t, (1 + u i)) * (∏ i ∈ s \ t, (1 + u i) - 1) := by
    conv_lhs => rw [← Finset.union_sdiff_of_subset ht, Finset.prod_union Finset.sdiff_disjoint.symm]
    rw [mul_sub_one]
  rw [hfac]
  exact (norm_mul_le _ _).trans <| mul_le_mul_of_nonneg_left
    ((s \ t).norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one u) (norm_nonneg _)

/-- Exponential form of `Finset.norm_prod_one_add_sub_prod_one_add_le` for nested finite sets
`t ⊆ s` in a seminormed commutative ring, requiring no hypothesis on `‖1‖`. -/
theorem norm_prod_one_add_sub_prod_one_add_le_exp {ι R : Type*} [DecidableEq ι]
    [SeminormedCommRing R] {s t : Finset ι} (ht : t ⊆ s) (u : ι → R) :
    ‖∏ i ∈ s, (1 + u i) - ∏ i ∈ t, (1 + u i)‖ ≤
      ‖∏ i ∈ t, (1 + u i)‖ * (Real.exp (∑ i ∈ s \ t, ‖u i‖) - 1) :=
  (norm_prod_one_add_sub_prod_one_add_le ht u).trans <| mul_le_mul_of_nonneg_left
    (sub_le_sub_right (Real.prod_one_add_le_exp_sum (s \ t) fun _ ↦ norm_nonneg _) 1)
    (norm_nonneg _)

end Finset

namespace TauCeti

section SeminormedCommRing

variable {ι R : Type*} [SeminormedCommRing R]

/-- **Sharp infinite-product majorant.** In a seminormed commutative ring,
`‖∏' i, (1 + f i) - 1‖ ≤ (∏' i, (1 + ‖f i‖)) - 1` whenever the norms `‖f i‖` are summable. -/
theorem norm_tprod_one_add_sub_one_le_tprod_one_add_norm_sub_one {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i) - 1‖ ≤ (∏' i, (1 + ‖f i‖)) - 1 := by
  have hm : Multipliable fun i ↦ 1 + ‖f i‖ := Real.multipliable_one_add_of_summable hf
  by_cases h : Multipliable fun i ↦ 1 + f i
  · refine le_of_tendsto' ((h.hasProd.sub_const 1).norm) fun s ↦ ?_
    exact (s.norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one f).trans <|
      sub_le_sub_right
        (hm.prod_le_tprod_of_nonneg (fun _ _ ↦ by positivity) fun _ _ ↦ by simp) 1
  · rw [tprod_eq_one_of_not_multipliable h, sub_self, norm_zero, sub_nonneg]
    simpa using hm.prod_le_tprod_of_nonneg (s := ∅) (by simp) fun _ _ ↦ by simp

/-- In a seminormed commutative ring, `‖∏' i, (1 + f i) - 1‖ ≤ exp (∑' i, ‖f i‖) - 1` whenever the
norms `‖f i‖` are summable. -/
theorem norm_tprod_one_add_sub_one_le {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i) - 1‖ ≤ Real.exp (∑' i, ‖f i‖) - 1 := by
  refine (norm_tprod_one_add_sub_one_le_tprod_one_add_norm_sub_one hf).trans <|
    sub_le_sub_right ?_ 1
  refine tprod_le_of_prod_le' (Real.one_le_exp (tsum_nonneg fun _ ↦ norm_nonneg _)) fun s ↦ ?_
  exact (Real.prod_one_add_le_exp_sum s fun _ ↦ norm_nonneg _).trans <|
    Real.exp_le_exp.2 (hf.sum_le_tsum s fun _ _ ↦ norm_nonneg _)

end SeminormedCommRing

section NormedCommRing

variable {ι R : Type*} [NormedCommRing R] [NormOneClass R]

/-- In a normed commutative ring with `‖1‖ = 1`, `‖∏' i, (1 + f i)‖ ≤ exp (∑' i, ‖f i‖)` whenever
the norms `‖f i‖` are summable. -/
theorem norm_tprod_one_add_le_exp_tsum {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i)‖ ≤ Real.exp (∑' i, ‖f i‖) := by
  by_cases h : Multipliable fun i ↦ 1 + f i
  · refine le_of_tendsto' (Filter.Tendsto.norm h.hasProd) fun s ↦ ?_
    calc ‖∏ i ∈ s, (1 + f i)‖ ≤ ∏ i ∈ s, ‖1 + f i‖ := Finset.norm_prod_le s _
      _ ≤ ∏ i ∈ s, (1 + ‖f i‖) := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          fun i _ ↦ (norm_add_le _ _).trans_eq (by rw [norm_one])
      _ ≤ Real.exp (∑ i ∈ s, ‖f i‖) := Real.prod_one_add_le_exp_sum s fun _ ↦ norm_nonneg _
      _ ≤ Real.exp (∑' i, ‖f i‖) :=
          Real.exp_le_exp.2 (hf.sum_le_tsum s fun _ _ ↦ norm_nonneg _)
  · rw [tprod_eq_one_of_not_multipliable h, norm_one]
    exact Real.one_le_exp (tsum_nonneg fun _ ↦ norm_nonneg _)

/-- In a complete normed commutative ring with multiplicative norm, an absolutely summable infinite
product `∏' i, (1 + f i)` vanishes if and only if one of its factors vanishes. -/
theorem tprod_one_add_eq_zero_iff [CompleteSpace R] [NormMulClass R] {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) :
    (∏' i, (1 + f i)) = 0 ↔ ∃ i, 1 + f i = 0 := by
  refine ⟨fun h0 ↦ ?_, tprod_of_exists_eq_zero⟩
  by_contra! hne
  exact tprod_one_add_ne_zero_of_summable hne hf h0

end NormedCommRing

end TauCeti
