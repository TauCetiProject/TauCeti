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
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import TauCeti.Analysis.Normed.Ring.Ultra
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Analysis.Normed.Group.NullFamily
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Bounds and ultrametric convergence for infinite products in normed rings

For `f` with summable norms, the infinite product `∏' i, (1 + f i)` in a normed commutative ring
has norm at most `exp (∑' i, ‖f i‖)`. Each finite partial product is bounded by
`∏ (1 + ‖f i‖) ≤ exp (∑ ‖f i‖)`, and the bound passes to the limit. This is the estimate used to
bound theta products and Siegel functions on the upper half-plane by elementary functions of
`|q|`. The same argument, from Mathlib's `Finset.norm_prod_one_add_sub_one_le`, bounds the distance
`‖∏' i, (1 + f i) - 1‖` by `exp (∑' i, ‖f i‖) - 1`, which controls such a product near the identity.

In a seminormed commutative ring, if `f` tends to zero along the cofinite filter, then the finite
products `∏ i ∈ s, f i` also tend to zero along the cofinite filter on `Finset ι`: only finitely
many terms have norm at least `1`, their norms multiply to a uniform bound `M` on all subproducts,
and any finite set containing an index with `‖f j‖ < ε / M` has product of norm less than `ε`. In
a complete ultrametric normed commutative ring, nonarchimedean summability turns this cofinite
vanishing into unconditional summability of `s ↦ ∏ i ∈ s, f i`, and hence unconditional
multipliability of `i ↦ 1 + f i` without requiring the factors to be units. Moreover, in any
ultrametric seminormed commutative ring, if every factor of a convergent product lies strictly
within `ε ≤ 1` of `1`, then so does the infinite product.

## Main results

* `TauCeti.norm_tprod_one_add_le_exp_tsum` and `TauCeti.norm_tprod_one_add_sub_one_le`:
  exponential norm bounds when `∑' i, ‖f i‖` converges.
* `Filter.Tendsto.finset_prod_of_cofinite`: if `f → 0` cofinitely in a seminormed commutative ring,
  then `s ↦ ∏ i ∈ s, f i` tends to `0` cofinitely.
* `TauCeti.summable_prod_of_tendsto_cofinite_zero`,
  `TauCeti.multipliable_one_add_of_tendsto_cofinite_zero` and
  `TauCeti.multipliable_of_tendsto_cofinite_one`: unconditional convergence of infinite products in
  complete ultrametric normed commutative rings.
* `HasProd.tendsto_cofinite_one_of_norm_sub_one_lt_one`, `HasProd.norm_sub_one_lt`,
  `TauCeti.norm_tprod_sub_one_lt` and `TauCeti.norm_tprod_one_add_sub_one_lt`: strict ultrametric
  perturbation bounds near `1`.
-/

public section

open Filter
open scoped Topology

/-- In a seminormed commutative ring, if `f` tends to zero along the cofinite filter, then the
finite products `∏ i ∈ s, f i` tend to zero along the cofinite filter on `Finset ι`. -/
theorem Filter.Tendsto.finset_prod_of_cofinite {ι R : Type*} [SeminormedCommRing R] {f : ι → R}
    (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto (fun s : Finset ι ↦ ∏ i ∈ s, f i) cofinite (𝓝 0) := by
  classical
  have hf0 : Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hf
  have hS₀ : {i : ι | ¬‖f i‖ < 1}.Finite :=
    Filter.eventually_cofinite.mp (hf0.eventually (Iio_mem_nhds zero_lt_one))
  let S₀ : Finset ι := hS₀.toFinset
  let M : ℝ := ∏ i ∈ S₀, ‖f i‖
  have hge1 {i : ι} (hi : i ∈ S₀) : 1 ≤ ‖f i‖ :=
    not_lt.mp (hS₀.mem_toFinset.mp hi)
  have hM1 : 1 ≤ M :=
    Finset.prod_const_one.symm.trans_le (Finset.prod_le_prod₀ (fun _ _ ↦ zero_le_one) fun _ ↦ hge1)
  have hM0 : 0 < M := zero_lt_one.trans_le hM1
  -- Every finite product of norms is bounded by the product `M` of those at least `1`.
  have hbound (t : Finset ι) : ∏ i ∈ t, ‖f i‖ ≤ M := calc
    ∏ i ∈ t, ‖f i‖ ≤ ∏ i ∈ t, max ‖f i‖ 1 :=
      Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ le_max_left _ _
    _ ≤ ∏ i ∈ t ∪ S₀, max ‖f i‖ 1 := by
      rw [← Finset.union_sdiff_of_subset (Finset.subset_union_left (s₁ := t) (s₂ := S₀)),
        Finset.prod_union Finset.disjoint_sdiff]
      exact le_mul_of_one_le_right
        (Finset.prod_nonneg fun _ _ ↦ zero_le_one.trans (le_max_right _ _))
        (Finset.prod_const_one.symm.trans_le
          (Finset.prod_le_prod₀ (fun _ _ ↦ zero_le_one) fun _ _ ↦ le_max_right _ _))
    _ = ∏ i ∈ S₀, max ‖f i‖ 1 := by
      symm
      refine Finset.prod_subset Finset.subset_union_right fun i _ hiS₀ ↦ ?_
      exact max_eq_right (le_of_not_ge fun h1 ↦ hiS₀ (hS₀.mem_toFinset.mpr (not_lt.mpr h1)))
    _ = M := Finset.prod_congr rfl fun i hi ↦ max_eq_left (hge1 hi)
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  have hS₁ : {i : ι | ¬‖f i‖ < ε / M}.Finite :=
    Filter.eventually_cofinite.mp (hf0.eventually (Iio_mem_nhds (div_pos hε hM0)))
  refine Filter.eventually_cofinite.mpr
    ((hS₁.toFinset.powerset.finite_toSet).subset fun s hs ↦ ?_)
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro j hj
  by_contra hjS₁
  have hfj : ‖f j‖ < ε / M := of_not_not (hS₁.mem_toFinset.not.mp hjS₁)
  have hlt : ‖∏ i ∈ s, f i‖ < ε := calc
    ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ :=
      TauCeti.norm_prod_le_prod_norm_of_nonempty ⟨j, hj⟩ f
    _ = ‖f j‖ * ∏ i ∈ s.erase j, ‖f i‖ := (Finset.mul_prod_erase s (‖f ·‖) hj).symm
    _ ≤ ‖f j‖ * M := mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    _ < ε / M * M := mul_lt_mul_of_pos_right hfj hM0
    _ = ε := div_mul_cancel₀ ε hM0.ne'
  exact hs (by simpa only [Real.dist_0_eq_abs, abs_of_nonneg (norm_nonneg _)] using hlt)

/-- In an ultrametric seminormed commutative ring, if `f` has a convergent infinite product and
every factor satisfies `‖f i - 1‖ < 1`, then `f` tends to `1` along the cofinite filter. Unlike in
a multiplicative group, this uses `‖f i - 1‖ < 1` so that finite partial products preserve the
distances `‖f i - 1‖`. -/
theorem HasProd.tendsto_cofinite_one_of_norm_sub_one_lt_one {ι R : Type*}
    [SeminormedCommRing R] [IsUltrametricDist R] {f : ι → R} {a : R} (hf : HasProd f a)
    (h : ∀ i, ‖f i - 1‖ < 1) : Tendsto f cofinite (𝓝 1) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlim : ∀ᶠ s : Finset ι in atTop, dist (∏ j ∈ s, f j) a < ε :=
    Metric.tendsto_nhds.mp hf ε hε
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp hlim
  refine Filter.eventually_cofinite.mpr (s₀.finite_toSet.subset fun i hi ↦ ?_)
  by_contra his₀
  rw [Finset.mem_coe] at his₀
  let u : R := ∏ j ∈ s₀, f j
  have hu : ‖u - 1‖ < 1 := TauCeti.norm_prod_sub_one_lt s₀ f zero_lt_one le_rfl fun j _ ↦ h j
  have hmul : ‖u * (f i - 1)‖ = ‖f i - 1‖ := by
    have h1 := TauCeti.norm_one_add_mul_of_norm_lt_one hu (f i - 1)
    rwa [add_sub_cancel] at h1
  have hprod : ∏ j ∈ insert i s₀, f j - u = u * (f i - 1) := by
    rw [Finset.prod_insert his₀]
    ring
  have hdist : ‖f i - 1‖ < ε := calc
    ‖f i - 1‖ = ‖∏ j ∈ insert i s₀, f j - u‖ := by rw [hprod, hmul]
    _ = ‖(∏ j ∈ insert i s₀, f j - a) + -(u - a)‖ := by congr 1; abel
    _ ≤ max ‖∏ j ∈ insert i s₀, f j - a‖ ‖u - a‖ := by
      simpa only [norm_neg] using
        IsUltrametricDist.norm_add_le_max (∏ j ∈ insert i s₀, f j - a) (-(u - a))
    _ < ε := max_lt
      (by simpa only [dist_eq_norm] using hs₀ (insert i s₀) (Finset.subset_insert i s₀))
      (by simpa only [dist_eq_norm] using hs₀ s₀ Finset.Subset.rfl)
  exact hi (by simpa only [dist_eq_norm] using hdist)

/-- In an ultrametric seminormed commutative ring, if `f` has product `a` and every factor lies
strictly within `ε ≤ 1` of `1`, then `‖a - 1‖ < ε`. -/
theorem HasProd.norm_sub_one_lt {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    {f : ι → R} {a : R} (hf : HasProd f a) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (h : ∀ i, ‖f i - 1‖ < ε) : ‖a - 1‖ < ε := by
  cases isEmpty_or_nonempty ι
  · refine (le_of_tendsto' (hf.sub_const 1).norm fun s ↦ ?_).trans_lt hε0
    rw [Finset.eq_empty_of_isEmpty s, Finset.prod_empty, sub_self, norm_zero]
  · have h0 : Tendsto (fun i ↦ f i - 1) cofinite (𝓝 0) := by
      simpa only [sub_self] using
        (hf.tendsto_cofinite_one_of_norm_sub_one_lt_one fun i ↦ (h i).trans_le hε).sub_const 1
    obtain ⟨i₀, hi₀⟩ := h0.exists_forall_norm_le
    have hi₀0 : 0 ≤ ‖f i₀ - 1‖ := norm_nonneg _
    have hi₀ε : ‖f i₀ - 1‖ < ε := h i₀
    let δ : ℝ := (‖f i₀ - 1‖ + ε) / 2
    have hδ0 : 0 < δ := div_pos (add_pos_of_nonneg_of_pos hi₀0 hε0) zero_lt_two
    have hδε : δ < ε := by
      rw [div_lt_iff₀ zero_lt_two]
      linarith
    have hi₀δ : ‖f i₀ - 1‖ < δ := by
      rw [lt_div_iff₀ zero_lt_two]
      linarith
    refine (le_of_tendsto' (hf.sub_const 1).norm fun s ↦ ?_).trans_lt hδε
    exact (TauCeti.norm_prod_sub_one_lt s f hδ0 (hδε.le.trans hε) fun j _ ↦
      (hi₀ j).trans_lt hi₀δ).le

namespace TauCeti

section Archimedean

variable {ι R : Type*} [NormedCommRing R] [NormOneClass R]

/-- In a normed commutative ring, `‖∏' i, (1 + f i)‖ ≤ exp (∑' i, ‖f i‖)` whenever the norms
`‖f i‖` are summable. -/
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

end Archimedean

section Ultrametric

/-- In an ultrametric seminormed commutative ring, if every factor lies strictly within `ε ≤ 1` of
`1`, then `‖∏' i, f i - 1‖ < ε`. -/
theorem norm_tprod_sub_one_lt {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    {f : ι → R} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (h : ∀ i, ‖f i - 1‖ < ε) :
    ‖∏' i, f i - 1‖ < ε := by
  by_cases hm : Multipliable f
  · exact hm.hasProd.norm_sub_one_lt hε0 hε h
  · rwa [tprod_eq_one_of_not_multipliable hm, sub_self, norm_zero]

/-- In an ultrametric seminormed commutative ring, if `‖f i‖ < ε` for every `i`, with
`0 < ε ≤ 1`, then `‖∏' i, (1 + f i) - 1‖ < ε`. -/
theorem norm_tprod_one_add_sub_one_lt {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    {f : ι → R} {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (h : ∀ i, ‖f i‖ < ε) :
    ‖∏' i, (1 + f i) - 1‖ < ε :=
  norm_tprod_sub_one_lt hε0 hε fun i ↦ by simpa only [add_sub_cancel_left] using h i

variable {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- In a complete ultrametric seminormed commutative ring, if `f` tends to zero along the cofinite
filter, then the family of finite products `s ↦ ∏ i ∈ s, f i` is unconditionally summable. -/
theorem summable_prod_of_tendsto_cofinite_zero {f : ι → R} (hf : Tendsto f cofinite (𝓝 0)) :
    Summable fun s : Finset ι ↦ ∏ i ∈ s, f i :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hf.finset_prod_of_cofinite

/-- In a complete ultrametric seminormed commutative ring, if `f` tends to zero along the cofinite
filter, then `i ↦ 1 + f i` is unconditionally multipliable. The factors need not be units. -/
theorem multipliable_one_add_of_tendsto_cofinite_zero {f : ι → R}
    (hf : Tendsto f cofinite (𝓝 0)) : Multipliable fun i ↦ 1 + f i :=
  multipliable_one_add_of_summable_prod (summable_prod_of_tendsto_cofinite_zero hf)

/-- In a complete ultrametric seminormed commutative ring, any family tending to `1` along the
cofinite filter is unconditionally multipliable, even when some factors are not units. -/
theorem multipliable_of_tendsto_cofinite_one {f : ι → R} (hf : Tendsto f cofinite (𝓝 1)) :
    Multipliable f := by
  have h0 : Tendsto (fun i ↦ f i - 1) cofinite (𝓝 0) := by
    simpa only [sub_self] using hf.sub_const 1
  simpa only [add_sub_cancel] using multipliable_one_add_of_tendsto_cofinite_zero h0

end Ultrametric

end TauCeti
