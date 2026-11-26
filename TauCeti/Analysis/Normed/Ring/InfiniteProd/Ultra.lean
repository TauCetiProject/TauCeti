/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# Unconditional infinite products in ultrametric normed rings

Over a commutative ultrametric seminormed ring `R`:

* Every family `f : ι → R` tending to `0` along the cofinite filter has summable finite partial
  products `s ↦ ∏ i ∈ s, f i` (`IsUltrametricDist.summable_prod_of_tendsto_cofinite_zero`) when
  `R` is complete, so `∏' i, (1 + f i)`, `∏' i, (1 - f i)`, and more generally `∏' i, g i` for any
  `g → 1` cofinitely are unconditionally multipliable without assuming the factors are units.
* In the Hausdorff complete case, `∏' i, (1 + f i) = ∑' s : Finset ι, ∏ i ∈ s, f i`
  (`IsUltrametricDist.tprod_one_add_eq_tsum_prod_of_tendsto_cofinite_zero`).
* Conversely, when every factor satisfies `‖f i - 1‖ < 1`, convergence of `HasProd f a` forces
  `f → 1` along `cofinite` (`HasProd.tendsto_cofinite_one_of_norm_sub_one_lt_one`), giving the
  characterisation `TauCeti.multipliable_iff_tendsto_cofinite_one_of_norm_sub_one_lt_one` in the
  complete case.
* Closed (`0 ≤ B ≤ 1`) and strict (`0 < ε ≤ 1`) perturbation bounds near `1` pass from the factors
  to any convergent `HasProd` limit (`HasProd.norm_sub_one_le`, `HasProd.norm_sub_one_lt`) without a
  Hausdorff hypothesis, and hence to the totalized infinite product `∏' i, f i`
  (`TauCeti.norm_tprod_sub_one_le`, `TauCeti.norm_tprod_sub_one_lt`).

## Main results

* `IsUltrametricDist.summable_prod_of_tendsto_cofinite_zero`,
  `IsUltrametricDist.multipliable_one_add_of_tendsto_cofinite_zero` and
  `IsUltrametricDist.multipliable_one_sub_of_tendsto_cofinite_zero`: unconditional convergence of
  `∏' i, (1 ± f i)` in a complete ultrametric seminormed commutative ring when `f → 0` cofinitely.
* `HasProd.tendsto_cofinite_one_of_norm_sub_one_lt_one`: factors of a convergent product with
  `‖f i - 1‖ < 1` tend to `1` along `cofinite`.
* `HasProd.norm_sub_one_le` and `HasProd.norm_sub_one_lt`: over a commutative ultrametric
  seminormed ring, closed (`0 ≤ B ≤ 1`) and strict (`0 < ε ≤ 1`) perturbation bounds near `1` for
  a supplied convergent product, without a Hausdorff hypothesis.
* `TauCeti.norm_tprod_sub_one_le` and `TauCeti.norm_tprod_sub_one_lt`: over a commutative
  ultrametric seminormed ring, totalized infinite products `∏' i, f i` (which default to `1` for
  nonmultipliable families) of elements within `B` (`0 ≤ B ≤ 1`) or strictly within `ε`
  (`0 < ε ≤ 1`) of `1` satisfy the same bound.
* `IsUltrametricDist.multipliable_of_tendsto_cofinite_one` and
  `TauCeti.multipliable_iff_tendsto_cofinite_one_of_norm_sub_one_lt_one`: in a complete
  ultrametric seminormed commutative ring, any family tending to `1` cofinitely is unconditionally
  multipliable, and conversely when every factor satisfies `‖f i - 1‖ < 1`.
* `IsUltrametricDist.tprod_one_add_eq_tsum_prod_of_tendsto_cofinite_zero`: in the Hausdorff complete
  ultrametric case, factors `1 + f i` with `f → 0` cofinitely satisfy
  `∏' i, (1 + f i) = ∑' s : Finset ι, ∏ i ∈ s, f i`.
-/

public section

open Filter
open scoped Topology

/-- In a complete ultrametric seminormed commutative ring, if `f` tends to `0` along the cofinite
filter, then the family of finite partial products `s ↦ ∏ i ∈ s, f i` is summable. -/
theorem IsUltrametricDist.summable_prod_of_tendsto_cofinite_zero {ι R : Type*}
    [SeminormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {f : ι → R}
    (hf : Tendsto f cofinite (nhds 0)) :
    Summable fun s : Finset ι ↦ ∏ i ∈ s, f i :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (TauCeti.tendsto_finsetProd_cofinite_zero hf)

/-- In a complete ultrametric seminormed commutative ring, `∏' i, (1 + f i)` is unconditionally
multipliable whenever `f` tends to `0` along the cofinite filter. Unlike
`NonarchimedeanGroup.multipliable_of_tendsto_cofinite_one`, the factors `1 + f i` need not be
units. -/
theorem IsUltrametricDist.multipliable_one_add_of_tendsto_cofinite_zero {ι R : Type*}
    [SeminormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {f : ι → R}
    (hf : Tendsto f cofinite (nhds 0)) :
    Multipliable fun i ↦ 1 + f i :=
  multipliable_one_add_of_summable_prod
    (IsUltrametricDist.summable_prod_of_tendsto_cofinite_zero hf)

/-- In a complete ultrametric seminormed commutative ring, `∏' i, (1 - f i)` is unconditionally
multipliable whenever `f` tends to `0` along the cofinite filter. -/
theorem IsUltrametricDist.multipliable_one_sub_of_tendsto_cofinite_zero {ι R : Type*}
    [SeminormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {f : ι → R}
    (hf : Tendsto f cofinite (nhds 0)) :
    Multipliable fun i ↦ 1 - f i := by
  simpa only [sub_eq_add_neg] using
    IsUltrametricDist.multipliable_one_add_of_tendsto_cofinite_zero (by simpa using hf.neg)

namespace TauCeti

/-- In an ultrametric seminormed commutative ring, if `f` has a convergent infinite product and
every factor satisfies `‖f i - 1‖ < 1`, then `f` tends to `1` along the cofinite filter. Unlike in
a multiplicative group, this uses `‖f i - 1‖ < 1` so that finite partial products preserve the
distances `‖f i - 1‖`. -/
theorem _root_.HasProd.tendsto_cofinite_one_of_norm_sub_one_lt_one {ι R : Type*}
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
within `B ≤ 1` of `1` (`0 ≤ B`), then `‖a - 1‖ ≤ B`. This is the `HasProd` form of
`TauCeti.norm_tprod_sub_one_le`, which needs no Hausdorff hypothesis. -/
theorem _root_.HasProd.norm_sub_one_le {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    {f : ι → R} {a : R} (hf : HasProd f a) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (h : ∀ i, ‖f i - 1‖ ≤ B) : ‖a - 1‖ ≤ B :=
  le_of_tendsto' (hf.sub_const 1).norm fun s ↦
    TauCeti.norm_prod_sub_one_le s f hB0 hB1 fun i _ ↦ h i

/-- In an ultrametric seminormed commutative ring, if `f` has product `a` and every factor lies
strictly within `ε` of `1` (`0 < ε ≤ 1`), then `‖a - 1‖ < ε`. This is the `HasProd` form of
`TauCeti.norm_tprod_sub_one_lt`, which needs no Hausdorff hypothesis. -/
theorem _root_.HasProd.norm_sub_one_lt {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    {f : ι → R} {a : R} (hf : HasProd f a) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (h : ∀ i, ‖f i - 1‖ < ε) : ‖a - 1‖ < ε := by
  obtain ⟨s₀, hs₀⟩ := (hf.eventually (Metric.ball_mem_nhds a hε0)).exists
  have h1 : ‖a - ∏ i ∈ s₀, f i‖ < ε := by
    rw [← dist_eq_norm, dist_comm]
    exact Metric.mem_ball.mp hs₀
  calc ‖a - 1‖ = ‖(a - ∏ i ∈ s₀, f i) + ((∏ i ∈ s₀, f i) - 1)‖ := by rw [sub_add_sub_cancel]
    _ ≤ max ‖a - ∏ i ∈ s₀, f i‖ ‖(∏ i ∈ s₀, f i) - 1‖ := IsUltrametricDist.norm_add_le_max _ _
    _ < ε := max_lt h1 (TauCeti.norm_prod_sub_one_lt s₀ f hε0 hε fun i _ ↦ h i)

/-- In an ultrametric seminormed commutative ring, the totalized infinite product `∏' i, f i`
(which defaults to `1` when `f` is not multipliable) of elements each within `B` of `1`
(`0 ≤ B ≤ 1`) satisfies `‖(∏' i, f i) - 1‖ ≤ B`. See `HasProd.norm_sub_one_le` for bounds on
actual limits of convergent products. -/
theorem norm_tprod_sub_one_le {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    (f : ι → R) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hf : ∀ i, ‖f i - 1‖ ≤ B) : ‖(∏' i, f i) - 1‖ ≤ B := by
  by_cases hm : Multipliable f
  · exact hm.hasProd.norm_sub_one_le hB0 hB1 hf
  · simpa [tprod_eq_one_of_not_multipliable hm] using hB0

/-- In an ultrametric seminormed commutative ring, the totalized infinite product `∏' i, f i`
(which defaults to `1` when `f` is not multipliable) of elements each strictly within `ε` of `1`
(`0 < ε ≤ 1`) satisfies `‖(∏' i, f i) - 1‖ < ε`. See `HasProd.norm_sub_one_lt` for bounds on
actual limits of convergent products. -/
theorem norm_tprod_sub_one_lt {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    (f : ι → R) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hf : ∀ i, ‖f i - 1‖ < ε) : ‖(∏' i, f i) - 1‖ < ε := by
  by_cases hm : Multipliable f
  · exact hm.hasProd.norm_sub_one_lt hε0 hε hf
  · simpa [tprod_eq_one_of_not_multipliable hm] using hε0

/-- In a complete ultrametric seminormed commutative ring, any family tending to `1` along the
cofinite filter is unconditionally multipliable, even when some factors are not units. -/
theorem _root_.IsUltrametricDist.multipliable_of_tendsto_cofinite_one {ι R : Type*}
    [SeminormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {f : ι → R}
    (hf : Tendsto f cofinite (𝓝 1)) : Multipliable f := by
  have h0 : Tendsto (fun i ↦ f i - 1) cofinite (𝓝 0) := by
    simpa only [sub_self] using hf.sub_const 1
  simpa only [add_sub_cancel] using
    _root_.IsUltrametricDist.multipliable_one_add_of_tendsto_cofinite_zero h0

/-- In a complete ultrametric seminormed commutative ring, a family whose factors all satisfy
`‖f i - 1‖ < 1` is unconditionally multipliable if and only if it tends to `1` along `cofinite`. -/
theorem multipliable_iff_tendsto_cofinite_one_of_norm_sub_one_lt_one
    {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {f : ι → R}
    (h : ∀ i, ‖f i - 1‖ < 1) : Multipliable f ↔ Tendsto f cofinite (𝓝 1) :=
  ⟨fun hf ↦ hf.hasProd.tendsto_cofinite_one_of_norm_sub_one_lt_one h,
    _root_.IsUltrametricDist.multipliable_of_tendsto_cofinite_one⟩

/-- In a complete Hausdorff ultrametric seminormed commutative ring, if `f → 0` along `cofinite`,
then `∏' i, (1 + f i) = ∑' s : Finset ι, ∏ i ∈ s, f i`. -/
theorem _root_.IsUltrametricDist.tprod_one_add_eq_tsum_prod_of_tendsto_cofinite_zero {ι R : Type*}
    [SeminormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [T2Space R] {f : ι → R}
    (hf : Tendsto f cofinite (𝓝 0)) :
    ∏' i, (1 + f i) = ∑' s : Finset ι, ∏ i ∈ s, f i :=
  tprod_one_add (_root_.IsUltrametricDist.summable_prod_of_tendsto_cofinite_zero hf)

end TauCeti
