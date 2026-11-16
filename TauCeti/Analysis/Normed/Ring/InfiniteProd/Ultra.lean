/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TauCeti.Analysis.Normed.Group.NullFamily
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# Unconditional infinite products in ultrametric rings

In a complete ultrametric seminormed commutative ring, a family `f : ι → R` tending to `1` along
the cofinite filter is unconditionally multipliable, without requiring absolute summability of
`‖f i - 1‖`, countability of `ι`, or `‖1‖ = 1`. Indeed, if `a i → 0` along `cofinite`, then the
elementary symmetric terms `s ↦ ∏ i ∈ s, a i` over `Finset ι` also tend to `0` along `cofinite`
(an inequality that needs only submultiplicativity of the norm, not the ultrametric inequality);
ultrametric completeness therefore makes `s ↦ ∏ i ∈ s, a i` summable, and Mathlib's
`multipliable_one_add_of_summable_prod` yields `∏' i, (1 + a i) = ∑' s : Finset ι, ∏ i ∈ s, a i`.

Conversely, whenever every factor lies in the open ball `‖f i - 1‖ < 1`, multiplication by any
finite partial product preserves norms (`TauCeti.norm_one_add_mul_of_norm_lt_one`), so any
`HasProd f a` forces `f → 1` along `cofinite`. Combining this with the attained maximum of a null
family (`Filter.Tendsto.exists_forall_norm_le`) extends the ultrametric distance-to-one estimates
to infinite products: if `0 < B ≤ 1` and `‖f i - 1‖ < B` for every `i`, then `‖a - 1‖ < B`.

## Main results

* `TauCeti.tendsto_prod_cofinite_zero`: if `f → 0` along `cofinite` in a seminormed commutative
  ring, then `s ↦ ∏ i ∈ s, f i` tends to `0` along `cofinite` on `Finset ι`.
* `TauCeti.summable_prod_of_tendsto_cofinite`: in a complete ultrametric seminormed commutative
  ring, `s ↦ ∏ i ∈ s, f i` is summable whenever `f → 0` along `cofinite`.
* `TauCeti.multipliable_of_tendsto_cofinite_one` and
  `TauCeti.tprod_one_add_eq_tsum_prod_of_tendsto_cofinite`: unconditional convergence of
  ultrametric infinite products and their symmetric-sum expansion.
* `HasProd.tendsto_cofinite_one_of_forall_norm_sub_one_lt_one` and
  `TauCeti.multipliable_iff_tendsto_cofinite_one_of_forall_norm_sub_one_lt_one`: equivalence of
  multipliability and tending to `1` when every factor satisfies `‖f i - 1‖ < 1`.
* `HasProd.norm_sub_one_le_of_forall_norm_sub_one_le` and
  `HasProd.norm_sub_one_lt_of_forall_norm_sub_one_lt`: closed and strict ultrametric bounds on
  `‖a - 1‖` for a `HasProd` limit.
-/

public section

open Filter
open scoped Topology

section HasProd

variable {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R] {f : ι → R} {a : R}

/-- In an ultrametric seminormed ring, if `a` and `b` are within `B ≤ 1` of `1`, so is `a * b`. -/
private theorem norm_mul_sub_one_le {R : Type*} [SeminormedRing R] [IsUltrametricDist R] {a b : R}
    {B : ℝ} (hB : B ≤ 1) (ha : ‖a - 1‖ ≤ B) (hb : ‖b - 1‖ ≤ B) : ‖a * b - 1‖ ≤ B := by
  calc ‖a * b - 1‖ = ‖(a - 1) * (b - 1) + (a - 1) + (b - 1)‖ := by
        congr 1
        simp only [mul_sub, sub_mul, mul_one, one_mul]
        abel
    _ ≤ max (max ‖(a - 1) * (b - 1)‖ ‖a - 1‖) ‖b - 1‖ :=
      (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max (IsUltrametricDist.norm_add_le_max _ _) le_rfl)
    _ ≤ B := max_le (max_le ((norm_mul_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (hb.trans hB)).trans ha)) ha) hb

/-- In an ultrametric seminormed commutative ring, a finite product of elements within `B ≤ 1` of
`1` is again within `B` of `1` (for `0 ≤ B`). -/
private theorem norm_prod_sub_one_le (s : Finset ι) (f : ι → R) {B : ℝ} (hB0 : 0 ≤ B)
    (hB1 : B ≤ 1) (hf : ∀ i ∈ s, ‖f i - 1‖ ≤ B) : ‖∏ i ∈ s, f i - 1‖ ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact norm_mul_sub_one_le hB1 (hf j (Finset.mem_insert_self j s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- **Factors of a convergent ultrametric product near `1` tend to `1`.** If `HasProd f a` in an
ultrametric seminormed commutative ring and every factor satisfies `‖f i - 1‖ < 1`, then `f → 1`
along `cofinite`. The bound `‖f i - 1‖ < 1` prevents a factor from annihilating the partial
products. -/
theorem HasProd.tendsto_cofinite_one_of_forall_norm_sub_one_lt_one (hf : HasProd f a)
    (h1 : ∀ i, ‖f i - 1‖ < 1) : Tendsto f cofinite (𝓝 1) := by
  classical
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨s₀, hs₀⟩ := Metric.tendsto_atTop.mp hf ε hε
  refine eventually_cofinite.mpr (s₀.finite_toSet.subset fun i hi ↦ ?_)
  by_contra his₀
  -- Multiplying `f i - 1` by the partial product `P = ∏ j ∈ s₀, f j` preserves its norm because
  -- `‖P - 1‖ < 1`.
  have hP : ‖∏ j ∈ s₀, f j - 1‖ < 1 :=
    TauCeti.norm_prod_sub_one_lt s₀ f zero_lt_one le_rfl fun j _ ↦ h1 j
  have hnorm : ‖f i - 1‖ = dist (∏ j ∈ insert i s₀, f j) (∏ j ∈ s₀, f j) := by
    rw [dist_eq_norm, Finset.prod_insert his₀, ← sub_one_mul, mul_comm,
      show ∏ j ∈ s₀, f j = 1 + (∏ j ∈ s₀, f j - 1) by abel,
      TauCeti.norm_one_add_mul_of_norm_lt_one hP]
  have hlt : dist (f i) 1 < ε := by
    rw [dist_eq_norm, hnorm]
    exact (IsUltrametricDist.dist_triangle_max _ a _).trans_lt
      (max_lt (hs₀ (insert i s₀) (Finset.subset_insert i s₀))
        (by rw [dist_comm]; exact hs₀ s₀ le_rfl))
  exact hi hlt

/-- **Closed ultrametric bound near `1` for an infinite product.** If `HasProd f a` in an
ultrametric seminormed commutative ring and every factor satisfies `‖f i - 1‖ ≤ B` with
`0 ≤ B ≤ 1`, then `‖a - 1‖ ≤ B`. -/
theorem HasProd.norm_sub_one_le_of_forall_norm_sub_one_le (hf : HasProd f a) {B : ℝ} (hB0 : 0 ≤ B)
    (hB1 : B ≤ 1) (h : ∀ i, ‖f i - 1‖ ≤ B) : ‖a - 1‖ ≤ B :=
  le_of_tendsto' (hf.sub_const 1).norm fun s ↦ norm_prod_sub_one_le s f hB0 hB1 fun i _ ↦ h i

/-- **Strict ultrametric bound near `1` for an infinite product.** If `HasProd f a` in an
ultrametric seminormed commutative ring and every factor satisfies `‖f i - 1‖ < B` with
`0 < B ≤ 1`, then `‖a - 1‖ < B`. This includes empty index types and families with `f i = 1`. -/
theorem HasProd.norm_sub_one_lt_of_forall_norm_sub_one_lt (hf : HasProd f a) {B : ℝ} (hB0 : 0 < B)
    (hB1 : B ≤ 1) (h : ∀ i, ‖f i - 1‖ < B) : ‖a - 1‖ < B := by
  cases isEmpty_or_nonempty ι
  · exact (hf.norm_sub_one_le_of_forall_norm_sub_one_le le_rfl zero_le_one isEmptyElim).trans_lt hB0
  · have hlim : Tendsto (fun i ↦ f i - 1) cofinite (𝓝 0) := by
      simpa only [sub_self] using
        (hf.tendsto_cofinite_one_of_forall_norm_sub_one_lt_one fun i ↦ (h i).trans_le hB1).sub_const
          1
    obtain ⟨i, hi⟩ := hlim.exists_forall_norm_le
    exact (hf.norm_sub_one_le_of_forall_norm_sub_one_le (norm_nonneg _) ((h i).le.trans hB1) hi)
      |>.trans_lt (h i)

end HasProd

namespace TauCeti

section SeminormedCommRing

variable {ι R : Type*} [SeminormedCommRing R]

/-- **Finite products of a null family tend to zero.** In any seminormed commutative ring, if
`f : ι → R` tends to `0` along `cofinite`, then `s ↦ ∏ i ∈ s, f i` tends to `0` along `cofinite`
on `Finset ι`. Neither the ultrametric inequality nor `‖1‖ = 1` is required. -/
theorem tendsto_prod_cofinite_zero {f : ι → R} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto (fun s : Finset ι ↦ ∏ i ∈ s, f i) cofinite (𝓝 0) := by
  classical
  have hnorm : Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0) := by
    simpa only [norm_zero] using hf.norm
  -- Only finitely many terms have norm exceeding `1`; their product `B ≥ 1` absorbs them.
  have hT : {i | ¬ ‖f i‖ ≤ 1}.Finite :=
    eventually_cofinite.mp (hnorm.eventually (ge_mem_nhds zero_lt_one))
  set T : Finset ι := hT.toFinset
  set B : ℝ := ∏ i ∈ T, ‖f i‖
  have hTgt : ∀ i ∈ T, 1 < ‖f i‖ := fun i hi ↦ not_le.mp (hT.mem_toFinset.mp hi)
  have hB1 : 1 ≤ B := Finset.one_le_prod₀ fun i hi ↦ (hTgt i hi).le
  have hB0 : 0 < B := zero_lt_one.trans_le hB1
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hU : {i | ¬ ‖f i‖ < ε / B}.Finite :=
    eventually_cofinite.mp (hnorm.eventually (gt_mem_nhds (div_pos hε hB0)))
  refine eventually_cofinite.mpr ((T ∪ hU.toFinset).powerset.finite_toSet.subset fun s hs ↦ ?_)
  by_contra hsF
  rw [Finset.mem_coe, Finset.mem_powerset] at hsF
  obtain ⟨i₀, hi₀s, hi₀F⟩ := Finset.not_subset.mp hsF
  have hi₀U : ‖f i₀‖ < ε / B := by
    by_contra h
    exact hi₀F (Finset.mem_union_right _ (hU.mem_toFinset.mpr h))
  -- Split the remaining factors of `s` into those in `T` (bounded by `B`) and outside `T` (`≤ 1`).
  have hrest : ∏ i ∈ s.erase i₀, ‖f i‖ ≤ B := by
    rw [← Finset.prod_inter_mul_prod_sdiff (s.erase i₀) T]
    refine mul_le_of_le_one_right (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
      (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i hi ↦ ?_) |>.trans ?_
    · by_contra h
      exact (Finset.mem_sdiff.mp hi).2 (hT.mem_toFinset.mpr h)
    · exact Finset.prod_le_prod_of_subset_of_one_le₀ Finset.inter_subset_right
        (fun _ _ ↦ norm_nonneg _) fun i hi _ ↦ (hTgt i hi).le
  have hlt : dist (∏ i ∈ s, f i) 0 < ε := by
    rw [dist_zero_right]
    calc ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := norm_prod_le_prod_norm_of_nonempty ⟨i₀, hi₀s⟩ f
      _ = ‖f i₀‖ * ∏ i ∈ s.erase i₀, ‖f i‖ := (Finset.mul_prod_erase s _ hi₀s).symm
      _ ≤ ‖f i₀‖ * B := mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
      _ < (ε / B) * B := mul_lt_mul_of_pos_right hi₀U hB0
      _ = ε := div_mul_cancel₀ ε hB0.ne'
  exact hs hlt

end SeminormedCommRing

section CompleteUltra

variable {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- **Summability of finite products of a null family.** In a complete ultrametric seminormed
commutative ring, if `f → 0` along `cofinite`, then `s ↦ ∏ i ∈ s, f i` is summable over
`Finset ι`. -/
theorem summable_prod_of_tendsto_cofinite {f : ι → R} (hf : Tendsto f cofinite (𝓝 0)) :
    Summable fun s : Finset ι ↦ ∏ i ∈ s, f i :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_prod_cofinite_zero hf)

/-- **Ultrametric convergence test for infinite products.** In a complete ultrametric seminormed
commutative ring, any family `f : ι → R` tending to `1` along `cofinite` is unconditionally
multipliable. -/
theorem multipliable_of_tendsto_cofinite_one {f : ι → R} (hf : Tendsto f cofinite (𝓝 1)) :
    Multipliable f := by
  have h0 : Tendsto (fun i ↦ f i - 1) cofinite (𝓝 0) := by
    simpa only [sub_self] using hf.sub_const 1
  simpa only [add_sub_cancel] using
    multipliable_one_add_of_summable_prod (summable_prod_of_tendsto_cofinite h0)

/-- **Equivalence of ultrametric multipliability near `1`.** In a complete ultrametric seminormed
commutative ring, a family whose factors all satisfy `‖f i - 1‖ < 1` is unconditionally
multipliable if and only if it tends to `1` along `cofinite`. -/
theorem multipliable_iff_tendsto_cofinite_one_of_forall_norm_sub_one_lt_one {f : ι → R}
    (h1 : ∀ i, ‖f i - 1‖ < 1) : Multipliable f ↔ Tendsto f cofinite (𝓝 1) :=
  ⟨fun hf ↦ hf.hasProd.tendsto_cofinite_one_of_forall_norm_sub_one_lt_one h1,
    multipliable_of_tendsto_cofinite_one⟩

/-- **Symmetric-sum expansion of an ultrametric infinite product.** In a complete Hausdorff
ultrametric seminormed commutative ring, if `f → 0` along `cofinite`, then
`∏' i, (1 + f i) = ∑' s : Finset ι, ∏ i ∈ s, f i`. -/
theorem tprod_one_add_eq_tsum_prod_of_tendsto_cofinite [T2Space R] {f : ι → R}
    (hf : Tendsto f cofinite (𝓝 0)) :
    ∏' i, (1 + f i) = ∑' s : Finset ι, ∏ i ∈ s, f i :=
  tprod_one_add (summable_prod_of_tendsto_cofinite hf)

end CompleteUltra

end TauCeti
