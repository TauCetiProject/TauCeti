/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.PartitionOfUnity
import TauCeti.Topology.Algebra.InfiniteSum.Real
import TauCeti.Topology.Order.Lattice

/-!
# Normalizing locally finite positive families and shrinking supports of partitions of unity

A locally finite family of nonnegative continuous functions `(f i)_{i ∈ ι}` on a topological space
`X` that is positive at each point normalizes to a partition of unity `PartitionOfUnity.ofExistsPos`
with weights `f i x / ∑ᶠ j, f j x` and the same open and closed supports as `f`.

Applying this normalization to the truncated weights `max 0 (ρ i x - (⨆ j, ρ j x) / 2)` of any
partition of unity `ρ : PartitionOfUnity ι X` yields a shrunken partition of unity `ρ.shrink` whose
closed supports lie inside the open supports of `ρ`: `tsupport (ρ.shrink i) ⊆ support (ρ i)`. In
particular, if every open support `support (ρ i)` lies in `U i`, then `ρ.shrink` is subordinate to
`U` in the closed-support sense (`PartitionOfUnity.IsSubordinate`). Neither separation nor normality
of `X`, nor openness of the sets `U i`, is used.

## Main definitions and results

* `PartitionOfUnity.ofExistsPos`: normalize a locally finite nonnegative family positive at every
  point into a partition of unity.
* `TauCeti.halfThresholdTrunc` and `PartitionOfUnity.shrinkOfThreshold`: truncate a family of
  continuous weights below half of a continuous positive function `m` (such as their pointwise
  maximum) and normalize when the truncated supports are locally finite.
* `TauCeti.continuous_ciSup_of_hasSum_one` and
  `TauCeti.locallyFinite_support_halfThresholdTrunc_of_hasSum_one`: continuity of the pointwise
  supremum and local finiteness after truncation for any family of continuous nonnegative weights
  summing pointwise to `1`.
* `PartitionOfUnity.shrink`: shrink the closed supports of a partition of unity on `X` inside its
  open supports, with weights given by `PartitionOfUnity.shrink_apply`.
* `PartitionOfUnity.shrink_pos_iff` and `PartitionOfUnity.support_shrink`: `ρ.shrink i` is positive
  (equivalently, supported) at `x` precisely when `(⨆ j, ρ j x) / 2 < ρ i x`.
* `PartitionOfUnity.tsupport_shrink_subset_support`: `tsupport (ρ.shrink i) ⊆ support (ρ i)`.
* `PartitionOfUnity.isSubordinate_shrink`: open-support subordination `∀ i, support (ρ i) ⊆ U i`
  upgrades to `ρ.shrink.IsSubordinate U`.

## References

* A. Dold, *Partitions of unity in the theory of fibrations*, Ann. of Math. (2) 78 (1963),
  223–255, §2.
-/

public section

open Function Set Filter Topology

variable {ι X : Type*} [TopologicalSpace X]

namespace PartitionOfUnity

section OfExistsPos

/-- Normalize a locally finite family of nonnegative continuous functions that is positive at every
point into a partition of unity on `X`. -/
noncomputable def ofExistsPos (f : ι → C(X, ℝ)) (hlf : LocallyFinite fun i ↦ support (f i))
    (hnn : ∀ i x, 0 ≤ f i x) (hpos : ∀ x, ∃ i, 0 < f i x) : PartitionOfUnity ι X where
  toFun i := ⟨fun x ↦ f i x / ∑ᶠ j, f j x,
    (f i).continuous.div (continuous_finsum (fun j ↦ (f j).continuous) hlf)
      fun x ↦ (finsum_pos (hnn · x) (hpos x) (hlf.point_finite x)).ne'⟩
  locallyFinite' := hlf.subset fun i x hx h0 ↦ hx (by simp [h0])
  nonneg' i x := div_nonneg (hnn i x) (finsum_nonneg fun j ↦ hnn j x)
  sum_eq_one' x _ := by
    simp only [ContinuousMap.coe_mk, div_eq_mul_inv]
    rw [← finsum_mul, mul_inv_cancel₀ (finsum_pos (hnn · x) (hpos x) (hlf.point_finite x)).ne']
  sum_le_one' x := by
    simp only [ContinuousMap.coe_mk, div_eq_mul_inv]
    rw [← finsum_mul, mul_inv_cancel₀ (finsum_pos (hnn · x) (hpos x) (hlf.point_finite x)).ne']

/-- Each weight of `PartitionOfUnity.ofExistsPos` is `f i x` divided by the finite sum
`∑ᶠ j, f j x`. -/
@[simp]
theorem ofExistsPos_apply (f : ι → C(X, ℝ)) (hlf : LocallyFinite fun i ↦ support (f i))
    (hnn : ∀ i x, 0 ≤ f i x) (hpos : ∀ x, ∃ i, 0 < f i x) (i : ι) (x : X) :
    ofExistsPos f hlf hnn hpos i x = f i x / ∑ᶠ j, f j x :=
  (rfl)

/-- A normalized weight of `PartitionOfUnity.ofExistsPos` is positive if and only if the original
weight is positive. -/
theorem ofExistsPos_pos_iff (f : ι → C(X, ℝ)) (hlf : LocallyFinite fun i ↦ support (f i))
    (hnn : ∀ i x, 0 ≤ f i x) (hpos : ∀ x, ∃ i, 0 < f i x) (i : ι) (x : X) :
    0 < ofExistsPos f hlf hnn hpos i x ↔ 0 < f i x :=
  div_pos_iff_of_pos_right (finsum_pos (hnn · x) (hpos x) (hlf.point_finite x))

/-- Normalization via `PartitionOfUnity.ofExistsPos` preserves open supports. -/
@[simp]
theorem support_ofExistsPos (f : ι → C(X, ℝ)) (hlf : LocallyFinite fun i ↦ support (f i))
    (hnn : ∀ i x, 0 ≤ f i x) (hpos : ∀ x, ∃ i, 0 < f i x) (i : ι) :
    support ⇑(ofExistsPos f hlf hnn hpos i) = support ⇑(f i) := by
  ext x
  simp only [mem_support, ofExistsPos_apply]
  exact ⟨fun h h0 ↦ h (by simp [h0]),
    fun h ↦ div_ne_zero h (finsum_pos (hnn · x) (hpos x) (hlf.point_finite x)).ne'⟩

/-- Normalization via `PartitionOfUnity.ofExistsPos` preserves closed supports. -/
@[simp]
theorem tsupport_ofExistsPos (f : ι → C(X, ℝ)) (hlf : LocallyFinite fun i ↦ support (f i))
    (hnn : ∀ i x, 0 ≤ f i x) (hpos : ∀ x, ∃ i, 0 < f i x) (i : ι) :
    tsupport ⇑(ofExistsPos f hlf hnn hpos i) = tsupport ⇑(f i) := by
  rw [tsupport, tsupport, support_ofExistsPos]

end OfExistsPos

end PartitionOfUnity

namespace TauCeti

section HalfThresholdTrunc

/-- Truncate a continuous weight `f i` below half of `m`: `x ↦ max 0 (f i x - m x / 2)`. -/
noncomputable def halfThresholdTrunc (f : ι → C(X, ℝ)) (m : C(X, ℝ)) (i : ι) : C(X, ℝ) :=
  ⟨fun x ↦ max 0 (f i x - m x / 2),
    continuous_const.max ((f i).continuous.sub (m.continuous.div_const 2))⟩

/-- Pointwise formula for `TauCeti.halfThresholdTrunc`. -/
@[simp]
theorem halfThresholdTrunc_apply (f : ι → C(X, ℝ)) (m : C(X, ℝ)) (i : ι) (x : X) :
    halfThresholdTrunc f m i x = max 0 (f i x - m x / 2) :=
  (rfl)

/-- Each truncated weight `TauCeti.halfThresholdTrunc` is nonnegative. -/
theorem halfThresholdTrunc_nonneg (f : ι → C(X, ℝ)) (m : C(X, ℝ)) (i : ι) (x : X) :
    0 ≤ halfThresholdTrunc f m i x :=
  le_max_left _ _

/-- A truncated weight `TauCeti.halfThresholdTrunc f m i x` is positive iff `m x / 2 < f i x`. -/
theorem halfThresholdTrunc_pos_iff {f : ι → C(X, ℝ)} {m : C(X, ℝ)} {i : ι} {x : X} :
    0 < halfThresholdTrunc f m i x ↔ m x / 2 < f i x := by
  rw [halfThresholdTrunc_apply, lt_max_iff, or_iff_right (lt_irrefl 0), sub_pos]

/-- A point `x` lies in the open support of `TauCeti.halfThresholdTrunc f m i` iff
`m x / 2 < f i x`. -/
theorem mem_support_halfThresholdTrunc_iff {f : ι → C(X, ℝ)} {m : C(X, ℝ)} {i : ι} {x : X} :
    x ∈ support (halfThresholdTrunc f m i) ↔ m x / 2 < f i x :=
  (halfThresholdTrunc_nonneg f m i x).lt_iff_ne'.symm.trans halfThresholdTrunc_pos_iff

/-- When `m` is positive everywhere, the open support of `halfThresholdTrunc f m i` lies in
`support (f i)`. -/
theorem support_halfThresholdTrunc_subset {f : ι → C(X, ℝ)} {m : C(X, ℝ)} (hm : ∀ x, 0 < m x)
    (i : ι) : support (halfThresholdTrunc f m i) ⊆ support (f i) :=
  fun x hx ↦ ((half_pos (hm x)).trans (mem_support_halfThresholdTrunc_iff.mp hx)).ne'

/-- When `m` is continuous and positive everywhere, the closed support of `halfThresholdTrunc f m i`
lies in the open support `support (f i)`. -/
theorem tsupport_halfThresholdTrunc_subset {f : ι → C(X, ℝ)} {m : C(X, ℝ)} (hm : ∀ x, 0 < m x)
    (i : ι) : tsupport (halfThresholdTrunc f m i) ⊆ support (f i) := by
  intro x hx
  have hclosed : IsClosed {y : X | m y / 2 ≤ f i y} :=
    isClosed_le (m.continuous.div_const 2) (f i).continuous
  have hle : m x / 2 ≤ f i x :=
    closure_minimal (fun y hy ↦ (mem_support_halfThresholdTrunc_iff.mp hy).le) hclosed hx
  exact ((half_pos (hm x)).trans_le hle).ne'

end HalfThresholdTrunc

section HasSumOne

private theorem bddAbove_range_of_hasSum_one (f : ι → C(X, ℝ)) (hnn : ∀ i x, 0 ≤ f i x)
    (hsum : ∀ x, HasSum (fun i ↦ f i x) 1) (x : X) : BddAbove (range fun i ↦ f i x) :=
  ⟨1, forall_mem_range.2 fun j ↦ le_hasSum (hsum x) j fun k _ ↦ hnn k x⟩

private theorem eventually_tail_lt_and_half_lt_finSup_of_hasSum_one (f : ι → C(X, ℝ))
    (hnn : ∀ i x, 0 ≤ f i x) (hsum : ∀ x, HasSum (fun i ↦ f i x) 1) (x₀ : X) :
    ∃ (I : Finset ι) (W : Set X), I.Nonempty ∧ W ∈ 𝓝 x₀ ∧
      ∀ x ∈ W, (∀ j ∉ I, f j x < (⨆ i, f i x₀) / 4) ∧
        (⨆ i, f i x₀) / 2 < ⨆ i : I, f i x := by
  classical
  obtain ⟨i₀, hi₀⟩ := (hsum x₀).exists_pos (fun i ↦ hnn i x₀) zero_lt_one
  have : Nonempty ι := ⟨i₀⟩
  let m₀ : ℝ := ⨆ i, f i x₀
  have hm₀ : 0 < m₀ := hi₀.trans_le (le_ciSup (bddAbove_range_of_hasSum_one f hnn hsum x₀) i₀)
  obtain ⟨i₁, hi₁⟩ := exists_lt_of_lt_ciSup (half_lt_self hm₀)
  obtain ⟨I₀, hI₀⟩ :=
    Filter.mem_atTop_sets.mp ((hsum x₀) (Ioi_mem_nhds (by linarith : 1 - m₀ / 4 < 1)))
  let I : Finset ι := insert i₁ I₀
  have hcont_sup : Continuous fun x ↦ ⨆ i : I, f i.val x :=
    TauCeti.continuous_ciSup_of_finite fun i : I ↦ (f i.val).continuous
  have hcont_sum : Continuous fun x ↦ ∑ i ∈ I, f i x := by fun_prop
  refine ⟨I, {x | 1 - m₀ / 4 < ∑ i ∈ I, f i x} ∩ {x | m₀ / 2 < ⨆ i : I, f i.val x},
    Finset.insert_nonempty i₁ I₀,
    ((isOpen_lt continuous_const hcont_sum).inter (isOpen_lt continuous_const hcont_sup)).mem_nhds
      ⟨hI₀ I (Finset.subset_insert i₁ I₀),
       hi₁.trans_le (le_ciSup (finite_range fun i : I ↦ f i.val x₀).bddAbove
         ⟨i₁, Finset.mem_insert_self i₁ I₀⟩)⟩,
    fun x ⟨hx1, hx2⟩ ↦ ⟨fun j hj ↦ ?_, hx2⟩⟩
  have hle := sum_le_hasSum (insert j I) (fun k _ ↦ hnn k x) (hsum x)
  rw [Finset.sum_insert hj] at hle
  dsimp at hx1
  linarith

/-- For a family of continuous nonnegative functions summing pointwise to `1`, the pointwise
supremum `x ↦ ⨆ i, f i x` is continuous. -/
theorem continuous_ciSup_of_hasSum_one (f : ι → C(X, ℝ)) (hnn : ∀ i x, 0 ≤ f i x)
    (hsum : ∀ x, HasSum (fun i ↦ f i x) 1) :
    Continuous fun x ↦ ⨆ i, f i x := by
  refine TauCeti.continuous_ciSup_of_eventually_le (fun i ↦ (f i).continuous)
    (bddAbove_range_of_hasSum_one f hnn hsum) fun x₀ ↦ ?_
  obtain ⟨I, W, hIne, hW, h⟩ := eventually_tail_lt_and_half_lt_finSup_of_hasSum_one f hnn hsum x₀
  have hm₀ : 0 ≤ ⨆ i, f i x₀ := Real.iSup_nonneg fun i ↦ hnn i x₀
  exact ⟨I, hIne, eventually_of_mem hW fun x hx j hj ↦ by linarith [(h x hx).1 j hj, (h x hx).2]⟩

/-- For a family of continuous nonnegative functions summing pointwise to `1`, truncating below
half of their pointwise supremum `m` yields a locally finite family of supports. -/
theorem locallyFinite_support_halfThresholdTrunc_of_hasSum_one (f : ι → C(X, ℝ))
    (hnn : ∀ i x, 0 ≤ f i x) (hsum : ∀ x, HasSum (fun i ↦ f i x) 1)
    {m : C(X, ℝ)} (hm : ∀ x, m x = ⨆ i, f i x) :
    LocallyFinite fun i ↦ support (halfThresholdTrunc f m i) := fun x₀ ↦ by
  obtain ⟨I, W, -, hW, h⟩ := eventually_tail_lt_and_half_lt_finSup_of_hasSum_one f hnn hsum x₀
  refine ⟨W, hW, I.finite_toSet.subset fun j ⟨x, hx_supp, hxW⟩ ↦ ?_⟩
  rw [Finset.mem_coe]
  by_contra hj
  have hpos : m x / 2 < f j x := mem_support_halfThresholdTrunc_iff.mp hx_supp
  have hfin : ⨆ i : I, f i.val x ≤ m x := by
    rw [hm x]
    exact Real.iSup_le (fun i ↦ le_ciSup (bddAbove_range_of_hasSum_one f hnn hsum x) i.val)
      (Real.iSup_nonneg fun i ↦ hnn i x)
  linarith [(h x hxW).1 j hj, (h x hxW).2]

end HasSumOne

end TauCeti

namespace PartitionOfUnity

open TauCeti

section ShrinkOfThreshold

/-- Shrink a family of continuous weights `f` using a continuous function `m` (such as their
pointwise maximum) such that at every point some `f i x` exceeds `m x / 2` and the truncated
supports `support (TauCeti.halfThresholdTrunc f m i)` are locally finite. -/
noncomputable def shrinkOfThreshold (f : ι → C(X, ℝ)) (m : C(X, ℝ))
    (hlf : LocallyFinite fun i ↦ support (halfThresholdTrunc f m i))
    (hm_att : ∀ x, ∃ i, m x / 2 < f i x) : PartitionOfUnity ι X :=
  ofExistsPos (halfThresholdTrunc f m) hlf (halfThresholdTrunc_nonneg f m)
    fun x ↦ let ⟨i, hi⟩ := hm_att x; ⟨i, halfThresholdTrunc_pos_iff.mpr hi⟩

/-- Each weight of `PartitionOfUnity.shrinkOfThreshold` is the truncated excess
`max 0 (f i x - m x / 2)` divided by the finite sum of those truncated excesses. -/
theorem shrinkOfThreshold_apply (f : ι → C(X, ℝ)) (m : C(X, ℝ))
    (hlf : LocallyFinite fun i ↦ support (halfThresholdTrunc f m i))
    (hm_att : ∀ x, ∃ i, m x / 2 < f i x) (i : ι) (x : X) :
    shrinkOfThreshold f m hlf hm_att i x =
      max 0 (f i x - m x / 2) / ∑ᶠ k, max 0 (f k x - m x / 2) :=
  (rfl)

/-- A weight of `PartitionOfUnity.shrinkOfThreshold` is positive iff `m x / 2 < f i x`. -/
theorem shrinkOfThreshold_pos_iff {f : ι → C(X, ℝ)} {m : C(X, ℝ)}
    {hlf : LocallyFinite fun i ↦ support (halfThresholdTrunc f m i)}
    {hm_att : ∀ x, ∃ i, m x / 2 < f i x} {i : ι} {x : X} :
    0 < shrinkOfThreshold f m hlf hm_att i x ↔ m x / 2 < f i x := by
  rw [shrinkOfThreshold, ofExistsPos_pos_iff, halfThresholdTrunc_pos_iff]

/-- The open support of `shrinkOfThreshold f m hlf hm_att i` is `{x | m x / 2 < f i x}`. -/
theorem support_shrinkOfThreshold (f : ι → C(X, ℝ)) (m : C(X, ℝ))
    (hlf : LocallyFinite fun i ↦ support (halfThresholdTrunc f m i))
    (hm_att : ∀ x, ∃ i, m x / 2 < f i x) (i : ι) :
    support (shrinkOfThreshold f m hlf hm_att i) = {x | m x / 2 < f i x} := by
  rw [shrinkOfThreshold, support_ofExistsPos]
  ext x
  exact mem_support_halfThresholdTrunc_iff

/-- Every open support of `PartitionOfUnity.shrinkOfThreshold` lies in `support (f i)` when `m` is
positive everywhere. -/
theorem support_shrinkOfThreshold_subset {f : ι → C(X, ℝ)} {m : C(X, ℝ)}
    {hlf : LocallyFinite fun i ↦ support (halfThresholdTrunc f m i)}
    (hm_pos : ∀ x, 0 < m x) {hm_att : ∀ x, ∃ i, m x / 2 < f i x} (i : ι) :
    support (shrinkOfThreshold f m hlf hm_att i) ⊆ support (f i) :=
  (support_ofExistsPos _ _ _ _ i).subset.trans (support_halfThresholdTrunc_subset hm_pos i)

/-- Every closed support of `PartitionOfUnity.shrinkOfThreshold` lies in `support (f i)` when `m` is
continuous and positive everywhere. -/
theorem tsupport_shrinkOfThreshold_subset_support {f : ι → C(X, ℝ)} {m : C(X, ℝ)}
    {hlf : LocallyFinite fun i ↦ support (halfThresholdTrunc f m i)}
    (hm_pos : ∀ x, 0 < m x) {hm_att : ∀ x, ∃ i, m x / 2 < f i x} (i : ι) :
    tsupport (shrinkOfThreshold f m hlf hm_att i) ⊆ support (f i) :=
  (tsupport_ofExistsPos _ _ _ _ i).subset.trans (tsupport_halfThresholdTrunc_subset hm_pos i)

/-- If every open support `support (f i)` lies in `U i` and `m` is continuous and positive
everywhere, then `PartitionOfUnity.shrinkOfThreshold` is subordinate to `U`. -/
theorem isSubordinate_shrinkOfThreshold {f : ι → C(X, ℝ)} {m : C(X, ℝ)}
    {hlf : LocallyFinite fun i ↦ support (halfThresholdTrunc f m i)}
    (hm_pos : ∀ x, 0 < m x) {hm_att : ∀ x, ∃ i, m x / 2 < f i x}
    {U : ι → Set X} (hU : ∀ i, support (f i) ⊆ U i) :
    (shrinkOfThreshold f m hlf hm_att).IsSubordinate U :=
  fun i ↦ (tsupport_shrinkOfThreshold_subset_support hm_pos i).trans (hU i)

end ShrinkOfThreshold

section Shrink

private noncomputable def maxWeight (ρ : PartitionOfUnity ι X) (x : X) : ℝ :=
  ⨆ i : ι, ρ i x

private theorem bddAbove_range_apply (ρ : PartitionOfUnity ι X) (x : X) :
    BddAbove (range fun i ↦ ρ i x) :=
  ⟨1, forall_mem_range.2 fun i ↦ ρ.le_one i x⟩

private theorem le_maxWeight (ρ : PartitionOfUnity ι X) (i : ι) (x : X) :
    ρ i x ≤ maxWeight ρ x :=
  le_ciSup (bddAbove_range_apply ρ x) i

private theorem continuous_maxWeight (ρ : PartitionOfUnity ι X) :
    Continuous (maxWeight ρ) :=
  continuous_ciSup_of_hasSum_one (ρ ·) ρ.nonneg fun x ↦ by
    have hsum : ∑ i ∈ ρ.finsupport x, ρ i x = 1 := by
      rw [← ρ.sum_eq_one (mem_univ x),
        finsum_eq_sum_of_support_subset _ (ρ.coe_finsupport x).superset]
    exact hsum ▸ hasSum_sum_of_ne_finset_zero fun i hi ↦ not_not.mp fun h0 ↦
      hi ((ρ.coe_finsupport x).symm.subset h0)

private noncomputable def maxWeightCont (ρ : PartitionOfUnity ι X) : C(X, ℝ) :=
  ⟨maxWeight ρ, continuous_maxWeight ρ⟩

private theorem maxWeight_pos (ρ : PartitionOfUnity ι X) (x : X) :
    0 < maxWeight ρ x :=
  let ⟨i₀, hi₀⟩ := ρ.exists_pos (mem_univ x)
  hi₀.trans_le (le_maxWeight ρ i₀ x)

private theorem exists_half_maxWeight_lt (ρ : PartitionOfUnity ι X) (x : X) :
    ∃ i, maxWeight ρ x / 2 < ρ i x :=
  let ⟨i₀, hi₀⟩ := ρ.exists_pos (mem_univ x)
  haveI : Nonempty ι := ⟨i₀⟩
  exists_lt_of_lt_ciSup (half_lt_self (hi₀.trans_le (le_maxWeight ρ i₀ x)))

/-- Shrink a partition of unity `ρ` on `X` by truncating each weight below half of the pointwise
maximum weight and renormalizing, so that every closed support lies in the corresponding open
support of `ρ`. -/
noncomputable def shrink (ρ : PartitionOfUnity ι X) : PartitionOfUnity ι X :=
  shrinkOfThreshold (ρ ·) (maxWeightCont ρ)
    (ρ.locallyFinite.subset (support_halfThresholdTrunc_subset (maxWeight_pos ρ)))
    (exists_half_maxWeight_lt ρ)

/-- Each weight of `ρ.shrink` is the truncated excess `max 0 (ρ i x - (⨆ j, ρ j x) / 2)` divided
by the finite sum of those truncated excesses. -/
theorem shrink_apply (ρ : PartitionOfUnity ι X) (i : ι) (x : X) :
    ρ.shrink i x =
      max 0 (ρ i x - (⨆ j, ρ j x) / 2) / ∑ᶠ k, max 0 (ρ k x - (⨆ j, ρ j x) / 2) :=
  (rfl)

/-- A shrunken weight `ρ.shrink i x` is positive if and only if `ρ i x` strictly exceeds half of
the pointwise supremum `⨆ j, ρ j x`. -/
theorem shrink_pos_iff {ρ : PartitionOfUnity ι X} {i : ι} {x : X} :
    0 < ρ.shrink i x ↔ (⨆ j, ρ j x) / 2 < ρ i x :=
  shrinkOfThreshold_pos_iff

/-- The open support of `ρ.shrink i` is the set of points where `ρ i` strictly exceeds half of the
pointwise supremum `⨆ j, ρ j x`. -/
theorem support_shrink (ρ : PartitionOfUnity ι X) (i : ι) :
    support (ρ.shrink i) = {x | (⨆ j, ρ j x) / 2 < ρ i x} :=
  support_shrinkOfThreshold (ρ ·) (maxWeightCont ρ) _ _ i

/-- Every open support of `ρ.shrink` is contained in the open support of `ρ`. -/
theorem support_shrink_subset (ρ : PartitionOfUnity ι X) (i : ι) :
    support (ρ.shrink i) ⊆ support (ρ i) :=
  support_shrinkOfThreshold_subset (maxWeight_pos ρ) i

/-- Every closed support of `ρ.shrink` is contained in the open support of `ρ`. -/
theorem tsupport_shrink_subset_support (ρ : PartitionOfUnity ι X) (i : ι) :
    tsupport (ρ.shrink i) ⊆ support (ρ i) :=
  tsupport_shrinkOfThreshold_subset_support (maxWeight_pos ρ) i

/-- If every open support `support (ρ i)` lies in `U i`, then `ρ.shrink` is subordinate to `U` in
the closed-support sense. -/
theorem isSubordinate_shrink {ρ : PartitionOfUnity ι X} {U : ι → Set X}
    (hU : ∀ i, support (ρ i) ⊆ U i) :
    ρ.shrink.IsSubordinate U :=
  isSubordinate_shrinkOfThreshold (maxWeight_pos ρ) hU

end Shrink

end PartitionOfUnity
