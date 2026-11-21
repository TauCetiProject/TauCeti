/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.PartitionOfUnity
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
* `PartitionOfUnity.halfMaxTrunc` and `PartitionOfUnity.shrinkOfMax`: truncate a family of
  continuous weights below half of a continuous positive function `m` (such as their pointwise
  maximum) and normalize when the truncated supports are locally finite.
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

namespace PartitionOfUnity

variable {ι X : Type*} [TopologicalSpace X]

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

section ShrinkOfMax

/-- Truncate a continuous weight `f i` below half of `m`: `x ↦ max 0 (f i x - m x / 2)`. -/
noncomputable def halfMaxTrunc (f : ι → C(X, ℝ)) (m : C(X, ℝ)) (i : ι) : C(X, ℝ) :=
  ⟨fun x ↦ max 0 (f i x - m x / 2),
    continuous_const.max ((f i).continuous.sub (m.continuous.div_const 2))⟩

/-- Pointwise formula for `PartitionOfUnity.halfMaxTrunc`. -/
@[simp]
theorem halfMaxTrunc_apply (f : ι → C(X, ℝ)) (m : C(X, ℝ)) (i : ι) (x : X) :
    halfMaxTrunc f m i x = max 0 (f i x - m x / 2) :=
  (rfl)

/-- Each truncated weight `PartitionOfUnity.halfMaxTrunc` is nonnegative. -/
theorem halfMaxTrunc_nonneg (f : ι → C(X, ℝ)) (m : C(X, ℝ)) (i : ι) (x : X) :
    0 ≤ halfMaxTrunc f m i x :=
  le_max_left _ _

/-- A truncated weight `PartitionOfUnity.halfMaxTrunc f m i x` is positive iff `m x / 2 < f i x`. -/
theorem halfMaxTrunc_pos_iff {f : ι → C(X, ℝ)} {m : C(X, ℝ)} {i : ι} {x : X} :
    0 < halfMaxTrunc f m i x ↔ m x / 2 < f i x := by
  rw [halfMaxTrunc_apply, lt_max_iff, or_iff_right (lt_irrefl 0), sub_pos]

/-- When `m` is positive everywhere, the open support of `halfMaxTrunc f m i` lies in
`support (f i)`. -/
theorem support_halfMaxTrunc_subset {f : ι → C(X, ℝ)} {m : C(X, ℝ)} (hm : ∀ x, 0 < m x) (i : ι) :
    support (halfMaxTrunc f m i) ⊆ support (f i) := by
  intro x hx
  have hpos : m x / 2 < f i x :=
    halfMaxTrunc_pos_iff.mp (lt_of_le_of_ne (halfMaxTrunc_nonneg f m i x) (Ne.symm hx))
  exact ((half_pos (hm x)).trans hpos).ne'

/-- When `m` is continuous and positive everywhere, the closed support of `halfMaxTrunc f m i`
lies in the open support `support (f i)`. -/
theorem tsupport_halfMaxTrunc_subset {f : ι → C(X, ℝ)} {m : C(X, ℝ)} (hm : ∀ x, 0 < m x) (i : ι) :
    tsupport (halfMaxTrunc f m i) ⊆ support (f i) := by
  intro x hx
  have hclosed : IsClosed {y : X | m y / 2 ≤ f i y} :=
    isClosed_le (m.continuous.div_const 2) (f i).continuous
  have hle : m x / 2 ≤ f i x := by
    refine closure_minimal (fun y hy ↦ ?_) hclosed hx
    rw [mem_ofPred_eq]
    exact (halfMaxTrunc_pos_iff.mp
      (lt_of_le_of_ne (halfMaxTrunc_nonneg f m i y) (Ne.symm hy))).le
  exact ((half_pos (hm x)).trans_le hle).ne'

/-- Shrink a family of continuous weights `f` using a continuous function `m` (such as their
pointwise maximum) such that at every point some `f i x` exceeds `m x / 2` and the truncated
supports `support (halfMaxTrunc f m i)` are locally finite. -/
noncomputable def shrinkOfMax (f : ι → C(X, ℝ)) (m : C(X, ℝ))
    (hlf : LocallyFinite fun i ↦ support (halfMaxTrunc f m i))
    (hm_att : ∀ x, ∃ i, m x / 2 < f i x) : PartitionOfUnity ι X :=
  ofExistsPos (halfMaxTrunc f m) hlf (halfMaxTrunc_nonneg f m)
    fun x ↦ let ⟨i, hi⟩ := hm_att x; ⟨i, halfMaxTrunc_pos_iff.mpr hi⟩

/-- Each weight of `PartitionOfUnity.shrinkOfMax` is the truncated excess
`max 0 (f i x - m x / 2)` divided by the finite sum of those truncated excesses. -/
theorem shrinkOfMax_apply (f : ι → C(X, ℝ)) (m : C(X, ℝ))
    (hlf : LocallyFinite fun i ↦ support (halfMaxTrunc f m i))
    (hm_att : ∀ x, ∃ i, m x / 2 < f i x) (i : ι) (x : X) :
    shrinkOfMax f m hlf hm_att i x =
      max 0 (f i x - m x / 2) / ∑ᶠ k, max 0 (f k x - m x / 2) :=
  (rfl)

/-- A weight of `PartitionOfUnity.shrinkOfMax` is positive iff `m x / 2 < f i x`. -/
theorem shrinkOfMax_pos_iff {f : ι → C(X, ℝ)} {m : C(X, ℝ)}
    {hlf : LocallyFinite fun i ↦ support (halfMaxTrunc f m i)}
    {hm_att : ∀ x, ∃ i, m x / 2 < f i x} {i : ι} {x : X} :
    0 < shrinkOfMax f m hlf hm_att i x ↔ m x / 2 < f i x := by
  rw [shrinkOfMax, ofExistsPos_pos_iff, halfMaxTrunc_pos_iff]

/-- The open support of `shrinkOfMax f m hlf hm_att i` is `{x | m x / 2 < f i x}`. -/
theorem support_shrinkOfMax (f : ι → C(X, ℝ)) (m : C(X, ℝ))
    (hlf : LocallyFinite fun i ↦ support (halfMaxTrunc f m i))
    (hm_att : ∀ x, ∃ i, m x / 2 < f i x) (i : ι) :
    support (shrinkOfMax f m hlf hm_att i) = {x | m x / 2 < f i x} := by
  ext x
  exact ((shrinkOfMax f m hlf hm_att).nonneg i x).lt_iff_ne'.symm.trans shrinkOfMax_pos_iff

/-- Every open support of `PartitionOfUnity.shrinkOfMax` lies in `support (f i)` when `m` is
positive everywhere. -/
theorem support_shrinkOfMax_subset {f : ι → C(X, ℝ)} {m : C(X, ℝ)}
    {hlf : LocallyFinite fun i ↦ support (halfMaxTrunc f m i)}
    (hm_pos : ∀ x, 0 < m x) {hm_att : ∀ x, ∃ i, m x / 2 < f i x} (i : ι) :
    support (shrinkOfMax f m hlf hm_att i) ⊆ support (f i) :=
  (support_ofExistsPos _ _ _ _ i).subset.trans (support_halfMaxTrunc_subset hm_pos i)

/-- Every closed support of `PartitionOfUnity.shrinkOfMax` lies in `support (f i)` when `m` is
continuous and positive everywhere. -/
theorem tsupport_shrinkOfMax_subset_support {f : ι → C(X, ℝ)} {m : C(X, ℝ)}
    {hlf : LocallyFinite fun i ↦ support (halfMaxTrunc f m i)}
    (hm_pos : ∀ x, 0 < m x) {hm_att : ∀ x, ∃ i, m x / 2 < f i x} (i : ι) :
    tsupport (shrinkOfMax f m hlf hm_att i) ⊆ support (f i) :=
  (tsupport_ofExistsPos _ _ _ _ i).subset.trans (tsupport_halfMaxTrunc_subset hm_pos i)

/-- If every open support `support (f i)` lies in `U i` and `m` is continuous and positive
everywhere, then `PartitionOfUnity.shrinkOfMax` is subordinate to `U`. -/
theorem isSubordinate_shrinkOfMax {f : ι → C(X, ℝ)} {m : C(X, ℝ)}
    {hlf : LocallyFinite fun i ↦ support (halfMaxTrunc f m i)}
    (hm_pos : ∀ x, 0 < m x) {hm_att : ∀ x, ∃ i, m x / 2 < f i x}
    {U : ι → Set X} (hU : ∀ i, support (f i) ⊆ U i) :
    (shrinkOfMax f m hlf hm_att).IsSubordinate U :=
  fun i ↦ (tsupport_shrinkOfMax_subset_support hm_pos i).trans (hU i)

end ShrinkOfMax

section Shrink

private noncomputable def maxWeight (ρ : PartitionOfUnity ι X) (x : X) : ℝ :=
  ⨆ i : ι, ρ i x

private theorem bddAbove_range_apply (ρ : PartitionOfUnity ι X) (x : X) :
    BddAbove (range fun i ↦ ρ i x) :=
  ⟨1, forall_mem_range.2 fun i ↦ ρ.le_one i x⟩

private theorem maxWeight_nonneg (ρ : PartitionOfUnity ι X) (x : X) :
    0 ≤ maxWeight ρ x :=
  Real.iSup_nonneg fun i ↦ ρ.nonneg i x

private theorem le_maxWeight (ρ : PartitionOfUnity ι X) (i : ι) (x : X) :
    ρ i x ≤ maxWeight ρ x :=
  le_ciSup (bddAbove_range_apply ρ x) i

private theorem maxWeight_eq_of_support_subset {ρ : PartitionOfUnity ι X} {I : Finset ι} {x : X}
    (hI : support (ρ · x) ⊆ I) :
    maxWeight ρ x = ⨆ i : I, ρ i x := by
  have hnonneg : 0 ≤ ⨆ i : I, ρ i x := Real.iSup_nonneg fun i ↦ ρ.nonneg i x
  refine le_antisymm (Real.iSup_le (fun i ↦ ?_) hnonneg)
    (Real.iSup_le (fun i : I ↦ le_maxWeight ρ i.1 x) (maxWeight_nonneg ρ x))
  by_cases hi : i ∈ I
  · exact le_ciSup (finite_range (fun j : I ↦ ρ j x)).bddAbove ⟨i, hi⟩
  · have h0 : ρ i x = 0 := by_contra fun hne ↦ hi (hI hne)
    exact h0.le.trans hnonneg

private theorem continuous_maxWeight (ρ : PartitionOfUnity ι X) :
    Continuous (maxWeight ρ) := by
  classical
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  obtain ⟨I, hI⟩ := ρ.locallyFinite.exists_finset_support x₀
  exact (TauCeti.continuous_ciSup_of_finite fun i : I ↦ (ρ i).continuous).continuousAt.congr
    (hI.mono fun x hx ↦ (maxWeight_eq_of_support_subset hx).symm)

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
  shrinkOfMax (ρ ·) (maxWeightCont ρ)
    (ρ.locallyFinite.subset (support_halfMaxTrunc_subset (maxWeight_pos ρ)))
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
  shrinkOfMax_pos_iff

/-- The open support of `ρ.shrink i` is the set of points where `ρ i` strictly exceeds half of the
pointwise supremum `⨆ j, ρ j x`. -/
theorem support_shrink (ρ : PartitionOfUnity ι X) (i : ι) :
    support (ρ.shrink i) = {x | (⨆ j, ρ j x) / 2 < ρ i x} :=
  support_shrinkOfMax (ρ ·) (maxWeightCont ρ) _ _ i

/-- Every open support of `ρ.shrink` is contained in the open support of `ρ`. -/
theorem support_shrink_subset (ρ : PartitionOfUnity ι X) (i : ι) :
    support (ρ.shrink i) ⊆ support (ρ i) :=
  support_shrinkOfMax_subset (maxWeight_pos ρ) i

/-- Every closed support of `ρ.shrink` is contained in the open support of `ρ`. -/
theorem tsupport_shrink_subset_support (ρ : PartitionOfUnity ι X) (i : ι) :
    tsupport (ρ.shrink i) ⊆ support (ρ i) :=
  tsupport_shrinkOfMax_subset_support (maxWeight_pos ρ) i

/-- If every open support `support (ρ i)` lies in `U i`, then `ρ.shrink` is subordinate to `U` in
the closed-support sense. -/
theorem isSubordinate_shrink {ρ : PartitionOfUnity ι X} {U : ι → Set X}
    (hU : ∀ i, support (ρ i) ⊆ U i) :
    ρ.shrink.IsSubordinate U :=
  isSubordinate_shrinkOfMax (maxWeight_pos ρ) hU

end Shrink

end PartitionOfUnity
