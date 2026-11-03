/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.PartitionOfUnity
import TauCeti.Topology.Order.Lattice

/-!
# Finite-subset gaps of a partition of unity and their countable recolouring

Let `ρ` be a partition of unity with weights `(ρ i)_{i ∈ ι}`, where `ι` may be uncountable. For a
finite set `E` of indices, the *gap* of `E` at `x` is
`ρ.gap E x = max 0 (min_{i ∈ E} ρ i x - sup_{i ∉ E} ρ i x)`,
with the supremum of an empty family read as `0`; the gap of `∅` is `0`.

A positive gap at `x` means that `E` is a strict top segment of the weights at `x`: every weight
in `E` is positive and strictly exceeds every weight outside `E`. Consequently the sets with a
positive gap at a point form a chain, so at most one of them has any prescribed cardinality.
Informally, if the positive weights at `x` are listed with multiplicity as `a₁ ≥ ⋯ ≥ aₘ > 0` and
`aₘ₊₁ = 0`, the set of the first `n` indices has gap `aₙ - aₙ₊₁`, and ties give gap zero. The
basic identity is that the gaps of the sets containing a fixed index `j` add up to `ρ j x`;
summing over `j` gives `∑ᶠ E, #E * ρ.gap E x = ∑ᶠ i, ρ i x`.

Each gap is continuous: near any point only finitely many weights are nonzero, and there the gap
is a finite expression in continuous functions. Grouping the gaps by cardinality, the functions
`n * ∑ᶠ_{#E = n} ρ.gap E` form a partition of unity indexed by `ℕ`, on the same set as `ρ`. Thus
any partition of unity, indexed by an arbitrary type, gives a countable one, and wherever the
`n`-th new weight is positive it is carried by a single set `E` of size `n` all of whose original
weights are positive. When `ρ` is subordinate to a cover `U`, this means that `x ∈ U i` for all
`i ∈ E`.

This is the countable colouring used to build classifying maps of numerable bundles into
Grassmannians of `ℕ →₀ 𝕜`: on the region where a set `E` of size `n` has positive gap, a chart
of any index in `E` provides a local frame, and the `n`-th colour weights these frames. The
positivity sets of the gaps are the open sets used in the proof of Lemma 5.9 of Milnor–Stasheff,
*Characteristic classes*, to refine a locally finite trivializing cover to a countable one.

## Main definitions and results

* `PartitionOfUnity.gap`: the gap of a finite set of indices.
* `PartitionOfUnity.continuous_gap`: each gap is continuous.
* `PartitionOfUnity.gap_pos_iff`: `E` has positive gap exactly when it is a nonempty strict top
  segment of positive weights.
* `PartitionOfUnity.eq_of_gap_pos_of_card_eq`: two sets of equal size with positive gaps at the
  same point coincide.
* `PartitionOfUnity.finsum_mem_gap`: the gaps of the sets containing `j` sum to `ρ j x`.
* `PartitionOfUnity.finsum_card_mul_gap`: `∑ᶠ E, #E * ρ.gap E x = ∑ᶠ i, ρ i x`.
* `PartitionOfUnity.gapPartition`: the partition of unity indexed by `ℕ` grouping gaps by size.
* `PartitionOfUnity.gapPartition_card_eq`: where `E` has positive gap, the colour of size `#E`
  is `#E * ρ.gap E x`.
-/

public section

open Function Set Filter Topology

namespace PartitionOfUnity

variable {ι X : Type*} [TopologicalSpace X] {s : Set X} (ρ : PartitionOfUnity ι X s)

/-- The gap of a finite set `E` of indices of a partition of unity at `x`: the excess of the
smallest weight in `E` over the largest weight outside `E`, truncated below at `0`. The supremum
over an empty complement is `0`, and the gap of `∅` is `0`. -/
noncomputable def gap (E : Finset ι) (x : X) : ℝ :=
  max 0 ((⨅ i : E, ρ i x) - ⨆ i : {i // i ∉ E}, ρ i x)

/-- The defining equation of `PartitionOfUnity.gap`. -/
theorem gap_def (E : Finset ι) (x : X) :
    ρ.gap E x = max 0 ((⨅ i : E, ρ i x) - ⨆ i : {i // i ∉ E}, ρ i x) :=
  (rfl)

/-- Gaps are nonnegative. -/
theorem gap_nonneg (E : Finset ι) (x : X) : 0 ≤ ρ.gap E x :=
  le_max_left _ _

variable {ρ}

/-! ### Elementary bounds on the infimum and the supremum -/

private theorem bddAbove_range_compl (E : Finset ι) (x : X) :
    BddAbove (range fun i : {i // i ∉ E} ↦ ρ i x) :=
  ⟨1, forall_mem_range.2 fun i ↦ ρ.le_one i x⟩

private theorem iSup_compl_nonneg (E : Finset ι) (x : X) :
    0 ≤ ⨆ i : {i // i ∉ E}, ρ i x :=
  Real.iSup_nonneg fun i ↦ ρ.nonneg i x

private theorem le_iSup_compl {E : Finset ι} {j : ι} (hj : j ∉ E) (x : X) :
    ρ j x ≤ ⨆ i : {i // i ∉ E}, ρ i x :=
  le_ciSup (f := fun i : {i // i ∉ E} ↦ ρ i x) (bddAbove_range_compl E x) ⟨j, hj⟩

private theorem iInf_le_of_mem {E : Finset ι} {j : ι} (hj : j ∈ E) (x : X) :
    ⨅ i : E, ρ i x ≤ ρ j x :=
  ciInf_le (f := fun i : E ↦ ρ i x) (finite_range _).bddBelow ⟨j, hj⟩

private theorem iInf_eq_of_mem {E : Finset ι} {j : ι} {x : X} (hj : j ∈ E)
    (h : ∀ i ∈ E, ρ j x ≤ ρ i x) : ⨅ i : E, ρ i x = ρ j x :=
  have : Nonempty E := ⟨⟨j, hj⟩⟩
  le_antisymm (iInf_le_of_mem hj x) (le_ciInf fun i ↦ h i i.2)

private theorem iSup_compl_eq_of_notMem {E : Finset ι} {k : ι} {x : X} (hk : k ∉ E)
    (h : ∀ i ∉ E, ρ i x ≤ ρ k x) : ⨆ i : {i // i ∉ E}, ρ i x = ρ k x :=
  have : Nonempty {i // i ∉ E} := ⟨⟨k, hk⟩⟩
  le_antisymm (ciSup_le fun i ↦ h i i.2) (le_iSup_compl hk x)

private theorem iSup_compl_eq_zero {E : Finset ι} {x : X} (h : ∀ i ∉ E, ρ i x = 0) :
    ⨆ i : {i // i ∉ E}, ρ i x = 0 :=
  le_antisymm (Real.iSup_le (fun i ↦ (h i i.2).le) le_rfl) (iSup_compl_nonneg E x)

/-- Where all weights outside a finite set `I` vanish, the supremum over the complement of `E`
is the supremum over the finite set `I \ E`. -/
private theorem iSup_compl_eq_iSup_sdiff [DecidableEq ι] {I E : Finset ι} {x : X}
    (hI : support (ρ · x) ⊆ I) :
    ⨆ i : {i // i ∉ E}, ρ i x = ⨆ i : (I \ E : Finset ι), ρ i x := by
  have hnonneg : 0 ≤ ⨆ i : (I \ E : Finset ι), ρ i x := Real.iSup_nonneg fun i ↦ ρ.nonneg i x
  refine le_antisymm (Real.iSup_le (fun i ↦ ?_) hnonneg)
    (Real.iSup_le (fun i ↦ le_iSup_compl (Finset.mem_sdiff.1 i.2).2 x) (iSup_compl_nonneg E x))
  by_cases hi : i.1 ∈ I
  · exact le_ciSup (f := fun i : (I \ E : Finset ι) ↦ ρ i x) (finite_range _).bddAbove
      ⟨i, Finset.mem_sdiff.2 ⟨hi, i.2⟩⟩
  · rw [show ρ i x = 0 from notMem_support.1 fun h ↦ hi (hI h)]
    exact hnonneg

/-! ### Positive gaps -/

private theorem iSup_lt_iInf_of_gap_pos {E : Finset ι} {x : X} (h : 0 < ρ.gap E x) :
    ⨆ i : {i // i ∉ E}, ρ i x < ⨅ i : E, ρ i x := by
  rw [gap, lt_max_iff] at h
  exact sub_pos.1 (h.resolve_left (lt_irrefl 0))

/-- If `E` has positive gap at `x`, every weight in `E` strictly exceeds every weight outside
`E`. -/
theorem lt_of_gap_pos {E : Finset ι} {x : X} (h : 0 < ρ.gap E x) {i j : ι} (hi : i ∈ E)
    (hj : j ∉ E) : ρ j x < ρ i x :=
  (le_iSup_compl hj x).trans_lt <| (iSup_lt_iInf_of_gap_pos h).trans_le (iInf_le_of_mem hi x)

/-- If `E` has positive gap at `x`, every weight in `E` is positive at `x`. -/
theorem pos_of_gap_pos {E : Finset ι} {x : X} (h : 0 < ρ.gap E x) {i : ι} (hi : i ∈ E) :
    0 < ρ i x :=
  (iSup_compl_nonneg E x).trans_lt <| (iSup_lt_iInf_of_gap_pos h).trans_le (iInf_le_of_mem hi x)

/-- A set with positive gap at `x` consists of indices whose weights are nonzero at `x`. -/
theorem subset_finsupport_of_gap_pos {E : Finset ι} {x : X} (h : 0 < ρ.gap E x) :
    E ⊆ ρ.finsupport x := fun _ hi ↦
  (ρ.mem_finsupport x).2 (pos_of_gap_pos h hi).ne'

/-- Gaps are nonnegative, so a gap is positive exactly when it is nonzero. -/
theorem gap_pos_iff_ne_zero {E : Finset ι} {x : X} : 0 < ρ.gap E x ↔ ρ.gap E x ≠ 0 :=
  (ρ.gap_nonneg E x).lt_iff_ne'

/-- A set with positive gap at `x` contains every index whose weight at `x` is at least the
weight of one of its members. -/
theorem mem_of_gap_pos_of_le {E : Finset ι} {x : X} (h : 0 < ρ.gap E x) {i j : ι} (hj : j ∈ E)
    (hji : ρ j x ≤ ρ i x) : i ∈ E := by
  by_contra hi
  exact (lt_of_gap_pos h hj hi).not_ge hji

@[simp]
theorem gap_empty (x : X) : ρ.gap ∅ x = 0 := by
  rw [gap, Real.iInf_of_isEmpty, zero_sub, max_eq_left (neg_nonpos.2 (iSup_compl_nonneg _ x))]

/-- A finite set has positive gap at `x` exactly when it is nonempty, its weights at `x` are
positive, and they strictly exceed every weight outside it. -/
theorem gap_pos_iff {E : Finset ι} {x : X} :
    0 < ρ.gap E x ↔ E.Nonempty ∧ (∀ i ∈ E, 0 < ρ i x) ∧ ∀ i ∈ E, ∀ j ∉ E, ρ j x < ρ i x := by
  classical
  refine ⟨fun h ↦ ⟨Finset.nonempty_iff_ne_empty.2 ?_, fun i hi ↦ pos_of_gap_pos h hi,
    fun i hi j hj ↦ lt_of_gap_pos h hi hj⟩, fun ⟨hne, hpos, hlt⟩ ↦ ?_⟩
  · rintro rfl
    exact h.ne' (gap_empty x)
  have : Nonempty E := hne.to_subtype
  obtain ⟨⟨i, hi⟩, hmin⟩ := exists_eq_ciInf_of_finite (f := fun i : E ↦ ρ i x)
  rw [gap, lt_max_iff, sub_pos, ← hmin, iSup_compl_eq_iSup_sdiff (ρ.coe_finsupport x).superset]
  refine Or.inr ?_
  rcases isEmpty_or_nonempty (ρ.finsupport x \ E : Finset ι) with h | h
  · rw [Real.iSup_of_isEmpty]
    exact hpos i hi
  · obtain ⟨⟨k, hk⟩, hmax⟩ :=
      exists_eq_ciSup_of_finite (f := fun k : (ρ.finsupport x \ E : Finset ι) ↦ ρ k x)
    rw [← hmax]
    exact hlt i hi k (Finset.mem_sdiff.1 hk).2

/-- Sets with positive gaps at the same point are nested. -/
theorem subset_or_subset_of_gap_pos {E F : Finset ι} {x : X} (hE : 0 < ρ.gap E x)
    (hF : 0 < ρ.gap F x) : E ⊆ F ∨ F ⊆ E := by
  by_contra! h
  obtain ⟨⟨i, hiE, hiF⟩, ⟨j, hjF, hjE⟩⟩ :=
    And.intro (Finset.not_subset.1 h.1) (Finset.not_subset.1 h.2)
  exact lt_asymm (lt_of_gap_pos hE hiE hjE) (lt_of_gap_pos hF hjF hiF)

/-- At each point, at most one set of each cardinality has positive gap. -/
theorem eq_of_gap_pos_of_card_eq {E F : Finset ι} {x : X} (hE : 0 < ρ.gap E x)
    (hF : 0 < ρ.gap F x) (hcard : E.card = F.card) : E = F := by
  rcases subset_or_subset_of_gap_pos hE hF with h | h
  · exact Finset.eq_of_subset_of_card_le h hcard.ge
  · exact (Finset.eq_of_subset_of_card_le h hcard.le).symm

/-- If `ρ` is subordinate to `U` and `E` has positive gap at `x`, then `x` lies in `U i` for
every `i ∈ E`. -/
theorem IsSubordinate.mem_of_gap_pos {U : ι → Set X} (hU : ρ.IsSubordinate U) {E : Finset ι}
    {x : X} (h : 0 < ρ.gap E x) {i : ι} (hi : i ∈ E) : x ∈ U i :=
  hU i <| subset_tsupport _ (pos_of_gap_pos h hi).ne'

/-! ### Continuity -/

/-- Near a point where all weights outside `I` vanish, the gap is a finite expression in the
weights indexed by `I`. -/
private theorem gap_eq_of_support_subset [DecidableEq ι] {I : Finset ι} (E : Finset ι) {x : X}
    (hI : support (ρ · x) ⊆ I) :
    ρ.gap E x = max 0 ((⨅ i : E, ρ i x) - ⨆ i : (I \ E : Finset ι), ρ i x) := by
  rw [gap, iSup_compl_eq_iSup_sdiff hI]

/-- Each gap of a partition of unity is continuous. -/
theorem continuous_gap (E : Finset ι) : Continuous (ρ.gap E) := by
  classical
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  obtain ⟨I, hI⟩ := ρ.locallyFinite.exists_finset_support x₀
  have hcont : Continuous fun x ↦ max 0 ((⨅ i : E, ρ i x) - ⨆ i : (I \ E : Finset ι), ρ i x) :=
    continuous_const.max <|
      (TauCeti.continuous_ciInf_of_finite fun i : E ↦ (ρ i).continuous).sub
        (TauCeti.continuous_ciSup_of_finite fun i : (I \ E : Finset ι) ↦ (ρ i).continuous)
  exact hcont.continuousAt.congr (hI.mono fun x hx ↦ (gap_eq_of_support_subset E hx).symm)

/-! ### The gap identities -/

/-- Pointwise, the gap is supported on subsets of a finite set `I` carrying all nonzero weights. -/
private theorem support_gap_subset {I : Finset ι} {x : X}
    (hI : support (ρ · x) ⊆ I) : support (ρ.gap · x) ⊆ I.powerset := fun _ hE ↦
  Finset.mem_coe.2 <| Finset.mem_powerset.2 fun _ hi ↦
    hI <| (pos_of_gap_pos (gap_pos_iff_ne_zero.2 hE) hi).ne'

/-- At each point only finitely many sets have nonzero gap. -/
theorem finite_support_gap (x : X) : (support (ρ.gap · x)).Finite := by
  classical
  exact (ρ.finsupport x).powerset.finite_toSet.subset
    (support_gap_subset (ρ.coe_finsupport x).superset)

/-! The identity `finsum_mem_gap` is proved on the finite support `T` of the weights at `x`, by
strong induction on the number of weights in `T` strictly below `ρ j x`. If there are none, only
`T` itself contributes. Otherwise, if `k` carries the largest weight below `ρ j x`, the sets
containing `j` with positive gap are the up-set of `j`, with gap `ρ j x - ρ k x`, and the sets
containing `k` with positive gap. -/

private theorem notMem_finsupport_iff {x : X} {i : ι} : i ∉ ρ.finsupport x ↔ ρ i x = 0 := by
  simp

/-- The base case: if `ρ j x` is the smallest nonzero weight, only the full support contributes. -/
private theorem sum_gap_filter_mem_of_forall_le [DecidableEq ι] {x : X} {j : ι}
    (hj : j ∈ ρ.finsupport x) (hmin : ∀ i ∈ ρ.finsupport x, ρ j x ≤ ρ i x) :
    ∑ E ∈ (ρ.finsupport x).powerset.filter (j ∈ ·), ρ.gap E x = ρ j x := by
  set T := ρ.finsupport x
  have hTmem : T ∈ T.powerset.filter (j ∈ ·) :=
    Finset.mem_filter.2 ⟨Finset.mem_powerset_self T, hj⟩
  have hgap : ρ.gap T x = ρ j x := by
    rw [gap, iInf_eq_of_mem hj hmin, iSup_compl_eq_zero fun i hi ↦ notMem_finsupport_iff.1 hi,
      sub_zero, max_eq_right (ρ.nonneg j x)]
  rw [Finset.sum_eq_single_of_mem T hTmem fun E hE hET ↦ ?_, hgap]
  obtain ⟨hET', hjE⟩ := Finset.mem_filter.1 hE
  by_contra hne
  exact hET (Finset.Subset.antisymm (Finset.mem_powerset.1 hET') fun i hi ↦
    mem_of_gap_pos_of_le (gap_pos_iff_ne_zero.2 hne) hjE (hmin i hi))

/-- The inductive step: if `k` carries the largest nonzero weight strictly below `ρ j x`, the sum
for `j` exceeds the sum for `k` by `ρ j x - ρ k x`. -/
private theorem sum_gap_filter_mem_eq [DecidableEq ι] {x : X} {j k : ι}
    (hj : j ∈ ρ.finsupport x) (hkj : ρ k x < ρ j x)
    (hmax : ∀ i ∈ ρ.finsupport x, ρ i x < ρ j x → ρ i x ≤ ρ k x) :
    ∑ E ∈ (ρ.finsupport x).powerset.filter (j ∈ ·), ρ.gap E x =
      ρ j x - ρ k x + ∑ E ∈ (ρ.finsupport x).powerset.filter (k ∈ ·), ρ.gap E x := by
  set T := ρ.finsupport x
  set U := T.filter fun i ↦ ρ j x ≤ ρ i x
  have hjU : j ∈ U := Finset.mem_filter.2 ⟨hj, le_rfl⟩
  have hkU : k ∉ U := fun h ↦ (Finset.mem_filter.1 h).2.not_gt hkj
  -- An index outside `U` either has weight zero or weight at most `ρ k x`.
  have hle {i : ι} (hi : i ∉ U) : ρ i x ≤ ρ k x := by
    by_cases hiT : i ∈ T
    · exact hmax i hiT (not_le.1 fun h ↦ hi (Finset.mem_filter.2 ⟨hiT, h⟩))
    · exact (notMem_finsupport_iff.1 hiT).trans_le (ρ.nonneg k x)
  have hgapU : ρ.gap U x = ρ j x - ρ k x := by
    rw [gap, iInf_eq_of_mem hjU fun i hi ↦ (Finset.mem_filter.1 hi).2,
      iSup_compl_eq_of_notMem hkU fun i hi ↦ hle hi, max_eq_right (sub_nonneg.2 hkj.le)]
  -- The sets containing `j` with positive gap are `U` and the sets containing `k` with positive
  -- gap.
  have hfilter : (T.powerset.filter (j ∈ ·)).filter (ρ.gap · x ≠ 0) =
      insert U ((T.powerset.filter (k ∈ ·)).filter (ρ.gap · x ≠ 0)) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hET, hjE⟩, hne⟩
      have hpos := gap_pos_iff_ne_zero.2 hne
      refine or_iff_not_imp_left.2 fun hEU ↦ ⟨⟨hET, ?_⟩, hne⟩
      have hUE : U ⊆ E := fun i hiU ↦ mem_of_gap_pos_of_le hpos hjE (Finset.mem_filter.1 hiU).2
      obtain ⟨i, hiE, hiU⟩ := Finset.not_subset.1 fun h ↦ hEU (Finset.Subset.antisymm h hUE)
      by_contra hkE
      exact (lt_of_gap_pos hpos hiE hkE).not_ge (hle hiU)
    · rintro (rfl | ⟨⟨hET, hkE⟩, hne⟩)
      · exact ⟨⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), hjU⟩,
          hgapU ▸ (sub_pos.2 hkj).ne'⟩
      · exact ⟨⟨hET, mem_of_gap_pos_of_le (gap_pos_iff_ne_zero.2 hne) hkE hkj.le⟩, hne⟩
  have hUnot : U ∉ (T.powerset.filter (k ∈ ·)).filter (ρ.gap · x ≠ 0) := fun h ↦
    hkU (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).2
  rw [← Finset.sum_filter_ne_zero, hfilter, Finset.sum_insert hUnot, Finset.sum_filter_ne_zero,
    hgapU]

/-- The finite form of `finsum_mem_gap`, summing over subsets of the finite support. -/
private theorem sum_gap_filter_mem [DecidableEq ι] (x : X) (j : ι) :
    ∑ E ∈ (ρ.finsupport x).powerset.filter (j ∈ ·), ρ.gap E x = ρ j x := by
  set T := ρ.finsupport x
  by_cases hjT : j ∉ T
  · rw [notMem_finsupport_iff.1 hjT, Finset.sum_eq_zero fun E hE ↦ (hjT <|
      Finset.mem_powerset.1 (Finset.mem_filter.1 hE).1 (Finset.mem_filter.1 hE).2).elim]
  push Not at hjT
  -- Strong induction on the number of nonzero weights strictly below `ρ j x`.
  suffices H : ∀ n, ∀ j ∈ T, (T.filter fun i ↦ ρ i x < ρ j x).card = n →
      ∑ E ∈ T.powerset.filter (j ∈ ·), ρ.gap E x = ρ j x from H _ j hjT rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hjT hn
  rcases (T.filter fun i ↦ ρ i x < ρ j x).eq_empty_or_nonempty with hL | hL
  · refine sum_gap_filter_mem_of_forall_le hjT fun i hi ↦ not_lt.1 fun hlt ↦ ?_
    exact Finset.notMem_empty i (hL ▸ Finset.mem_filter.2 ⟨hi, hlt⟩)
  obtain ⟨k, hkL, hkmax⟩ := (T.filter fun i ↦ ρ i x < ρ j x).exists_max_image (ρ · x) hL
  obtain ⟨hkT, hkj⟩ := Finset.mem_filter.1 hkL
  have hcard : (T.filter fun i ↦ ρ i x < ρ k x).card < n := hn ▸ Finset.card_lt_card
    ⟨Finset.monotone_filter_right _ fun _ _ hik ↦ hik.trans hkj,
      fun h ↦ lt_irrefl _ (Finset.mem_filter.1 (h hkL)).2⟩
  rw [sum_gap_filter_mem_eq hjT hkj fun i hi hij ↦ hkmax i (Finset.mem_filter.2 ⟨hi, hij⟩),
    ih _ hcard k hkT rfl, sub_add_cancel]

/-- The gaps of the finite sets containing a fixed index `j` sum to the weight `ρ j x`. -/
theorem finsum_mem_gap (x : X) (j : ι) : ∑ᶠ (E : Finset ι) (_ : j ∈ E), ρ.gap E x = ρ j x := by
  classical
  rw [← sum_gap_filter_mem x j]
  refine finsum_mem_eq_sum_of_inter_support_eq (s := {E : Finset ι | j ∈ E}) _ ?_
  ext E
  simp only [mem_inter_iff, mem_ofPred_eq, Finset.coe_filter, Finset.mem_powerset,
    mem_support]
  exact ⟨fun ⟨hjE, hne⟩ ↦ ⟨⟨subset_finsupport_of_gap_pos (gap_pos_iff_ne_zero.2 hne), hjE⟩, hne⟩,
    fun ⟨⟨_, hjE⟩, hne⟩ ↦ ⟨hjE, hne⟩⟩

/-- The finite form of `finsum_card_mul_gap`, summing over subsets of the finite support. -/
private theorem sum_card_mul_gap (x : X) :
    ∑ E ∈ (ρ.finsupport x).powerset, (E.card : ℝ) * ρ.gap E x =
      ∑ i ∈ ρ.finsupport x, ρ i x := by
  classical
  calc ∑ E ∈ (ρ.finsupport x).powerset, (E.card : ℝ) * ρ.gap E x
      = ∑ E ∈ (ρ.finsupport x).powerset, ∑ _j ∈ E, ρ.gap E x := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ j ∈ ρ.finsupport x, ∑ E ∈ (ρ.finsupport x).powerset.filter (j ∈ ·), ρ.gap E x := by
        refine Finset.sum_comm' fun E j ↦ ?_
        simp only [Finset.mem_powerset, Finset.mem_filter]
        exact ⟨fun ⟨hE, hj⟩ ↦ ⟨⟨hE, hj⟩, hE hj⟩, fun ⟨⟨hE, hj⟩, _⟩ ↦ ⟨hE, hj⟩⟩
    _ = ∑ i ∈ ρ.finsupport x, ρ i x := Finset.sum_congr rfl fun j _ ↦ sum_gap_filter_mem x j

/-- Weighting each gap by the size of its set recovers the total weight. -/
theorem finsum_card_mul_gap (x : X) :
    ∑ᶠ E : Finset ι, (E.card : ℝ) * ρ.gap E x = ∑ᶠ i, ρ i x := by
  classical
  rw [finsum_eq_sum_of_support_subset _ ((support_mul_subset_right _ _).trans
      (support_gap_subset (ρ.coe_finsupport x).superset)),
    finsum_eq_sum_of_support_subset _ (ρ.coe_finsupport x).superset, sum_card_mul_gap]

/-- On the set of a partition of unity, the size-weighted gaps sum to one. -/
theorem finsum_card_mul_gap_eq_one {x : X} (hx : x ∈ s) :
    ∑ᶠ E : Finset ι, (E.card : ℝ) * ρ.gap E x = 1 := by
  rw [finsum_card_mul_gap, ρ.sum_eq_one hx]

/-! ### The countable partition of unity -/

/-- Pointwise, the gaps of a fixed size are a finite sum over subsets of any finite set carrying
all nonzero weights. -/
private theorem finsum_card_eq_gap_eq_sum {I : Finset ι} {x : X}
    (hI : support (ρ · x) ⊆ I) (n : ℕ) :
    ∑ᶠ (E : Finset ι) (_ : E.card = n), ρ.gap E x = ∑ E ∈ I.powersetCard n, ρ.gap E x := by
  refine finsum_mem_eq_sum_of_inter_support_eq (s := {E : Finset ι | E.card = n}) _ ?_
  ext E
  simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_coe, Finset.mem_powersetCard]
  refine ⟨fun ⟨hE, hne⟩ ↦ ⟨⟨?_, hE⟩, hne⟩, fun ⟨⟨_, hE⟩, hne⟩ ↦ ⟨hE, hne⟩⟩
  exact Finset.mem_powerset.1 (support_gap_subset hI hne)

private theorem continuous_card_mul_finsum_gap (n : ℕ) :
    Continuous fun x ↦ (n : ℝ) * ∑ᶠ (E : Finset ι) (_ : E.card = n), ρ.gap E x := by
  classical
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  obtain ⟨I, hI⟩ := ρ.locallyFinite.exists_finset_support x₀
  have hcont : Continuous fun x ↦ (n : ℝ) * ∑ E ∈ I.powersetCard n, ρ.gap E x :=
    continuous_const.mul <| continuous_finsetSum _ fun E _ ↦ continuous_gap E
  exact hcont.continuousAt.congr
    (hI.mono fun x hx ↦ congrArg ((n : ℝ) * ·) (finsum_card_eq_gap_eq_sum hx n).symm)

private theorem finsum_card_mul_finsum_gap (x : X) :
    ∑ᶠ n : ℕ, (n : ℝ) * ∑ᶠ (E : Finset ι) (_ : E.card = n), ρ.gap E x = ∑ᶠ i, ρ i x := by
  classical
  set T := ρ.finsupport x
  have hT : support (ρ · x) ⊆ T := (ρ.coe_finsupport x).superset
  simp_rw [finsum_card_eq_gap_eq_sum hT]
  have hsupp : support (fun n : ℕ ↦ (n : ℝ) * ∑ E ∈ T.powersetCard n, ρ.gap E x) ⊆
      Finset.range (T.card + 1) := fun n hn ↦ by
    by_contra h
    rw [Finset.mem_coe, Finset.mem_range, not_lt, Nat.succ_le_iff] at h
    exact hn (by simp only [Finset.powersetCard_eq_empty.2 h, Finset.sum_empty, mul_zero])
  rw [finsum_eq_sum_of_support_subset _ hsupp, finsum_eq_sum_of_support_subset _ hT,
    ← sum_card_mul_gap, ← Finset.sum_fiberwise_of_maps_to (g := Finset.card)
      (t := Finset.range (T.card + 1)) fun E hE ↦
        Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_le_card (Finset.mem_powerset.1 hE)))]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Finset.mul_sum, ← Finset.powersetCard_eq_filter]
  exact Finset.sum_congr rfl fun E hE ↦ by rw [(Finset.mem_powersetCard.1 hE).2]

/-- The countable partition of unity obtained from a partition of unity `ρ` by grouping its gaps
by cardinality: its `n`-th weight is `n * ∑ᶠ_{#E = n} ρ.gap E`. The `0`-th weight vanishes. It is
a partition of unity on the same set as `ρ`, whatever the cardinality of the index type of `ρ`.
At each point at most one set of size `n` has positive gap (`eq_of_gap_pos_of_card_eq`), so where
the `n`-th weight is positive it is carried by a single set; see `gapPartition_card_eq`. -/
noncomputable def gapPartition : PartitionOfUnity ℕ X s where
  toFun n := ⟨fun x ↦ (n : ℝ) * ∑ᶠ (E : Finset ι) (_ : E.card = n), ρ.gap E x,
    continuous_card_mul_finsum_gap n⟩
  locallyFinite' := by
    classical
    intro x₀
    obtain ⟨I, hI⟩ := ρ.locallyFinite.exists_finset_support x₀
    refine ⟨_, hI, (Set.finite_Iic I.card).subset fun n ⟨x, hxn, hx⟩ ↦ ?_⟩
    simp only [mem_support, ContinuousMap.coe_mk, finsum_card_eq_gap_eq_sum hx n] at hxn
    by_contra hn
    rw [Finset.powersetCard_eq_empty.2 (not_le.1 hn), Finset.sum_empty, mul_zero] at hxn
    exact hxn rfl
  nonneg' n x := by
    classical
    simp only [Pi.zero_apply, finsum_card_eq_gap_eq_sum (ρ.coe_finsupport x).superset n]
    exact mul_nonneg n.cast_nonneg (Finset.sum_nonneg fun E _ ↦ ρ.gap_nonneg E x)
  sum_eq_one' x hx := by
    simpa only [ContinuousMap.coe_mk, finsum_card_mul_finsum_gap] using ρ.sum_eq_one hx
  sum_le_one' x := by
    simpa only [ContinuousMap.coe_mk, finsum_card_mul_finsum_gap] using ρ.sum_le_one x

variable (ρ) in
theorem gapPartition_apply (n : ℕ) (x : X) :
    ρ.gapPartition n x = n * ∑ᶠ (E : Finset ι) (_ : E.card = n), ρ.gap E x :=
  (rfl)

@[simp]
theorem gapPartition_zero (x : X) : ρ.gapPartition 0 x = 0 := by
  simp [gapPartition_apply]

/-- Where a set `E` has positive gap, the weight of `gapPartition` indexed by its size is carried
by `E` alone. -/
theorem gapPartition_card_eq {E : Finset ι} {x : X} (h : 0 < ρ.gap E x) :
    ρ.gapPartition E.card x = E.card * ρ.gap E x := by
  classical
  rw [gapPartition_apply, finsum_card_eq_gap_eq_sum (ρ.coe_finsupport x).superset,
    Finset.sum_eq_single_of_mem E
      (Finset.mem_powersetCard.2 ⟨subset_finsupport_of_gap_pos h, rfl⟩)]
  intro F hF hFE
  by_contra hne
  exact hFE (eq_of_gap_pos_of_card_eq (gap_pos_iff_ne_zero.2 hne) h
    (Finset.mem_powersetCard.1 hF).2)

/-- A positive weight of `gapPartition` at `x` is carried by a set of indices of that size with
positive gap at `x`. -/
theorem exists_gap_pos_of_gapPartition_pos {n : ℕ} {x : X} (h : 0 < ρ.gapPartition n x) :
    ∃ E : Finset ι, E.card = n ∧ 0 < ρ.gap E x := by
  by_contra! hE
  have h0 : ∑ᶠ (E : Finset ι) (_ : E.card = n), ρ.gap E x = 0 :=
    finsum_eq_zero_of_forall_eq_zero fun E ↦ by
      rw [finsum_eq_if]
      split_ifs with hE'
      exacts [(hE E hE').antisymm (ρ.gap_nonneg E x), rfl]
  rw [gapPartition_apply, h0, mul_zero] at h
  exact lt_irrefl 0 h

end PartitionOfUnity
