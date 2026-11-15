/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.MilnorJoin.Bundle
public import TauCeti.Topology.Homotopy.Extension.Ball
public import TauCeti.Topology.Homotopy.HomotopyGroup.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.FundamentalGroupAction
public import TauCeti.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Weak contractibility of the strong-coordinate Milnor join

Unlike the weak simplicial join `universalGSpace G`, a compact subset of the strong-coordinate join
`TauCeti.MilnorTotalSpace G` need not lie in a finite subjoin. Following Milnor (*Construction of
universal bundles, II*, §3) and tom Dieck (*Algebraic Topology*, §14.4.3), we prove weak
contractibility directly from the strong coordinate topology:

1. For each cutoff `N : ℕ`, the partial weight sum
   `S_N(p) = ∑ i ∈ Finset.range N, weight i p` is continuous and approaches `1` on each point. By
   compactness, any continuous map `f : C(X, MilnorTotalSpace G)` with compact image admits a single
   `N` such that `1 / 2 < S_N(f x)` for all `x`
   (`TauCeti.MilnorTotalSpace.exists_gt_half_partialWeightSum_of_isCompact_range`).
2. Multiplying tail weights (`i ≥ N`) by `1 - s` and dividing all weights by the positive
   denominator `S_N + (1 - s)(1 - S_N)` defines a homotopy
   `TauCeti.MilnorTotalSpace.tailTruncationHomotopy` from `f` to a map
   `TauCeti.MilnorTotalSpace.tailTruncationMap` supported on indices `< N`. Continuity follows from
   `TauCeti.MilnorTotalSpace.continuous_iff`, referencing vertex labels only where weights are
   strictly positive.
3. Because index `N` has zero weight everywhere along the truncated map, linear interpolation in
   coordinates deforms it to a vertex `vertex N a` at the unused index `N`
   (`TauCeti.MilnorTotalSpace.coneAtFreshIndexHomotopy`, taking `a = 1` when `G` has a unit).

Every continuous map with compact image into `MilnorTotalSpace G` is therefore null-homotopic when
`G` is nonempty (`ContinuousMap.nullhomotopic_to_milnorTotalSpace_of_isCompact_range`,
`ContinuousMap.nullhomotopic_to_milnorTotalSpace`). Consequently `MilnorTotalSpace G` is path
connected, simply connected, and has trivial homotopy groups in all dimensions,
`MilnorClassifyingSpace G` is path connected, and every sphere map into `MilnorTotalSpace G` is both
freely and pointedly null-homotopic and extends over the closed unit ball.

## Main definitions

* `TauCeti.MilnorTotalSpace.partialWeightSum`: continuous partial sum `S_N = ∑_{i < N} t_i`.
* `TauCeti.MilnorTotalSpace.tailTruncationMap`, `TauCeti.MilnorTotalSpace.tailTruncationHomotopy`:
  truncation to indices `< N` and the renormalized homotopy from `f` when `0 < S_N ∘ f`.
* `TauCeti.MilnorTotalSpace.coneAtFreshIndexHomotopy`: coordinate cone homotopy to `vertex N a` for
  a map whose `N`-th weight vanishes everywhere.

## Main results

* `TauCeti.MilnorTotalSpace.exists_gt_half_partialWeightSum_of_isCompact_range`: uniform bound
  `1 / 2 < S_N(f x)` over any map with compact range.
* `ContinuousMap.nullhomotopic_to_milnorTotalSpace_of_isCompact_range`,
  `ContinuousMap.nullhomotopic_to_milnorTotalSpace`: maps with compact image (or from compact
  domains) into `MilnorTotalSpace G` are null-homotopic.
* `TauCeti.instPathConnectedSpaceMilnorTotalSpace`,
  `TauCeti.instPathConnectedSpaceMilnorClassifyingSpace`,
  `TauCeti.instSimplyConnectedSpaceMilnorTotalSpace`,
  `HomotopyGroup.subsingleton_milnorTotalSpace`: connectivity and vanishing of all homotopy groups.
* `TauCeti.exists_extension_closedBall_milnorTotalSpace`,
  `TauCeti.homotopicRel_const_singleton_sphere_milnorTotalSpace`: unbased closed-ball extension and
  pointed null-homotopy of maps from unit spheres.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. (2) 63 (1956), 430–436, §3.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, §14.4.3.
-/

public section

noncomputable section

open HomotopyGroup Metric Set Topology unitInterval
open scoped Topology.Homotopy

universe u v

namespace TauCeti

namespace MilnorTotalSpace

/-! ### Constructing join points from finite-support weights and labels -/

section CoordBuilder

variable {G : Type u}

/-- Underlying coordinate vector placing weight `w i` at vertex `⟨i, ℓ i⟩` for `i ∈ S`. -/
private def ofFinsetCoordVal (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G) : (Σ _ : ℕ, G) →₀ ℝ := by
  let _ : DecidableEq (Σ _ : ℕ, G) := Classical.decEq _
  exact ∑ i ∈ S, Finsupp.single (⟨i, ℓ i⟩ : Σ _ : ℕ, G) (w i)

private theorem ofFinsetCoordVal_apply [DecidableEq G] (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G)
    (i : ℕ) (b : G) :
    ofFinsetCoordVal S w ℓ ⟨i, b⟩ = if i ∈ S ∧ b = ℓ i then w i else 0 := by
  unfold ofFinsetCoordVal
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply, Sigma.mk.injEq]
  by_cases hi : i ∈ S
  · rw [Finset.sum_eq_single i]
    · simp [hi, eq_comm]
    · intro j _ hji
      simp [hji]
    · intro hi'
      exact absurd hi hi'
  · rw [Finset.sum_eq_zero]
    · simp [hi]
    · intro j hj
      have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
      simp [hji]

/-- Point of `MilnorTotalSpace G` built from nonnegative weights `w` summing to `1` on a finite
index set `S` and vertex labels `ℓ`. -/
private def ofFinsetCoord (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G)
    (hw_nonneg : ∀ i ∈ S, 0 ≤ w i) (hw_sum : ∑ i ∈ S, w i = 1) : MilnorTotalSpace G := by
  classical
  refine ofRealization ⟨ofFinsetCoordVal S w ℓ, ?_⟩
  rw [mem_indexedJoin_realization_iff]
  refine ⟨fun ⟨i, b⟩ ↦ ?_, ?_, fun ⟨i₁, b₁⟩ ⟨i₂, b₂⟩ hv₁ hv₂ h12 ↦ ?_⟩
  · rw [ofFinsetCoordVal_apply]
    split_ifs with h
    · exact hw_nonneg i h.1
    · exact le_rfl
  · unfold ofFinsetCoordVal
    rw [Finsupp.sum_finsetSum _ _ _ (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
      Finset.sum_congr rfl fun i _ ↦ Finsupp.sum_single_index (h := fun _ r ↦ r) rfl]
    exact hw_sum
  · dsimp only at h12
    subst h12
    rw [ofFinsetCoordVal_apply] at hv₁ hv₂
    split_ifs at hv₁ with h₁
    · split_ifs at hv₂ with h₂
      · rw [h₁.2, h₂.2]
      · exact absurd rfl hv₂
    · exact absurd rfl hv₁

private theorem val_ofFinsetCoord [DecidableEq G] (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G)
    (hw_nonneg : ∀ i ∈ S, 0 ≤ w i) (hw_sum : ∑ i ∈ S, w i = 1) (i : ℕ) (b : G) :
    (ofFinsetCoord S w ℓ hw_nonneg hw_sum).val ⟨i, b⟩ =
      if i ∈ S ∧ b = ℓ i then w i else 0 := by
  rw [ofFinsetCoord, val_ofRealization, ofFinsetCoordVal_apply]

private theorem weight_ofFinsetCoord (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G)
    (hw_nonneg : ∀ i ∈ S, 0 ≤ w i) (hw_sum : ∑ i ∈ S, w i = 1) (i : ℕ) :
    weight i (ofFinsetCoord S w ℓ hw_nonneg hw_sum) = if i ∈ S then w i else 0 := by
  classical
  by_cases hi : i ∈ S
  · simp only [hi, ↓reduceIte]
    by_cases hwi : w i = 0
    · rw [hwi]
      by_contra hne
      obtain ⟨b, hb⟩ := weight_ne_zero_iff.mp hne
      rw [val_ofFinsetCoord] at hb
      simp [hwi] at hb
    · have hv : (ofFinsetCoord S w ℓ hw_nonneg hw_sum).val ⟨i, ℓ i⟩ = w i := by
        rw [val_ofFinsetCoord]
        simp [hi]
      rw [weight_eq_val_of_ne_zero (hv ▸ hwi), hv]
  · simp only [hi, ↓reduceIte]
    by_contra hne
    obtain ⟨b, hb⟩ := weight_ne_zero_iff.mp hne
    rw [val_ofFinsetCoord] at hb
    simp [hi] at hb

private theorem label_ofFinsetCoord (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G)
    (hw_nonneg : ∀ i ∈ S, 0 ≤ w i) (hw_sum : ∑ i ∈ S, w i = 1) {i : ℕ}
    (hi : i ∈ S) (hwi : 0 < w i) :
    label i (ofFinsetCoord S w ℓ hw_nonneg hw_sum) = ℓ i := by
  classical
  refine (eq_label_of_val_pos (p := ofFinsetCoord S w ℓ hw_nonneg hw_sum) ?_).symm
  rw [val_ofFinsetCoord]
  simp [hi, hwi]

private theorem sum_weight_of_support_subset {p : MilnorTotalSpace G} {S : Finset ℕ}
    (hS : ∀ i, i ∉ S → weight i p = 0) : ∑ i ∈ S, weight i p = 1 :=
  (hasSum_sum_of_ne_finset_zero hS).unique (hasSum_weight p)

end CoordBuilder

/-! ### Partial weight sums and compact tail bounds -/

section PartialWeightSum

variable (G : Type u) [TopologicalSpace G]

/-- Continuous partial sum `S_N(p) = ∑_{i < N} t_i(p)` of the first `N` barycentric weights. -/
def partialWeightSum (N : ℕ) : C(MilnorTotalSpace G, ℝ) where
  toFun p := ∑ i ∈ Finset.range N, weight i p
  continuous_toFun := by fun_prop

variable {G}

@[simp]
theorem partialWeightSum_apply (N : ℕ) (p : MilnorTotalSpace G) :
    partialWeightSum G N p = ∑ i ∈ Finset.range N, weight i p :=
  (rfl)

theorem partialWeightSum_zero (p : MilnorTotalSpace G) : partialWeightSum G 0 p = 0 := by
  simp

theorem partialWeightSum_nonneg (N : ℕ) (p : MilnorTotalSpace G) :
    0 ≤ partialWeightSum G N p := by
  rw [partialWeightSum_apply]
  exact Finset.sum_nonneg fun i _ ↦ weight_nonneg i p

theorem partialWeightSum_mono {M N : ℕ} (hMN : M ≤ N) (p : MilnorTotalSpace G) :
    partialWeightSum G M p ≤ partialWeightSum G N p := by
  rw [partialWeightSum_apply, partialWeightSum_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN)
    fun i _ _ ↦ weight_nonneg i p

theorem partialWeightSum_le_one (N : ℕ) (p : MilnorTotalSpace G) :
    partialWeightSum G N p ≤ 1 := by
  let S := (finite_support_weight p).toFinset ∪ Finset.range N
  have hsum : ∑ i ∈ S, weight i p = 1 :=
    sum_weight_of_support_subset fun i hi ↦ by
      by_contra hne
      exact hi (Finset.mem_union_left _ ((finite_support_weight p).mem_toFinset.mpr hne))
  rw [← hsum, partialWeightSum_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    fun i _ _ ↦ weight_nonneg i p

/-- Every point of `MilnorTotalSpace G` has partial weight sum equal to `1` once `N` exceeds its
finitely many active indices. -/
theorem exists_partialWeightSum_eq_one (p : MilnorTotalSpace G) :
    ∃ N, partialWeightSum G N p = 1 := by
  let supp := (finite_support_weight p).toFinset
  refine ⟨supp.sup id + 1, ?_⟩
  rw [partialWeightSum_apply]
  refine sum_weight_of_support_subset fun i hi ↦ ?_
  by_contra hne
  have hmem : i ∈ supp := (finite_support_weight p).mem_toFinset.mpr hne
  exact hi (Finset.mem_range.mpr (Nat.lt_succ_of_le (supp.le_sup (f := id) hmem)))

/-- Every point of `MilnorTotalSpace G` has `1 / 2 < partialWeightSum G N p` for some `N`. -/
theorem exists_gt_half_partialWeightSum (p : MilnorTotalSpace G) :
    ∃ N, 1 / 2 < partialWeightSum G N p := by
  obtain ⟨N, hN⟩ := exists_partialWeightSum_eq_one p
  exact ⟨N, by linarith⟩

/-- **Compact tail bound.** For any continuous map `f : C(X, MilnorTotalSpace G)` with compact
image, a single cutoff `N` satisfies `1 / 2 < S_N(f x)` for all `x : X`. -/
theorem exists_gt_half_partialWeightSum_of_isCompact_range {X : Type v} [TopologicalSpace X]
    {f : C(X, MilnorTotalSpace G)} (hf : IsCompact (Set.range f)) :
    ∃ N, ∀ x, 1 / 2 < partialWeightSum G N (f x) := by
  obtain ⟨t, ht⟩ := hf.elim_finite_subcover
    (fun N ↦ {p : MilnorTotalSpace G | 1 / 2 < partialWeightSum G N p})
    (fun N ↦ isOpen_lt continuous_const (partialWeightSum G N).continuous)
    fun p _ ↦ Set.mem_iUnion.mpr (exists_gt_half_partialWeightSum p)
  refine ⟨t.sup id, fun x ↦ ?_⟩
  obtain ⟨N, hNt, hNx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_range_self x))
  exact lt_of_lt_of_le hNx (partialWeightSum_mono (t.le_sup (f := id) hNt) (f x))

/-- On a compact domain, a single cutoff `N` satisfies `1 / 2 < S_N(f x)` everywhere. -/
theorem exists_gt_half_partialWeightSum_comp {X : Type v} [TopologicalSpace X] [CompactSpace X]
    (f : C(X, MilnorTotalSpace G)) :
    ∃ N, ∀ x, 1 / 2 < partialWeightSum G N (f x) :=
  exists_gt_half_partialWeightSum_of_isCompact_range (isCompact_range f.continuous)

end PartialWeightSum

/-! ### Tail-truncation homotopy and fresh-vertex cone homotopy -/

section Homotopies

variable {G : Type u} [TopologicalSpace G] {X : Type v} [TopologicalSpace X]

/-- Denominator `S_N(f x) + (1 - s)(1 - S_N(f x))` of the tail-truncation homotopy at `(s, x)`. -/
private def tailDenom (N : ℕ) (f : C(X, MilnorTotalSpace G)) (z : I × X) : ℝ :=
  partialWeightSum G N (f z.2) + (1 - (z.1 : ℝ)) * (1 - partialWeightSum G N (f z.2))

private theorem tailDenom_pos {N : ℕ} {f : C(X, MilnorTotalSpace G)}
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) :
    0 < tailDenom N f z := by
  have hS_pos : 0 < partialWeightSum G N (f z.2) := hf z.2
  have hS_le : partialWeightSum G N (f z.2) ≤ 1 := partialWeightSum_le_one N (f z.2)
  have hs : 0 ≤ 1 - (z.1 : ℝ) := sub_nonneg.mpr z.1.2.2
  have h1S : 0 ≤ 1 - partialWeightSum G N (f z.2) := sub_nonneg.mpr hS_le
  exact add_pos_of_pos_of_nonneg hS_pos (mul_nonneg hs h1S)

/-- Rescaled weight of `tailTruncationHomotopy` at index `i` and parameter `z = (s, x)`. -/
private def tailWeight (N : ℕ) (f : C(X, MilnorTotalSpace G)) (z : I × X) (i : ℕ) : ℝ :=
  (if i < N then weight i (f z.2) else (1 - (z.1 : ℝ)) * weight i (f z.2)) / tailDenom N f z

private theorem tailWeight_nonneg {N : ℕ} {f : C(X, MilnorTotalSpace G)}
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) (i : ℕ) :
    0 ≤ tailWeight N f z i := by
  refine div_nonneg ?_ (tailDenom_pos hf z).le
  split_ifs
  · exact weight_nonneg i (f z.2)
  · exact mul_nonneg (sub_nonneg.mpr z.1.2.2) (weight_nonneg i (f z.2))

private theorem sum_tailWeight {N : ℕ} {f : C(X, MilnorTotalSpace G)}
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) :
    ∑ i ∈ (finite_support_weight (f z.2)).toFinset ∪ Finset.range N, tailWeight N f z i = 1 := by
  let S := (finite_support_weight (f z.2)).toFinset ∪ Finset.range N
  have hsum_one : ∑ i ∈ S, weight i (f z.2) = 1 :=
    sum_weight_of_support_subset fun i hi ↦ by
      by_contra hne
      exact hi (Finset.mem_union_left _ ((finite_support_weight (f z.2)).mem_toFinset.mpr hne))
  have hfilter : S.filter (· < N) = Finset.range N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    intro hi
    exact Finset.mem_union_right _ (Finset.mem_range.mpr hi)
  have hsplit := Finset.sum_filter_add_sum_filter_not S (· < N) (fun i ↦ weight i (f z.2))
  rw [hfilter, ← partialWeightSum_apply, hsum_one] at hsplit
  have htail : ∑ i ∈ S.filter (fun i ↦ ¬ i < N), weight i (f z.2) =
      1 - partialWeightSum G N (f z.2) := by linarith
  unfold tailWeight
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul, ← div_eq_mul_inv]
  have hnum : ∑ i ∈ S,
      (if i < N then weight i (f z.2) else (1 - (z.1 : ℝ)) * weight i (f z.2)) =
        tailDenom N f z := by
    rw [← Finset.sum_filter_add_sum_filter_not S (· < N)]
    have hleft : ∑ i ∈ S.filter (· < N),
        (if i < N then weight i (f z.2) else (1 - (z.1 : ℝ)) * weight i (f z.2)) =
          partialWeightSum G N (f z.2) := by
      rw [Finset.sum_congr rfl fun i hi ↦ ite_eq_left (Finset.mem_filter.mp hi).2, hfilter,
        partialWeightSum_apply]
    have hright : ∑ i ∈ S.filter (fun i ↦ ¬ i < N),
        (if i < N then weight i (f z.2) else (1 - (z.1 : ℝ)) * weight i (f z.2)) =
          (1 - (z.1 : ℝ)) * (1 - partialWeightSum G N (f z.2)) := by
      rw [Finset.sum_congr rfl fun i hi ↦ ite_eq_right (Finset.mem_filter.mp hi).2,
        ← Finset.mul_sum, htail]
    rw [hleft, hright]
    rfl
  rw [hnum, div_self (tailDenom_pos hf z).ne']

/-- Pointwise value of the tail-truncation homotopy at `z = (s, x)`. -/
private def tailTruncationPt (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) : MilnorTotalSpace G :=
  ofFinsetCoord ((finite_support_weight (f z.2)).toFinset ∪ Finset.range N)
    (tailWeight N f z) (fun i ↦ label i (f z.2))
    (fun i _ ↦ tailWeight_nonneg hf z i) (sum_tailWeight hf z)

private theorem weight_tailTruncationPt (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (z : I × X) (i : ℕ) :
    weight i (tailTruncationPt N f hf z) = tailWeight N f z i := by
  unfold tailTruncationPt
  rw [weight_ofFinsetCoord]
  split_ifs with hi
  · rfl
  · have hw0 : weight i (f z.2) = 0 := by
      by_contra hne
      exact hi (Finset.mem_union_left _
        ((finite_support_weight (f z.2)).mem_toFinset.mpr hne))
    simp [tailWeight, hw0]

private theorem label_tailTruncationPt (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) {z : I × X} {i : ℕ}
    (hz : 0 < tailWeight N f z i) :
    label i (tailTruncationPt N f hf z) = label i (f z.2) := by
  have hw_pos : 0 < weight i (f z.2) := by
    by_contra hle
    have hw0 : weight i (f z.2) = 0 :=
      le_antisymm (not_lt.mp hle) (weight_nonneg i (f z.2))
    simp [tailWeight, hw0] at hz
  have hi_mem : i ∈ (finite_support_weight (f z.2)).toFinset ∪ Finset.range N :=
    Finset.mem_union_left _ ((finite_support_weight (f z.2)).mem_toFinset.mpr hw_pos.ne')
  exact label_ofFinsetCoord _ _ _ _ _ hi_mem hz

/-- Underlying parameterized map of the tail-truncation homotopy on `I × X`. -/
private def tailTruncationHomotopyFun (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) : C(I × X, MilnorTotalSpace G) where
  toFun := tailTruncationPt N f hf
  continuous_toFun := by
    have hden_cont : Continuous (tailDenom N f) := by
      unfold tailDenom
      fun_prop
    rw [continuous_iff]
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · simp_rw [weight_tailTruncationPt]
      unfold tailWeight
      by_cases hi : i < N
      · simp only [hi, ↓reduceIte]
        exact ((continuous_weight i).comp (f.continuous.comp continuous_snd)).div
          hden_cont fun z ↦ (tailDenom_pos hf z).ne'
      · simp only [hi, ↓reduceIte]
        exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          ((continuous_weight i).comp (f.continuous.comp continuous_snd)))).div
          hden_cont fun z ↦ (tailDenom_pos hf z).ne'
    · refine ((continuousOn_label i).comp (f.continuous.comp continuous_snd).continuousOn
        (fun z hz ↦ ?_)).congr fun z hz ↦ ?_
      · change 0 < weight i (tailTruncationPt N f hf z) at hz
        rw [weight_tailTruncationPt] at hz
        rw [mem_coordSet_iff]
        by_contra hle
        have hw0 : weight i (f z.2) = 0 :=
          le_antisymm (not_lt.mp hle) (weight_nonneg i (f z.2))
        simp [tailWeight, hw0] at hz
      · change 0 < weight i (tailTruncationPt N f hf z) at hz
        rw [weight_tailTruncationPt] at hz
        exact label_tailTruncationPt N f hf hz

/-- **Truncated map at `s = 1`.** Given `0 < S_N(f x)` everywhere, `tailTruncationMap N f hf` keeps
the first `N` labels of `f`, renormalizes weights `< N` by `S_N(f x)`, and sets all weights `≥ N`
to `0`. -/
def tailTruncationMap (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) : C(X, MilnorTotalSpace G) :=
  (tailTruncationHomotopyFun N f hf).comp ⟨fun x ↦ (1, x), by fun_prop⟩

@[simp]
theorem weight_tailTruncationMap (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) (i : ℕ) (x : X) :
    weight i (tailTruncationMap N f hf x) =
      if i < N then weight i (f x) / partialWeightSum G N (f x) else 0 := by
  change weight i (tailTruncationPt N f hf (1, x)) = _
  rw [weight_tailTruncationPt]
  have hden1 : tailDenom N f (1, x) = partialWeightSum G N (f x) := by
    simp [tailDenom]
  by_cases hi : i < N
  · simp [hi, tailWeight, hden1]
  · simp [hi, tailWeight]

theorem weight_tailTruncationMap_of_le (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) {i : ℕ} (hi : N ≤ i) (x : X) :
    weight i (tailTruncationMap N f hf x) = 0 := by
  rw [weight_tailTruncationMap, ite_eq_right (not_lt.mpr hi)]

@[simp]
theorem label_tailTruncationMap (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) {i : ℕ} {x : X} (hi : i < N)
    (hx : f x ∈ coordSet G i) :
    label i (tailTruncationMap N f hf x) = label i (f x) := by
  change label i (tailTruncationPt N f hf (1, x)) = _
  refine label_tailTruncationPt N f hf ?_
  simp only [tailWeight, hi, ↓reduceIte]
  exact div_pos (mem_coordSet_iff.mp hx) (tailDenom_pos hf (1, x))

/-- **Renormalized tail-truncation homotopy** from `f` to `tailTruncationMap N f hf` when
`0 < S_N(f x)` everywhere. -/
def tailTruncationHomotopy (N : ℕ) (f : C(X, MilnorTotalSpace G))
    (hf : ∀ x, 0 < partialWeightSum G N (f x)) :
    f.Homotopy (tailTruncationMap N f hf) where
  toContinuousMap := tailTruncationHomotopyFun N f hf
  map_zero_left x := by
    have hden0 : tailDenom N f (0, x) = 1 := by
      unfold tailDenom
      simp
    refine (ext_coord (fun i ↦ ?_) (fun i hi ↦ ?_)).symm
    · change weight i (f x) = weight i (tailTruncationPt N f hf (0, x))
      rw [weight_tailTruncationPt]
      simp [tailWeight, hden0]
    · change label i (f x) = label i (tailTruncationPt N f hf (0, x))
      refine (label_tailTruncationPt N f hf (z := (0, x)) (i := i) ?_).symm
      simp [tailWeight, hden0, mem_coordSet_iff.mp hi]
  map_one_left _ := rfl

/-- Weight of the fresh-vertex cone homotopy at `z = (s, x)` and index `i`. -/
private def coneWeight (N : ℕ) (g : C(X, MilnorTotalSpace G)) (z : I × X) (i : ℕ) : ℝ :=
  if i = N then (z.1 : ℝ) else (1 - (z.1 : ℝ)) * weight i (g z.2)

/-- Pointwise value of the fresh-vertex cone homotopy at `z = (s, x)`. -/
private def conePt (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) (z : I × X) : MilnorTotalSpace G := by
  let S := (finite_support_weight (g z.2)).toFinset
  have hN_notMem : N ∉ S := fun hmem ↦
    (finite_support_weight (g z.2)).mem_toFinset.mp hmem (hg z.2)
  have hsum_g : ∑ i ∈ S, weight i (g z.2) = 1 :=
    sum_weight_of_support_subset fun i hi ↦ by
      by_contra hne
      exact hi ((finite_support_weight (g z.2)).mem_toFinset.mpr hne)
  exact ofFinsetCoord (insert N S)
    (coneWeight N g z)
    (fun i ↦ if i = N then a else label i (g z.2))
    (fun i _ ↦ by
      unfold coneWeight
      split_ifs
      · exact z.1.2.1
      · exact mul_nonneg (sub_nonneg.mpr z.1.2.2) (weight_nonneg i (g z.2)))
    (by
      unfold coneWeight
      rw [Finset.sum_insert hN_notMem, ite_eq_left rfl,
        Finset.sum_congr rfl fun i hi ↦ ite_eq_right (ne_of_mem_of_not_mem hi hN_notMem),
        ← Finset.mul_sum, hsum_g, mul_one, add_sub_cancel])

private theorem weight_conePt (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) (z : I × X) (i : ℕ) :
    weight i (conePt N a g hg z) = coneWeight N g z i := by
  unfold conePt
  rw [weight_ofFinsetCoord]
  by_cases hiN : i = N
  · simp [hiN]
  · simp only [Finset.mem_insert, hiN, false_or]
    split_ifs with hi
    · rfl
    · have hw0 : weight i (g z.2) = 0 := by
        by_contra hne
        exact hi ((finite_support_weight (g z.2)).mem_toFinset.mpr hne)
      simp [coneWeight, hiN, hw0]

private theorem label_conePt_self (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) {z : I × X} (hs : 0 < (z.1 : ℝ)) :
    label N (conePt N a g hg z) = a := by
  unfold conePt
  have hpos : 0 < coneWeight N g z N := by simp [coneWeight, hs]
  exact (label_ofFinsetCoord _ _ _ _ _ (Finset.mem_insert_self N _) hpos).trans (ite_eq_left rfl)

private theorem label_conePt_of_ne (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) {z : I × X} {i : ℕ} (hiN : i ≠ N)
    (hz : 0 < coneWeight N g z i) :
    label i (conePt N a g hg z) = label i (g z.2) := by
  unfold conePt
  have hw_pos : 0 < weight i (g z.2) := by
    by_contra hle
    have hw0 : weight i (g z.2) = 0 :=
      le_antisymm (not_lt.mp hle) (weight_nonneg i (g z.2))
    simp [coneWeight, hiN, hw0] at hz
  have hmem : i ∈ insert N (finite_support_weight (g z.2)).toFinset :=
    Finset.mem_insert_of_mem ((finite_support_weight (g z.2)).mem_toFinset.mpr hw_pos.ne')
  exact (label_ofFinsetCoord _ _ _ _ _ hmem hz).trans (ite_eq_right hiN)

/-- **Cone homotopy at an unused index.** Any map `g : C(X, MilnorTotalSpace G)` whose `N`-th
weight vanishes everywhere is homotopic to the constant map at `vertex N a` (in particular, to the
identity-labelled vertex `vertex N 1` when `G` has a `1`). -/
def coneAtFreshIndexHomotopy (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) :
    g.Homotopy (ContinuousMap.const X (vertex N a)) where
  toFun := conePt N a g hg
  continuous_toFun := by
    rw [continuous_iff]
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · simp_rw [weight_conePt]
      unfold coneWeight
      by_cases hiN : i = N
      · simp only [hiN, ↓reduceIte]
        exact continuous_subtype_val.comp continuous_fst
      · simp only [hiN, ↓reduceIte]
        fun_prop
    · by_cases hiN : i = N
      · subst hiN
        refine (continuousOn_const (c := a)).congr fun z hz ↦ ?_
        change 0 < weight i (conePt i a g hg z) at hz
        rw [weight_conePt] at hz
        simp only [coneWeight, ↓reduceIte] at hz
        exact label_conePt_self i a g hg hz
      · refine ((continuousOn_label i).comp (g.continuous.comp continuous_snd).continuousOn
          (fun z hz ↦ ?_)).congr fun z hz ↦ ?_
        · change 0 < weight i (conePt N a g hg z) at hz
          rw [weight_conePt] at hz
          rw [mem_coordSet_iff]
          by_contra hle
          have hw0 : weight i (g z.2) = 0 :=
            le_antisymm (not_lt.mp hle) (weight_nonneg i (g z.2))
          simp [coneWeight, hiN, hw0] at hz
        · change 0 < weight i (conePt N a g hg z) at hz
          rw [weight_conePt] at hz
          exact label_conePt_of_ne N a g hg hiN hz
  map_zero_left x := by
    refine (ext_coord (fun i ↦ ?_) (fun i hi ↦ ?_)).symm
    · change weight i (g x) = weight i (conePt N a g hg (0, x))
      rw [weight_conePt]
      by_cases hiN : i = N
      · subst hiN
        simp [coneWeight, hg x]
      · simp [coneWeight, hiN]
    · change label i (g x) = label i (conePt N a g hg (0, x))
      have hiN : i ≠ N := by
        rintro rfl
        exact (mem_coordSet_iff.mp hi).ne' (hg x)
      have hz : 0 < coneWeight N g (0, x) i := by
        simpa [coneWeight, hiN] using mem_coordSet_iff.mp hi
      exact (label_conePt_of_ne N a g hg hiN hz).symm
  map_one_left x := by
    refine ext_coord (fun i ↦ ?_) (fun i hi ↦ ?_)
    · change weight i (conePt N a g hg (1, x)) = weight i (vertex N a)
      rw [weight_conePt, weight_vertex]
      by_cases hiN : i = N <;> simp [coneWeight, hiN]
    · have hi' : 0 < weight i (conePt N a g hg (1, x)) := mem_coordSet_iff.mp hi
      rw [weight_conePt] at hi'
      by_cases hiN : i = N
      · subst hiN
        change label i (conePt i a g hg (1, x)) = label i (vertex i a)
        rw [label_vertex]
        exact label_conePt_self i a g hg zero_lt_one
      · simp [coneWeight, hiN] at hi'

end Homotopies

end MilnorTotalSpace

end TauCeti

namespace ContinuousMap

open TauCeti

variable {X : Type v} [TopologicalSpace X] {G : Type u} [TopologicalSpace G]

/-- **Every continuous map with compact image into `MilnorTotalSpace G` is null-homotopic** when
`G` is nonempty. When `G` has a `1`, the cone vertex can be chosen to be `vertex N 1`. -/
theorem nullhomotopic_to_milnorTotalSpace_of_isCompact_range [Nonempty G]
    {f : C(X, MilnorTotalSpace G)} (hf : IsCompact (Set.range f)) :
    f.Nullhomotopic := by
  obtain ⟨a⟩ := ‹Nonempty G›
  obtain ⟨N, hN⟩ := MilnorTotalSpace.exists_gt_half_partialWeightSum_of_isCompact_range hf
  have hN_pos : ∀ x, 0 < MilnorTotalSpace.partialWeightSum G N (f x) := fun x ↦ by
    linarith [hN x]
  refine ⟨MilnorTotalSpace.vertex N a, ⟨(MilnorTotalSpace.tailTruncationHomotopy N f hN_pos).trans
    (MilnorTotalSpace.coneAtFreshIndexHomotopy N a (MilnorTotalSpace.tailTruncationMap N f hN_pos)
      fun x ↦ MilnorTotalSpace.weight_tailTruncationMap_of_le N f hN_pos le_rfl x)⟩⟩

/-- **Every continuous map from a compact space into `MilnorTotalSpace G` is null-homotopic** when
`G` is nonempty. -/
theorem nullhomotopic_to_milnorTotalSpace [CompactSpace X] [Nonempty G]
    (f : C(X, MilnorTotalSpace G)) :
    f.Nullhomotopic :=
  nullhomotopic_to_milnorTotalSpace_of_isCompact_range (isCompact_range f.continuous)

end ContinuousMap

namespace TauCeti

section ConnectivityAndHomotopyGroups

variable (G : Type u) [TopologicalSpace G]

/-- `MilnorTotalSpace G` is path connected whenever `G` is nonempty. -/
instance instPathConnectedSpaceMilnorTotalSpace [Nonempty G] :
    PathConnectedSpace (MilnorTotalSpace G) where
  nonempty := inferInstance
  joined x y := by
    let f : C(Bool, MilnorTotalSpace G) :=
      ⟨fun b ↦ if b then y else x, continuous_of_discreteTopology⟩
    obtain ⟨c, ⟨H⟩⟩ := ContinuousMap.nullhomotopic_to_milnorTotalSpace f
    exact ⟨(H.evalAt false).trans (H.evalAt true).symm⟩

/-- `MilnorClassifyingSpace G` is path connected for every topological group `G`. -/
instance instPathConnectedSpaceMilnorClassifyingSpace [Group G] :
    PathConnectedSpace (MilnorClassifyingSpace G) :=
  (milnorClassifyingSpaceProj_surjective G).pathConnectedSpace
    (continuous_milnorClassifyingSpaceProj G)

/-- `MilnorTotalSpace G` is simply connected whenever `G` is nonempty. -/
instance instSimplyConnectedSpaceMilnorTotalSpace [Nonempty G] :
    SimplyConnectedSpace (MilnorTotalSpace G) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun x γ ↦ ?_⟩
  refine Path.Homotopic.refl_of_forall_mem_of_nullhomotopic
    (ContinuousMap.nullhomotopic_to_milnorTotalSpace_of_isCompact_range ?_) γ Set.mem_range_self
  rw [ContinuousMap.coe_mk, Subtype.range_coe]
  exact isCompact_range γ.continuous

end ConnectivityAndHomotopyGroups

end TauCeti

namespace HomotopyGroup

open TauCeti

/-- **Weak contractibility of `MilnorTotalSpace G`.** Every homotopy group (and zeroth homotopy
set) `HomotopyGroup N (MilnorTotalSpace G) x` vanishes for arbitrary index types `N`. -/
instance subsingleton_milnorTotalSpace
    {G : Type u} [TopologicalSpace G] (N : Type*) (x : MilnorTotalSpace G) :
    Subsingleton (HomotopyGroup N (MilnorTotalSpace G) x) := by
  classical
  have : Nonempty G := MilnorTotalSpace.nonempty_of_milnorTotalSpace x
  by_cases hfin : Finite N
  · by_cases hemp : IsEmpty N
    · have : Subsingleton (ZerothHomotopy (MilnorTotalSpace G)) :=
        (pathConnectedSpace_iff_zerothHomotopy.mp inferInstance).2
      exact (homotopyGroupEquivZerothHomotopyOfIsEmpty N x).subsingleton
    · have : Nonempty N := not_isEmpty_iff.mp hemp
      let _ : Fintype N := Fintype.ofFinite N
      have h_one (a : HomotopyGroup N (MilnorTotalSpace G) x) : a = 1 := by
        induction a using Quotient.inductionOn with | h p =>
        have hp : IsCompact (Set.range (Subtype.val : Set.range p → MilnorTotalSpace G)) := by
          rw [Subtype.range_coe]
          exact isCompact_range p.1.continuous
        obtain ⟨g, hg⟩ := one_mem_orbit_of_forall_mem_of_nullhomotopic
          (ContinuousMap.nullhomotopic_to_milnorTotalSpace_of_isCompact_range hp) p
          Set.mem_range_self
        exact (fundamentalGroup_smul_eq_self g _).symm.trans hg
      exact ⟨fun a b ↦ (h_one a).trans (h_one b).symm⟩
  · have : Infinite N := not_finite_iff_infinite.mp hfin
    infer_instance

end HomotopyGroup

namespace TauCeti

/-! ### Sphere null-extension and based null-homotopy comparisons -/

section SphereExtension

variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {G : Type u} [TopologicalSpace G]

/-- **Every continuous map from the unit sphere of a proper real seminormed space into
`MilnorTotalSpace G` extends continuously over the closed unit ball** when `G` is nonempty. -/
theorem exists_extension_closedBall_milnorTotalSpace [Nonempty G]
    (g : C(sphere (0 : E) 1, MilnorTotalSpace G)) :
    ∃ G' : C(closedBall (0 : E) 1, MilnorTotalSpace G),
      ∀ y : sphere (0 : E) 1, G' ⟨y, sphere_subset_closedBall y.2⟩ = g y :=
  g.nullhomotopic_iff_exists_extension_closedBall.mp g.nullhomotopic_to_milnorTotalSpace

/-- **Based null-homotopy on unit spheres.** Every continuous map from the unit sphere of a proper
real seminormed space into `MilnorTotalSpace G` is homotopic relative to `{s₀}` to the constant map
at `g s₀`. -/
theorem homotopicRel_const_singleton_sphere_milnorTotalSpace
    (g : C(sphere (0 : E) 1, MilnorTotalSpace G)) (s₀ : sphere (0 : E) 1) :
    g.HomotopicRel (ContinuousMap.const _ (g s₀)) {s₀} := by
  have : Nonempty G := MilnorTotalSpace.nonempty_of_milnorTotalSpace (g s₀)
  exact (g.homotopicRel_const_singleton_sphere_iff_nullhomotopic s₀).mpr
    g.nullhomotopic_to_milnorTotalSpace

end SphereExtension

end TauCeti
