/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.PartitionOfUnity
public import TauCeti.Topology.Homotopy.HurewiczFibration.Basic
import TauCeti.Topology.LocallyFinite.Basic
import TauCeti.Topology.Order.Lattice
import TauCeti.Topology.PartitionOfUnity.Gap
import TauCeti.Topology.PartitionOfUnity.Shrink
import TauCeti.Topology.Semicontinuity.CompactInfimum

/-!
# Local-to-global homotopy lifting over numerable covers

Dold's local-to-global theorem for fibrations: let `p : E → B` be a continuous map and
`(U i)_{i ∈ ι}` a numerable cover of `B`, meaning there exists a locally finite partition of unity
`ρ : PartitionOfUnity ι B` with `support (ρ i) ⊆ U i` for all `i`. If for a space `A` each
restriction `p ⁻¹' U i → U i` has the homotopy lifting property with respect to every open subset
of `A`, then `p` has the homotopy lifting property globally with respect to `A`
(`TauCeti.HasHomotopyLiftingProperty.of_partitionOfUnity`).

In particular, if each restriction `p ⁻¹' U i → U i` is a Hurewicz fibration, then `p` is a
Hurewicz fibration (`TauCeti.isHurewiczFibration_of_partitionOfUnity`), with no separation,
countability or paracompactness assumption on the test spaces. Over a normal paracompact base
(which includes every paracompact Hausdorff base via Mathlib's `NormalSpace` instance), any open
cover is numerable, so a map that is locally a Hurewicz fibration over an open cover is globally a
Hurewicz fibration (`TauCeti.isHurewiczFibration_of_isOpenCover`).

## Implementation notes

Given a homotopy `H : C(I × A, B)` starting at `p ∘ f` on a nonempty space `A`:

1. For each subdivision number `m + 1` and tuple `α : Fin (m + 1) → ι`, define the tube weight
   `η m α a = ⨅ k, ⨅ t ∈ [k/(m+1), (k+1)/(m+1)], ρ (α k) (H (t, a))`. Compactness of the segments
   makes `η m α` continuous, and the Lebesgue number lemma on `I` supplies a positive weight at each
   `a : A`.
2. Truncating `η m α a` by `(m : ℝ) * ∑_{j < m} sup_β η j β a` produces a single locally finite
   nonnegative family positive at every point of `A`, normalized via `PartitionOfUnity.ofExistsPos`
   to a partition of unity `ν` on `A`.
3. Applying `PartitionOfUnity.gapPartition` and `PartitionOfUnity.shrink` yields a countable
   partition of unity `μ : PartitionOfUnity ℕ A` whose `n`-th closed support lies inside the union
   of the pairwise disjoint open gap strata `{a | 0 < ν.gap E a}` with `#E = n`.
4. Stepping along the cumulative sums `τ n a = ∑_{j < n} μ j a` lifts `H` up to time `τ n` by
   finitely many local lifts on each gap stratum; local finiteness of `μ` makes the sequence of
   partial lifts locally stationary near every point of `A`.

## Main results

* `TauCeti.HasHomotopyLiftingProperty.of_partitionOfUnity`: Dold's local-to-global homotopy lifting
  theorem over a numerable cover.
* `TauCeti.HasHomotopyLiftingProperty.of_isOpenCover`: local-to-global homotopy lifting over an open
  cover of a normal paracompact base.
* `TauCeti.isHurewiczFibration_of_partitionOfUnity`: a continuous map locally a Hurewicz fibration
  over a numerable cover is a Hurewicz fibration.
* `TauCeti.isHurewiczFibration_of_isSubordinate`: convenience form for closed-support subordination
  `ρ.IsSubordinate U`.
* `TauCeti.isHurewiczFibration_of_isOpenCover`: a continuous map locally a Hurewicz fibration over
  an open cover of a normal paracompact base is a Hurewicz fibration.

## References

* A. Dold, *Partitions of unity in the theory of fibrations*, Ann. of Math. (2) 78 (1963),
  223–255, Theorem 4.8.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Theorem 4.42.
-/

public section

open Function Set Filter Topology unitInterval

universe w u v

namespace TauCeti

section UniformSegments

private noncomputable def segEndpt (m : ℕ) (j : Fin (m + 2)) : I :=
  ⟨(j : ℝ) / (m + 1 : ℝ),
    ⟨by positivity,
      div_le_one_of_le₀ (by exact_mod_cast Nat.le_of_lt_succ j.2) (by positivity)⟩⟩

private theorem segEndpt_zero (m : ℕ) : segEndpt m 0 = 0 := by
  apply Subtype.ext
  simp [segEndpt]

private theorem segEndpt_last (m : ℕ) : segEndpt m (Fin.last (m + 1)) = 1 := by
  apply Subtype.ext
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  simp [segEndpt, div_self hm]

private theorem segEndpt_mono (m : ℕ) : Monotone (segEndpt m) := fun _ _ hj ↦
  Subtype.mk_le_mk.2 (div_le_div_of_nonneg_right (by exact_mod_cast hj) (by positivity))

private theorem segEndpt_sub (m : ℕ) (k : Fin (m + 1)) :
    (segEndpt m k.succ : ℝ) - (segEndpt m k.castSucc : ℝ) = 1 / (m + 1 : ℝ) := by
  simp only [segEndpt, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

private instance instNonemptySeg (m : ℕ) (k : Fin (m + 1)) :
    Nonempty (Icc (segEndpt m k.castSucc) (segEndpt m k.succ)) :=
  (nonempty_Icc.2 (segEndpt_mono m k.castSucc_le_succ)).to_subtype

end UniformSegments

section TubePartition

variable {ι : Type*} {B : Type v} {A : Type w} [TopologicalSpace B] [TopologicalSpace A]

private noncomputable def tubeWeight (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (m : ℕ) (α : Fin (m + 1) → ι) : C(A, ℝ) :=
  ⟨fun a ↦ ⨅ k : Fin (m + 1),
      ⨅ t : Icc (segEndpt m k.castSucc) (segEndpt m k.succ), ρ (α k) (H (t.1, a)),
    TauCeti.continuous_ciInf_of_finite fun k ↦
      (by fun_prop : Continuous fun p : Icc (segEndpt m k.castSucc) (segEndpt m k.succ) × A ↦
        ρ (α k) (H (p.1.1, p.2))).iInf_of_compactSpace⟩

private theorem tubeWeight_apply (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (m : ℕ) (α : Fin (m + 1) → ι) (a : A) :
    tubeWeight ρ H m α a = ⨅ k : Fin (m + 1),
      ⨅ t : Icc (segEndpt m k.castSucc) (segEndpt m k.succ), ρ (α k) (H (t.1, a)) :=
  rfl

private theorem tubeWeight_nonneg (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (m : ℕ) (α : Fin (m + 1) → ι) (a : A) :
    0 ≤ tubeWeight ρ H m α a := by
  rw [tubeWeight_apply]
  exact le_ciInf fun k ↦ le_ciInf fun t ↦ ρ.nonneg (α k) (H (t.1, a))

private theorem tubeWeight_le_apply (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (m : ℕ) (α : Fin (m + 1) → ι) (a : A) (k : Fin (m + 1))
    {t : I} (ht : t ∈ Icc (segEndpt m k.castSucc) (segEndpt m k.succ)) :
    tubeWeight ρ H m α a ≤ ρ (α k) (H (t, a)) := by
  rw [tubeWeight_apply]
  have hbdd₁ : BddBelow (range fun k' : Fin (m + 1) ↦
      ⨅ s : Icc (segEndpt m k'.castSucc) (segEndpt m k'.succ), ρ (α k') (H (s.1, a))) :=
    (finite_range _).bddBelow
  have hbdd₂ : BddBelow (range fun s : Icc (segEndpt m k.castSucc) (segEndpt m k.succ) ↦
      ρ (α k) (H (s.1, a))) :=
    ⟨0, forall_mem_range.2 fun s ↦ ρ.nonneg (α k) (H (s.1, a))⟩
  exact (ciInf_le hbdd₁ k).trans (ciInf_le hbdd₂ ⟨t, ht⟩)

private theorem tubeWeight_le_one (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (m : ℕ) (α : Fin (m + 1) → ι) (a : A) :
    tubeWeight ρ H m α a ≤ 1 :=
  (tubeWeight_le_apply ρ H m α a 0
    (left_mem_Icc.2 (segEndpt_mono m (Fin.castSucc_le_succ 0)))).trans (ρ.le_one _ _)

private theorem pos_of_tubeWeight_pos {ρ : PartitionOfUnity ι B} {H : C(I × A, B)}
    {m : ℕ} {α : Fin (m + 1) → ι} {a : A} (h : 0 < tubeWeight ρ H m α a)
    (k : Fin (m + 1)) {t : I} (ht : t ∈ Icc (segEndpt m k.castSucc) (segEndpt m k.succ)) :
    0 < ρ (α k) (H (t, a)) :=
  h.trans_le (tubeWeight_le_apply ρ H m α a k ht)

private theorem exists_tubeWeight_pos (ρ : PartitionOfUnity ι B) (H : C(I × A, B)) (a : A) :
    ∃ (m : ℕ) (α : Fin (m + 1) → ι), 0 < tubeWeight ρ H m α a := by
  let V : ι → Set I := fun i ↦ {t : I | 0 < ρ i (H (t, a))}
  have hV_open : ∀ i, IsOpen (V i) := fun i ↦ isOpen_lt continuous_const (by fun_prop)
  have hV_cov : (univ : Set I) ⊆ ⋃ i, V i := fun t _ ↦
    mem_iUnion.2 (ρ.exists_pos (mem_univ (H (t, a))))
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV_open hV_cov
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  have hseg : ∀ k : Fin (m + 1), ∃ i,
      Icc (segEndpt m k.castSucc) (segEndpt m k.succ) ⊆ V i := fun k ↦ by
    obtain ⟨i, hi⟩ := hball (segEndpt m k.castSucc) (mem_univ _)
    refine ⟨i, fun t ht ↦ hi ?_⟩
    have ht1 : (segEndpt m k.castSucc : ℝ) ≤ t := ht.1
    have ht2 : (t : ℝ) ≤ segEndpt m k.succ := ht.2
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 ht1)]
    exact ((sub_le_sub_right ht2 _).trans_eq (segEndpt_sub m k)).trans_lt hm
  choose α hα using hseg
  refine ⟨m, α, ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin (m + 1) ↦
    ⨅ t : Icc (segEndpt m k.castSucc) (segEndpt m k.succ), ρ (α k) (H (t.1, a)))
  rw [tubeWeight_apply, ← hk₀]
  exact (Continuous.lowerSemicontinuous (by fun_prop)).lt_ciInf_iff.2 fun t ↦ hα k₀ t.2

private theorem exists_nhds_finset_support (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (a₀ : A) :
    ∃ F : Finset ι, ∀ᶠ a in 𝓝 a₀, ∀ t : I, support (fun i ↦ ρ i (H (t, a))) ⊆ F := by
  classical
  have hlf : LocallyFinite fun i ↦ H ⁻¹' support (ρ i) :=
    ρ.locallyFinite.preimage_continuous H.continuous
  obtain ⟨W, hW, hfin⟩ := hlf.exists_mem_nhdsSet_finite (isCompact_univ.prod isCompact_singleton)
  have hsub : (univ : Set I) ×ˢ ({a₀} : Set A) ⊆ interior W :=
    fun z hz ↦ mem_interior_iff_mem_nhds.2 (mem_nhdsSet_iff_forall.1 hW z hz)
  obtain ⟨U₁, U₂, -, hU₂, hU₁, ha₀, hprod⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton isOpen_interior hsub
  refine ⟨hfin.toFinset, Filter.eventually_of_mem (hU₂.mem_nhds (ha₀ rfl)) fun a ha t i hi ↦ ?_⟩
  exact hfin.mem_toFinset.2 ⟨(t, a), hi, interior_subset (hprod ⟨hU₁ (mem_univ t), ha⟩)⟩

private noncomputable def levelMax (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (m : ℕ) (a : A) : ℝ :=
  ⨆ α : Fin (m + 1) → ι, tubeWeight ρ H m α a

private theorem levelMax_nonneg (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (m : ℕ) (a : A) :
    0 ≤ levelMax ρ H m a :=
  Real.iSup_nonneg fun α ↦ tubeWeight_nonneg ρ H m α a

private theorem le_levelMax (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (m : ℕ) (α : Fin (m + 1) → ι) (a : A) :
    tubeWeight ρ H m α a ≤ levelMax ρ H m a :=
  le_ciSup ⟨1, forall_mem_range.2 fun β ↦ tubeWeight_le_one ρ H m β a⟩ α

private theorem levelMax_eq_of_support_subset {ρ : PartitionOfUnity ι B}
    {H : C(I × A, B)} {F : Finset ι} {a : A}
    (hF : ∀ t : I, support (fun i ↦ ρ i (H (t, a))) ⊆ F) (m : ℕ) :
    levelMax ρ H m a = ⨆ α : Fin (m + 1) → F, tubeWeight ρ H m (fun k ↦ (α k).1) a := by
  have hnonneg : 0 ≤ ⨆ α : Fin (m + 1) → F, tubeWeight ρ H m (fun k ↦ (α k).1) a :=
    Real.iSup_nonneg fun α ↦ tubeWeight_nonneg ρ H m _ a
  refine le_antisymm (Real.iSup_le (fun α ↦ ?_) hnonneg)
    (Real.iSup_le (fun α ↦ le_levelMax ρ H m _ a) (levelMax_nonneg ρ H m a))
  by_cases hα : ∀ k, α k ∈ F
  · exact le_ciSup (finite_range (fun β : Fin (m + 1) → F ↦
      tubeWeight ρ H m (fun k ↦ (β k).1) a)).bddAbove fun k ↦ ⟨α k, hα k⟩
  · push Not at hα
    obtain ⟨k, hk⟩ := hα
    have hzero : ρ (α k) (H (segEndpt m k.castSucc, a)) = 0 :=
      by_contra fun hne ↦ hk (hF _ hne)
    exact ((tubeWeight_le_apply ρ H m α a k
      (left_mem_Icc.2 (segEndpt_mono m k.castSucc_le_succ))).trans_eq hzero).trans hnonneg

private theorem continuous_levelMax (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (m : ℕ) :
    Continuous (levelMax ρ H m) := by
  refine continuous_iff_continuousAt.2 fun a₀ ↦ ?_
  obtain ⟨F, hF⟩ := exists_nhds_finset_support ρ H a₀
  have hcont : Continuous fun a ↦
      ⨆ α : Fin (m + 1) → F, tubeWeight ρ H m (fun k ↦ (α k).1) a :=
    TauCeti.continuous_ciSup_of_finite fun α ↦ (tubeWeight ρ H m _).continuous
  exact hcont.continuousAt.congr (hF.mono fun a ha ↦ (levelMax_eq_of_support_subset ha m).symm)

private noncomputable def truncTubeWeight (ρ : PartitionOfUnity ι B)
    (H : C(I × A, B)) (idx : Σ m : ℕ, Fin (m + 1) → ι) : C(A, ℝ) :=
  ⟨fun a ↦ max 0 (tubeWeight ρ H idx.1 idx.2 a -
      (idx.1 : ℝ) * ∑ j ∈ Finset.range idx.1, levelMax ρ H j a),
    have := continuous_levelMax ρ H
    by fun_prop⟩

private theorem truncTubeWeight_apply (ρ : PartitionOfUnity ι B)
    (H : C(I × A, B)) (idx : Σ m : ℕ, Fin (m + 1) → ι) (a : A) :
    truncTubeWeight ρ H idx a = max 0 (tubeWeight ρ H idx.1 idx.2 a -
      (idx.1 : ℝ) * ∑ j ∈ Finset.range idx.1, levelMax ρ H j a) :=
  rfl

private theorem truncTubeWeight_nonneg (ρ : PartitionOfUnity ι B) (H : C(I × A, B))
    (idx : Σ m : ℕ, Fin (m + 1) → ι) (a : A) :
    0 ≤ truncTubeWeight ρ H idx a :=
  le_max_left _ _

private theorem tubeWeight_pos_of_truncTubeWeight_pos {ρ : PartitionOfUnity ι B}
    {H : C(I × A, B)} {idx : Σ m : ℕ, Fin (m + 1) → ι} {a : A}
    (h : 0 < truncTubeWeight ρ H idx a) :
    0 < tubeWeight ρ H idx.1 idx.2 a := by
  have hpos := (lt_max_iff.1 h).resolve_left (lt_irrefl 0)
  have hsum : 0 ≤ (idx.1 : ℝ) * ∑ j ∈ Finset.range idx.1, levelMax ρ H j a :=
    mul_nonneg idx.1.cast_nonneg (Finset.sum_nonneg fun j _ ↦ levelMax_nonneg ρ H j a)
  linarith

private theorem exists_truncTubeWeight_pos (ρ : PartitionOfUnity ι B)
    (H : C(I × A, B)) (a : A) :
    ∃ idx : Σ m : ℕ, Fin (m + 1) → ι, 0 < truncTubeWeight ρ H idx a := by
  classical
  have hex : ∃ m : ℕ, ∃ α : Fin (m + 1) → ι, 0 < tubeWeight ρ H m α a :=
    exists_tubeWeight_pos ρ H a
  let m₀ := Nat.find hex
  obtain ⟨α₀, hα₀⟩ := Nat.find_spec hex
  have hsum : ∑ j ∈ Finset.range m₀, levelMax ρ H j a = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ le_antisymm ?_ (levelMax_nonneg ρ H j a)
    refine Real.iSup_le (fun β ↦ ?_) le_rfl
    by_contra hpos
    exact Nat.find_min hex (Finset.mem_range.1 hj) ⟨β, not_le.1 hpos⟩
  refine ⟨⟨m₀, α₀⟩, ?_⟩
  rw [truncTubeWeight_apply, hsum, mul_zero, sub_zero,
    max_eq_right (tubeWeight_nonneg ρ H m₀ α₀ a)]
  exact hα₀

private theorem locallyFinite_truncTubeWeight (ρ : PartitionOfUnity ι B)
    (H : C(I × A, B)) :
    LocallyFinite fun idx ↦ support (truncTubeWeight ρ H idx) := by
  classical
  intro a₀
  obtain ⟨m₀, α₀, hm₀⟩ := exists_tubeWeight_pos ρ H a₀
  have hM_pos : 0 < levelMax ρ H m₀ a₀ := hm₀.trans_le (le_levelMax ρ H m₀ α₀ a₀)
  let c : ℝ := levelMax ρ H m₀ a₀ / 2
  have hc : 0 < c := half_pos hM_pos
  have hW₁ : ∀ᶠ a in 𝓝 a₀, c < levelMax ρ H m₀ a :=
    (continuous_levelMax ρ H m₀).continuousAt.eventually (Ioi_mem_nhds (half_lt_self hM_pos))
  obtain ⟨F, hW₂⟩ := exists_nhds_finset_support ρ H a₀
  let N : ℕ := max (m₀ + 1) (⌈1 / c⌉₊ + 1)
  let S : Finset (Σ m : ℕ, Fin (m + 1) → ι) :=
    (Finset.range N).sigma fun m ↦ Fintype.piFinset fun _ : Fin (m + 1) ↦ F
  refine ⟨{a | c < levelMax ρ H m₀ a ∧ ∀ t : I, support (fun i ↦ ρ i (H (t, a))) ⊆ F},
    hW₁.and hW₂, S.finite_toSet.subset ?_⟩
  rintro ⟨m, α⟩ ⟨a, hne, hc_lt, hF⟩
  have hpos : 0 < truncTubeWeight ρ H ⟨m, α⟩ a :=
    lt_of_le_of_ne (truncTubeWeight_nonneg ρ H ⟨m, α⟩ a) (Ne.symm hne)
  have hη_pos : 0 < tubeWeight ρ H m α a := tubeWeight_pos_of_truncTubeWeight_pos hpos
  have hmN : m < N := by
    by_contra hm_ge
    have hm_le : N ≤ m := not_lt.1 hm_ge
    have hm₀_lt : m₀ < m := (Nat.lt_succ_self m₀).trans_le ((le_max_left _ _).trans hm_le)
    have hsum_ge : c ≤ ∑ j ∈ Finset.range m, levelMax ρ H j a :=
      hc_lt.le.trans <| Finset.single_le_sum (fun j _ ↦ levelMax_nonneg ρ H j a)
        (Finset.mem_range.2 hm₀_lt)
    have hNc : 1 ≤ (N : ℝ) * c := by
      have hceil : 1 / c ≤ ⌈1 / c⌉₊ := Nat.le_ceil (1 / c)
      have hN_ge : (⌈1 / c⌉₊ : ℝ) ≤ N := by exact_mod_cast (Nat.le_succ _).trans (le_max_right _ _)
      linarith [(div_le_iff₀ hc).1 (hceil.trans hN_ge)]
    have hm_cast : (N : ℝ) ≤ m := by exact_mod_cast hm_le
    have hmul : 1 ≤ (m : ℝ) * ∑ j ∈ Finset.range m, levelMax ρ H j a :=
      hNc.trans (mul_le_mul hm_cast hsum_ge hc.le m.cast_nonneg)
    have hsub := (lt_max_iff.1 hpos).resolve_left (lt_irrefl 0)
    linarith [tubeWeight_le_one ρ H m α a]
  refine Finset.mem_coe.2 (Finset.mem_sigma.2 ⟨Finset.mem_range.2 hmN, ?_⟩)
  exact Fintype.mem_piFinset.2 fun k ↦ hF (segEndpt m k.castSucc)
    (pos_of_tubeWeight_pos hη_pos k (left_mem_Icc.2 (segEndpt_mono m k.castSucc_le_succ))).ne'

private noncomputable def tubePartition (ρ : PartitionOfUnity ι B)
    (H : C(I × A, B)) : PartitionOfUnity (Σ m : ℕ, Fin (m + 1) → ι) A :=
  PartitionOfUnity.ofExistsPos (truncTubeWeight ρ H) (locallyFinite_truncTubeWeight ρ H)
    (truncTubeWeight_nonneg ρ H) (exists_truncTubeWeight_pos ρ H)

end TubePartition

section PartialLift

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- A partial homotopy lift of `H` along `p` starting at `f`, valid up to the continuous stopping
time `τ` and constant in time after `τ`. -/
private structure PartialLift {X : Type*} [TopologicalSpace X]
    (p : E → B) (f : C(X, E)) (H : C(I × X, B)) (τ : C(X, I)) where
  map : C(I × X, E)
  proj_eq : ∀ t x, p (map (t, x)) = H (min t (τ x), x)
  zero_eq : ∀ x, map (0, x) = f x
  const_of_ge : ∀ t x, τ x ≤ t → map (t, x) = map (τ x, x)

private def PartialLift.congrTime {X : Type*} [TopologicalSpace X] {p : E → B}
    {f : C(X, E)} {H : C(I × X, B)} {τ₁ τ₂ : C(X, I)}
    (L : PartialLift p f H τ₁) (h : ∀ x, τ₁ x = τ₂ x) :
    PartialLift p f H τ₂ where
  map := L.map
  proj_eq t x := by rw [L.proj_eq, h x]
  zero_eq := L.zero_eq
  const_of_ge t x ht := by rw [← h x]; exact L.const_of_ge t x (h x ▸ ht)

private def PartialLift.initial {X : Type*} [TopologicalSpace X] {p : E → B}
    (f : C(X, E)) (H : C(I × X, B)) (hH : ∀ x, H (0, x) = p (f x)) :
    PartialLift p f H (.const X 0) where
  map := ⟨fun z ↦ f z.2, by fun_prop⟩
  proj_eq t x := by
    rw [ContinuousMap.coe_mk, ContinuousMap.const_apply, min_eq_right unitInterval.nonneg', hH x]
  zero_eq _ := rfl
  const_of_ge _ _ _ := rfl

private def restrictHomotopy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : C(I × X, Y)) (S : Set X) : C(I × S, Y) :=
  ⟨fun z ↦ H (z.1, z.2.1), by fun_prop⟩

@[simp]
private theorem restrictHomotopy_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : C(I × X, Y)) (S : Set X) (t : I) (x : S) :
    restrictHomotopy H S (t, x) = H (t, x.1) :=
  rfl

private def PartialLift.restrict {X : Type*} [TopologicalSpace X] {p : E → B}
    {f : C(X, E)} {H : C(I × X, B)} {τ : C(X, I)} (L : PartialLift p f H τ) (S : Set X) :
    PartialLift p (f.restrict S) (restrictHomotopy H S) (τ.restrict S) where
  map := restrictHomotopy L.map S
  proj_eq t x := L.proj_eq t x.1
  zero_eq x := L.zero_eq x.1
  const_of_ge t x h := L.const_of_ge t x.1 h

/-- Extend a `PartialLift` defined on an open neighbourhood `O` of `closure {x | τ₁ x < τ₂ x}`
to `X` by keeping `L` outside `O`. -/
private theorem PartialLift.extendFromOpen {X : Type*} [TopologicalSpace X] {p : E → B}
    {f : C(X, E)} {H : C(I × X, B)} {τ₁ τ₂ : C(X, I)} (hτ : ∀ x, τ₁ x ≤ τ₂ x)
    (L : PartialLift p f H τ₁) {O : Set X} (hO : IsOpen O)
    (hclos : closure {x : X | τ₁ x < τ₂ x} ⊆ O)
    (LO : PartialLift p (f.restrict O) (restrictHomotopy H O) (τ₂.restrict O))
    (hLO : ∀ (t : I) (x : O), τ₁ x.1 = τ₂ x.1 → LO.map (t, x) = L.map (t, x.1)) :
    ∃ L' : PartialLift p f H τ₂,
      ∀ t x, τ₁ x = τ₂ x → L'.map (t, x) = L.map (t, x) := by
  classical
  let raw (z : I × X) : E :=
    if hz : z.2 ∈ O then LO.map (z.1, ⟨z.2, hz⟩) else L.map z
  have hraw_pos : ∀ (t : I) {x : X} (hx : x ∈ O), raw (t, x) = LO.map (t, ⟨x, hx⟩) := by
    intro t x hx; dsimp only [raw]; split_ifs; rfl
  have hraw_neg : ∀ (t : I) {x : X} (hx : x ∉ O), raw (t, x) = L.map (t, x) := by
    intro t x hx; dsimp only [raw]; split_ifs; rfl
  have hraw_eq_of_eq : ∀ t x, τ₁ x = τ₂ x → raw (t, x) = L.map (t, x) := fun t x heq ↦ by
    by_cases hx : x ∈ O
    · rw [hraw_pos t hx]; exact hLO t ⟨x, hx⟩ heq
    · exact hraw_neg t hx
  have heq_of_notMem : ∀ {x : X}, x ∉ O → τ₁ x = τ₂ x := fun {x} hx ↦
    le_antisymm (hτ x) (not_lt.1 fun hlt ↦ hx (hclos (subset_closure hlt)))
  have hraw_cont : Continuous raw := by
    refine continuous_iff_continuousAt.2 fun ⟨t₀, x₀⟩ ↦ ?_
    by_cases hx₀ : x₀ ∈ O
    · have hOn : ContinuousOn raw (univ ×ˢ O) :=
        continuousOn_iff_continuous_domRestrict.2 <|
          (by fun_prop : Continuous fun z : univ ×ˢ O ↦ LO.map (z.1.1, ⟨z.1.2, z.2.2⟩)).congr
            fun z ↦ (hraw_pos z.1.1 z.2.2).symm
      exact hOn.continuousAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t₀, hx₀⟩)
    · have hx₀_compl : x₀ ∈ (closure {x : X | τ₁ x < τ₂ x})ᶜ := fun hmem ↦ hx₀ (hclos hmem)
      have hopen_compl : IsOpen ((univ : Set I) ×ˢ (closure {x : X | τ₁ x < τ₂ x})ᶜ) :=
        isOpen_univ.prod isClosed_closure.isOpen_compl
      refine L.map.continuous.continuousAt.congr
        (Filter.eventually_of_mem (hopen_compl.mem_nhds ⟨mem_univ t₀, hx₀_compl⟩) fun z hz ↦ ?_)
      exact (hraw_eq_of_eq z.1 z.2
        (le_antisymm (hτ z.2) (not_lt.1 fun hlt ↦ hz.2 (subset_closure hlt)))).symm
  refine ⟨{
    map := ⟨raw, hraw_cont⟩
    proj_eq := fun t x ↦ by
      rw [ContinuousMap.coe_mk]
      by_cases hx : x ∈ O
      · rw [hraw_pos t hx, LO.proj_eq]; rfl
      · have heq := heq_of_notMem hx
        rw [hraw_eq_of_eq t x heq, L.proj_eq, heq]
    zero_eq := fun x ↦ by
      rw [ContinuousMap.coe_mk]
      by_cases hx : x ∈ O
      · rw [hraw_pos 0 hx, LO.zero_eq]; rfl
      · rw [hraw_neg 0 hx, L.zero_eq]
    const_of_ge := fun t x ht ↦ by
      rw [ContinuousMap.coe_mk]
      by_cases hx : x ∈ O
      · rw [hraw_pos t hx, hraw_pos (τ₂ x) hx]
        exact LO.const_of_ge t ⟨x, hx⟩ ht
      · have heq := heq_of_notMem hx
        rw [hraw_eq_of_eq t x heq, hraw_eq_of_eq (τ₂ x) x heq, ← heq]
        exact L.const_of_ge t x (heq ▸ ht)
  }, hraw_eq_of_eq⟩

private def stepTime {X : Type*} [TopologicalSpace X] (τ₁ τ₂ : C(X, I)) : C(I × X, I) :=
  ⟨fun z ↦ ⟨min (τ₂ z.2 : ℝ) ((τ₁ z.2 : ℝ) + (z.1 : ℝ)),
      ⟨le_min (τ₂ z.2).2.1 (add_nonneg (τ₁ z.2).2.1 z.1.2.1),
        (min_le_left _ _).trans (τ₂ z.2).2.2⟩⟩,
    by fun_prop⟩

@[simp]
private theorem coe_stepTime {X : Type*} [TopologicalSpace X] (τ₁ τ₂ : C(X, I)) (s : I) (x : X) :
    (stepTime τ₁ τ₂ (s, x) : ℝ) = min (τ₂ x : ℝ) ((τ₁ x : ℝ) + (s : ℝ)) :=
  rfl

private theorem stepTime_mem_Icc {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    (hτ : ∀ x, τ₁ x ≤ τ₂ x) (s : I) (x : X) :
    stepTime τ₁ τ₂ (s, x) ∈ Icc (τ₁ x) (τ₂ x) :=
  ⟨le_min (hτ x) (le_add_of_nonneg_right s.2.1), min_le_left _ _⟩

private theorem stepTime_zero {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    (hτ : ∀ x, τ₁ x ≤ τ₂ x) (x : X) :
    stepTime τ₁ τ₂ (0, x) = τ₁ x := by
  ext
  have hle : (τ₁ x : ℝ) ≤ τ₂ x := hτ x
  simp [hle]

private def stepOffset {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    (hτ : ∀ x, τ₁ x ≤ τ₂ x) : C(I × X, I) :=
  ⟨fun z ↦ ⟨max (τ₁ z.2 : ℝ) (min (τ₂ z.2 : ℝ) (z.1 : ℝ)) - (τ₁ z.2 : ℝ),
      ⟨sub_nonneg.2 (le_max_left _ _), by
        have h1 : max (τ₁ z.2 : ℝ) (min (τ₂ z.2 : ℝ) (z.1 : ℝ)) ≤ τ₂ z.2 :=
          max_le (hτ z.2) (min_le_left _ _)
        linarith [(τ₁ z.2).2.1, (τ₂ z.2).2.2]⟩⟩,
    by fun_prop⟩

@[simp]
private theorem coe_stepOffset {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    (hτ : ∀ x, τ₁ x ≤ τ₂ x) (t : I) (x : X) :
    (stepOffset hτ (t, x) : ℝ) = max (τ₁ x : ℝ) (min (τ₂ x : ℝ) (t : ℝ)) - (τ₁ x : ℝ) :=
  rfl

private theorem stepOffset_eq_zero_of_le {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    (hτ : ∀ x, τ₁ x ≤ τ₂ x) {t : I} {x : X} (ht : t ≤ τ₁ x) :
    stepOffset hτ (t, x) = 0 := by
  ext
  simp [max_eq_left ((min_le_right (τ₂ x : ℝ) (t : ℝ)).trans ht)]

private theorem stepOffset_eq_zero_of_eq {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    (hτ : ∀ x, τ₁ x ≤ τ₂ x) (t : I) {x : X} (heq : τ₁ x = τ₂ x) :
    stepOffset hτ (t, x) = 0 := by
  ext
  have hmin : min (τ₂ x : ℝ) (t : ℝ) ≤ τ₁ x := heq ▸ min_le_left _ _
  simp [max_eq_left hmin]

private theorem stepTime_stepOffset_of_gt {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    (hτ : ∀ x, τ₁ x ≤ τ₂ x) {t : I} {x : X} (ht : τ₁ x < t) :
    stepTime τ₁ τ₂ (stepOffset hτ (t, x), x) = min t (τ₂ x) := by
  ext
  have hmax : max (τ₁ x : ℝ) (min (τ₂ x : ℝ) (t : ℝ)) = min (τ₂ x : ℝ) (t : ℝ) :=
    max_eq_right (le_min (hτ x) ht.le)
  rw [coe_stepTime, coe_stepOffset, hmax, add_sub_cancel, ← min_assoc, min_self, min_comm]
  rfl

/-- Advance a `PartialLift` from stopping time `τ₁` to `τ₂` using a local Hurewicz lift over an
open neighbourhood `O` of `closure {x | τ₁ x < τ₂ x}`. -/
private theorem PartialLift.advanceOpen {X : Type*} [TopologicalSpace X] {p : E → B}
    {f : C(X, E)} {H : C(I × X, B)} {τ₁ τ₂ : C(X, I)} (hτ : ∀ x, τ₁ x ≤ τ₂ x)
    (L : PartialLift p f H τ₁) {O : Set X} (hO : IsOpen O)
    (hclos : closure {x : X | τ₁ x < τ₂ x} ⊆ O) {U : Set B}
    (hhlp : HasHomotopyLiftingProperty
      (Set.MapsTo.restrict p (p ⁻¹' U) U (mapsTo_preimage p U)) O)
    (hHU : ∀ x ∈ O, ∀ t ∈ Icc (τ₁ x) (τ₂ x), H (t, x) ∈ U) :
    ∃ L' : PartialLift p f H τ₂,
      ∀ t x, τ₁ x = τ₂ x → L'.map (t, x) = L.map (t, x) := by
  classical
  let gO : C(O, E) := ⟨fun x ↦ L.map (τ₁ x.1, x.1), by fun_prop⟩
  let KO : C(I × O, B) := ⟨fun z ↦ H (stepTime τ₁ τ₂ (z.1, z.2.1), z.2.1), by fun_prop⟩
  obtain ⟨GO, hGO_proj, hGO_zero⟩ := hhlp.exists_lift_of_mem gO KO
    (fun z ↦ hHU z.2.1 z.2.2 _ (stepTime_mem_Icc hτ z.1 z.2.1))
    (fun x ↦ by simp only [KO, gO, ContinuousMap.coe_mk, stepTime_zero hτ, L.proj_eq, min_self])
  let onO : C(I × O, E) :=
    ⟨fun z ↦ if z.1 ≤ τ₁ z.2.1 then L.map (z.1, z.2.1)
        else GO (stepOffset hτ (z.1, z.2.1), z.2),
      Continuous.if_le (by fun_prop) (by fun_prop) continuous_fst (by fun_prop) fun z hz ↦ by
        rw [stepOffset_eq_zero_of_le hτ hz.le, hGO_zero z.2, hz]; rfl⟩
  have honO_apply (t : I) (x : O) :
      onO (t, x) = if t ≤ τ₁ x.1 then L.map (t, x.1) else GO (stepOffset hτ (t, x.1), x) := rfl
  have honO_eq_of_eq : ∀ (t : I) (x : O), τ₁ x.1 = τ₂ x.1 → onO (t, x) = L.map (t, x.1) := by
    intro t x heq
    rw [honO_apply]
    split_ifs with ht
    · rfl
    · rw [stepOffset_eq_zero_of_eq hτ t heq, hGO_zero x]
      exact (L.const_of_ge t x.1 (le_of_not_ge ht)).symm
  let LO : PartialLift p (f.restrict O) (restrictHomotopy H O) (τ₂.restrict O) :=
    { map := onO
      proj_eq := fun t x ↦ by
        rw [honO_apply, restrictHomotopy_apply, ContinuousMap.restrict_apply]
        split_ifs with ht
        · rw [L.proj_eq, min_eq_left ht, min_eq_left (ht.trans (hτ x.1))]
        · rw [← Function.comp_apply (f := p), hGO_proj]
          exact stepTime_stepOffset_of_gt hτ (not_le.1 ht) ▸ rfl
      zero_eq := fun x ↦ by
        rw [honO_apply, ContinuousMap.restrict_apply, ite_eq_left unitInterval.nonneg', L.zero_eq]
      const_of_ge := fun t x ht ↦ by
        rw [ContinuousMap.restrict_apply] at ht ⊢
        by_cases heq : τ₁ x.1 = τ₂ x.1
        · rw [honO_eq_of_eq t x heq, honO_eq_of_eq (τ₂ x.1) x heq, ← heq]
          exact L.const_of_ge t x.1 (heq ▸ ht)
        · have hlt : τ₁ x.1 < τ₂ x.1 := lt_of_le_of_ne (hτ x.1) heq
          rw [honO_apply, honO_apply,
            ite_eq_right (not_le.2 (hlt.trans_le ht)), ite_eq_right (not_le.2 hlt)]
          have htle : (τ₂ x.1 : ℝ) ≤ t := ht
          exact congrArg (fun s ↦ GO (s, x)) (Subtype.ext (by simp [min_eq_left htle])) }
  exact L.extendFromOpen hτ hO hclos LO honO_eq_of_eq

private noncomputable def clipSegTime {X : Type*} [TopologicalSpace X] (τ₁ τ₂ : C(X, I))
    (m : ℕ) (j : Fin (m + 2)) : C(X, I) :=
  ⟨fun x ↦ max (τ₁ x) (min (τ₂ x) (segEndpt m j)), by fun_prop⟩

private theorem clipSegTime_apply {X : Type*} [TopologicalSpace X] (τ₁ τ₂ : C(X, I))
    (m : ℕ) (j : Fin (m + 2)) (x : X) :
    clipSegTime τ₁ τ₂ m j x = max (τ₁ x) (min (τ₂ x) (segEndpt m j)) :=
  rfl

private theorem clipSegTime_zero {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    (m : ℕ) (x : X) :
    clipSegTime τ₁ τ₂ m 0 x = τ₁ x := by
  rw [clipSegTime_apply, segEndpt_zero, min_eq_right unitInterval.nonneg',
    max_eq_left unitInterval.nonneg']

private theorem clipSegTime_last {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    (hτ : ∀ x, τ₁ x ≤ τ₂ x) (m : ℕ) (x : X) :
    clipSegTime τ₁ τ₂ m (Fin.last (m + 1)) x = τ₂ x := by
  rw [clipSegTime_apply, segEndpt_last, min_eq_left unitInterval.le_one', max_eq_right (hτ x)]

private theorem clipSegTime_mono {X : Type*} [TopologicalSpace X] (τ₁ τ₂ : C(X, I))
    (m : ℕ) (k : Fin (m + 1)) (x : X) :
    clipSegTime τ₁ τ₂ m k.castSucc x ≤ clipSegTime τ₁ τ₂ m k.succ x := by
  rw [clipSegTime_apply, clipSegTime_apply]
  exact max_le_max_left _ (min_le_min_left _ (segEndpt_mono m k.castSucc_le_succ))

private theorem clipSegTime_eq_of_eq {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    (m : ℕ) (k : Fin (m + 1)) {x : X} (heq : τ₁ x = τ₂ x) :
    clipSegTime τ₁ τ₂ m k.castSucc x = clipSegTime τ₁ τ₂ m k.succ x := by
  rw [clipSegTime_apply, clipSegTime_apply, ← heq,
    max_eq_left (min_le_left _ _), max_eq_left (min_le_left _ _)]

private theorem closure_lt_clipSegTime_subset {X : Type*} [TopologicalSpace X]
    {τ₁ τ₂ : C(X, I)} (m : ℕ) (k : Fin (m + 1)) :
    closure {x : X | clipSegTime τ₁ τ₂ m k.castSucc x < clipSegTime τ₁ τ₂ m k.succ x} ⊆
      {x : X | segEndpt m k.castSucc ≤ τ₂ x ∧ τ₁ x ≤ segEndpt m k.succ} := by
  refine closure_minimal (fun x hx ↦ ⟨?_, ?_⟩)
    ((isClosed_le continuous_const τ₂.continuous).inter
      (isClosed_le τ₁.continuous continuous_const))
  · by_contra hle
    have h1 : min (τ₂ x) (segEndpt m k.castSucc) = τ₂ x := min_eq_left (not_le.1 hle).le
    have h2 : min (τ₂ x) (segEndpt m k.succ) = τ₂ x :=
      min_eq_left ((not_le.1 hle).le.trans (segEndpt_mono m k.castSucc_le_succ))
    have heq : clipSegTime τ₁ τ₂ m k.castSucc x = clipSegTime τ₁ τ₂ m k.succ x := by
      rw [clipSegTime_apply, clipSegTime_apply, h1, h2]
    exact hx.ne heq
  · by_contra hle
    have h2 : min (τ₂ x) (segEndpt m k.succ) ≤ τ₁ x :=
      (min_le_right _ _).trans (not_le.1 hle).le
    have h1 : min (τ₂ x) (segEndpt m k.castSucc) ≤ τ₁ x :=
      (min_le_min_left _ (segEndpt_mono m k.castSucc_le_succ)).trans h2
    have heq : clipSegTime τ₁ τ₂ m k.castSucc x = clipSegTime τ₁ τ₂ m k.succ x := by
      rw [clipSegTime_apply, clipSegTime_apply, max_eq_left h1, max_eq_left h2]
    exact hx.ne heq

private theorem Icc_clipSegTime_subset {X : Type*} [TopologicalSpace X] {τ₁ τ₂ : C(X, I)}
    {m : ℕ} {k : Fin (m + 1)} {x : X}
    (hx : segEndpt m k.castSucc ≤ τ₂ x ∧ τ₁ x ≤ segEndpt m k.succ) :
    Icc (clipSegTime τ₁ τ₂ m k.castSucc x) (clipSegTime τ₁ τ₂ m k.succ x) ⊆
      Icc (segEndpt m k.castSucc) (segEndpt m k.succ) := by
  intro t ht
  rw [mem_Icc, clipSegTime_apply, clipSegTime_apply] at ht
  exact ⟨((min_eq_right hx.1).symm.trans_le (le_max_right _ _)).trans ht.1,
    ht.2.trans (max_le hx.2 (min_le_right _ _))⟩

/-- Advance a `PartialLift` across `m + 1` uniform segments on an open stratum `S ⊆ A` where each
segment `[k/(m+1), (k+1)/(m+1)]` maps into `{b | 0 < ρ (α k) b} ⊆ U (α k)`. -/
private theorem PartialLift.advanceTube {ι : Type*} {A : Type w} [TopologicalSpace A]
    {p : E → B} {U : ι → Set B} (ρ : PartitionOfUnity ι B) (hρ : ∀ i, support (ρ i) ⊆ U i)
    (hlift : ∀ i (W : Set A), IsOpen W →
      HasHomotopyLiftingProperty
        (Set.MapsTo.restrict p (p ⁻¹' U i) (U i) (mapsTo_preimage p (U i))) W)
    {S : Set A} (hS : IsOpen S) {f : C(S, E)} {H : C(I × S, B)} {τ₁ τ₂ : C(S, I)}
    (hτ : ∀ x, τ₁ x ≤ τ₂ x) (L : PartialLift p f H τ₁) (m : ℕ) (α : Fin (m + 1) → ι)
    (hseg : ∀ (x : S) (k : Fin (m + 1)),
      ∀ t ∈ Icc (segEndpt m k.castSucc) (segEndpt m k.succ), 0 < ρ (α k) (H (t, x))) :
    ∃ L' : PartialLift p f H τ₂,
      ∀ t x, τ₁ x = τ₂ x → L'.map (t, x) = L.map (t, x) := by
  have step : ∀ j : Fin (m + 2), ∃ Lj : PartialLift p f H (clipSegTime τ₁ τ₂ m j),
      ∀ t x, τ₁ x = τ₂ x → Lj.map (t, x) = L.map (t, x) := by
    refine Fin.induction ?_ ?_
    · exact ⟨L.congrTime fun x ↦ (clipSegTime_zero m x).symm, fun _ _ _ ↦ rfl⟩
    · intro k ⟨Lk, hLk⟩
      let σ₁ := clipSegTime τ₁ τ₂ m k.castSucc
      let σ₂ := clipSegTime τ₁ τ₂ m k.succ
      let hσ : ∀ x, σ₁ x ≤ σ₂ x := clipSegTime_mono τ₁ τ₂ m k
      have hφ_cont : Continuous fun z : I × S ↦
          ρ (α k) (H (Icc.convexComb (σ₁ z.2) (σ₂ z.2) z.1, z.2)) :=
        (ρ (α k)).continuous.comp <| H.continuous.comp <|
          (Icc.continuous_convexComb_prod.comp
            (by fun_prop : Continuous fun z : I × S ↦ (σ₁ z.2, σ₂ z.2, z.1))).prodMk continuous_snd
      have hφx_cont : ∀ x : S, Continuous fun u : I ↦
          ρ (α k) (H (Icc.convexComb (σ₁ x) (σ₂ x) u, x)) :=
        fun x ↦ hφ_cont.comp (continuous_id.prodMk continuous_const)
      let O : Set S := {x : S | 0 < ⨅ u : I, ρ (α k) (H (Icc.convexComb (σ₁ x) (σ₂ x) u, x))}
      have hO : IsOpen O := isOpen_lt continuous_const hφ_cont.iInf_of_compactSpace
      have hclos : closure {x : S | σ₁ x < σ₂ x} ⊆ O := by
        refine (closure_lt_clipSegTime_subset m k).trans fun x hx ↦ ?_
        rw [mem_ofPred_eq]
        refine (hφx_cont x).lowerSemicontinuous.lt_ciInf_iff.2 fun u ↦ ?_
        exact hseg x k _ (Icc_clipSegTime_subset hx
          ⟨Icc.le_convexComb (hσ x) u, Icc.convexComb_le (hσ x) u⟩)
      have hHU : ∀ x ∈ O, ∀ t ∈ Icc (σ₁ x) (σ₂ x), H (t, x) ∈ U (α k) := by
        intro x hx t ht
        rw [Icc.eq_convexComb ht.1 ht.2]
        exact hρ (α k) (((hφx_cont x).lowerSemicontinuous.lt_ciInf_iff.1 hx) _).ne'
      obtain ⟨Lk', hLk'⟩ := Lk.advanceOpen hσ hO hclos
        (.of_isOpenEmbedding (hlift (α k))
          (hS.isOpenEmbedding_subtypeVal.comp hO.isOpenEmbedding_subtypeVal)) hHU
      exact ⟨Lk', fun t x heq ↦ (hLk' t x (clipSegTime_eq_of_eq m k heq)).trans (hLk t x heq)⟩
  obtain ⟨Llast, hLlast⟩ := step (Fin.last (m + 1))
  exact ⟨Llast.congrTime (clipSegTime_last hτ m), hLlast⟩

end PartialLift

section SequentialSchedule

private def cumTime {A : Type w} [TopologicalSpace A] (μ : PartitionOfUnity ℕ A) (n : ℕ) :
    C(A, I) :=
  ⟨fun a ↦ ⟨∑ j ∈ Finset.range n, μ j a, Finset.sum_nonneg fun j _ ↦ μ.nonneg j a, by
      classical
      exact (Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        fun j _ _ ↦ μ.nonneg j a).trans
          (μ.sum_finsupport' (mem_univ a) Finset.subset_union_right).le⟩,
    by fun_prop⟩

@[simp]
private theorem coe_cumTime {A : Type w} [TopologicalSpace A] (μ : PartitionOfUnity ℕ A)
    (n : ℕ) (a : A) :
    (cumTime μ n a : ℝ) = ∑ j ∈ Finset.range n, μ j a :=
  rfl

private theorem cumTime_zero_apply {A : Type w} [TopologicalSpace A] (μ : PartitionOfUnity ℕ A)
    (a : A) :
    cumTime μ 0 a = 0 := by
  ext; simp

private theorem cumTime_le_succ {A : Type w} [TopologicalSpace A] (μ : PartitionOfUnity ℕ A)
    (n : ℕ) (a : A) :
    cumTime μ n a ≤ cumTime μ (n + 1) a := by
  rw [← Subtype.coe_le_coe, coe_cumTime, coe_cumTime, Finset.sum_range_succ]
  linarith [μ.nonneg n a]

private theorem closure_cumTime_lt_subset {A : Type w} [TopologicalSpace A]
    (μ : PartitionOfUnity ℕ A) (n : ℕ) :
    closure {a : A | cumTime μ n a < cumTime μ (n + 1) a} ⊆ tsupport (μ n) := by
  refine closure_mono fun a ha ↦ ?_
  rw [mem_ofPred_eq, ← Subtype.coe_lt_coe, coe_cumTime, coe_cumTime, Finset.sum_range_succ] at ha
  exact (by linarith : 0 < μ n a).ne'

private theorem cumTime_eq_one_of_finsupport_subset {A : Type w} [TopologicalSpace A]
    (μ : PartitionOfUnity ℕ A) {n : ℕ} {a : A} (h : μ.finsupport a ⊆ Finset.range n) :
    cumTime μ n a = 1 :=
  Subtype.ext (μ.sum_finsupport' (mem_univ a) h)

/-- Advance a global `PartialLift` on `A` from `cumTime μ n` to `cumTime μ (n + 1)` by lifting
independently on the pairwise disjoint open gap strata `{a | 0 < ν.gap E a}` of cardinality `n`. -/
private theorem PartialLift.advanceGapStep {ι : Type*} {E : Type u} {B : Type v} {A : Type w}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace A]
    {p : E → B} {U : ι → Set B} (ρ : PartitionOfUnity ι B) (hρ : ∀ i, support (ρ i) ⊆ U i)
    (hlift : ∀ i (W : Set A), IsOpen W →
      HasHomotopyLiftingProperty
        (Set.MapsTo.restrict p (p ⁻¹' U i) (U i) (mapsTo_preimage p (U i))) W)
    {f : C(A, E)} {H : C(I × A, B)} (n : ℕ)
    (L : PartialLift p f H (cumTime (tubePartition ρ H).gapPartition.shrink n)) :
    ∃ L' : PartialLift p f H (cumTime (tubePartition ρ H).gapPartition.shrink (n + 1)),
      ∀ t a, cumTime (tubePartition ρ H).gapPartition.shrink n a =
        cumTime (tubePartition ρ H).gapPartition.shrink (n + 1) a →
        L'.map (t, a) = L.map (t, a) := by
  classical
  let ν := tubePartition ρ H
  let μ := ν.gapPartition.shrink
  let τ₁ := cumTime μ n
  let τ₂ := cumTime μ (n + 1)
  have hτ : ∀ a, τ₁ a ≤ τ₂ a := cumTime_le_succ μ n
  let Stratum (F : Finset (Σ m : ℕ, Fin (m + 1) → ι)) : Set A := {a : A | 0 < ν.gap F a}
  have hStratum_open : ∀ F, IsOpen (Stratum F) := fun F ↦
    isOpen_lt continuous_const (ν.continuous_gap F)
  have hlocal : ∀ F : {F : Finset (Σ m : ℕ, Fin (m + 1) → ι) // F.card = n ∧ F.Nonempty},
      ∃ LF : PartialLift p (f.restrict (Stratum F.1)) (restrictHomotopy H (Stratum F.1))
        (τ₂.restrict (Stratum F.1)),
      ∀ t (x : Stratum F.1), τ₁ x.1 = τ₂ x.1 → LF.map (t, x) = L.map (t, x.1) := by
    intro ⟨F, hcard, hne⟩
    let idx := hne.choose
    refine (L.restrict (Stratum F)).advanceTube ρ hρ hlift (hStratum_open F)
      (fun x ↦ hτ x.1) idx.1 idx.2 fun x k t ht ↦ ?_
    have hν_pos : 0 < tubePartition ρ H idx x.1 := ν.pos_of_gap_pos x.2 hne.choose_spec
    rw [tubePartition, PartitionOfUnity.ofExistsPos_pos_iff] at hν_pos
    exact pos_of_tubeWeight_pos (tubeWeight_pos_of_truncTubeWeight_pos hν_pos) k ht
  choose LF hLF using hlocal
  let hasStratum (a : A) : Prop :=
    ∃ F : {F : Finset (Σ m : ℕ, Fin (m + 1) → ι) // F.card = n ∧ F.Nonempty}, a ∈ Stratum F.1
  let O : Set A := {a : A | hasStratum a}
  have hO : IsOpen O := by
    convert isOpen_iUnion fun F : {F // F.card = n ∧ F.Nonempty} ↦ hStratum_open F.1
    ext a; simp [O, hasStratum]
  have hclos_sub : closure {a : A | τ₁ a < τ₂ a} ⊆ O := fun a ha ↦ by
    have hsupp_gap : a ∈ support (ν.gapPartition n) :=
      ν.gapPartition.tsupport_shrink_subset_support n (closure_cumTime_lt_subset μ n ha)
    have hpos_gap : 0 < ν.gapPartition n a :=
      lt_of_le_of_ne (ν.gapPartition.nonneg n a) (Ne.symm hsupp_gap)
    obtain ⟨F, hcard, hgap⟩ := ν.exists_gap_pos_of_gapPartition_pos hpos_gap
    exact ⟨⟨F, hcard, (ν.gap_pos_iff.1 hgap).1⟩, hgap⟩
  let onO_fun (z : I × O) : E := (LF z.2.2.choose).map (z.1, ⟨z.2.1, z.2.2.choose_spec⟩)
  have honO_stratum :
      ∀ (F : {F : Finset (Σ m : ℕ, Fin (m + 1) → ι) // F.card = n ∧ F.Nonempty})
        (t : I) (x : O) (hx : x.1 ∈ Stratum F.1),
        onO_fun (t, x) = (LF F).map (t, ⟨x.1, hx⟩) := by
    intro F t x hx
    have hsub : x.2.choose = F := Subtype.ext <|
      ν.eq_of_gap_pos_of_card_eq x.2.choose_spec hx (x.2.choose.2.1.trans F.2.1.symm)
    cases hsub; rfl
  have honO_cont : Continuous onO_fun := by
    refine continuous_iff_continuousAt.2 fun ⟨t₀, x₀⟩ ↦ ?_
    obtain ⟨F, hx₀F⟩ := x₀.2
    let UF : Set O := {x : O | x.1 ∈ Stratum F.1}
    have hUF_open : IsOpen UF := (hStratum_open F.1).preimage continuous_subtype_val
    have hOn : ContinuousOn onO_fun (univ ×ˢ UF) :=
      continuousOn_iff_continuous_domRestrict.2 <|
        (by fun_prop : Continuous fun z : univ ×ˢ UF ↦ (LF F).map (z.1.1, ⟨z.1.2.1, z.2.2⟩)).congr
          fun z ↦ (honO_stratum F z.1.1 z.1.2 z.2.2).symm
    exact hOn.continuousAt ((isOpen_univ.prod hUF_open).mem_nhds ⟨mem_univ t₀, hx₀F⟩)
  let LO : PartialLift p (f.restrict O) (restrictHomotopy H O) (τ₂.restrict O) :=
    { map := ⟨onO_fun, honO_cont⟩
      proj_eq := fun t x ↦ by
        obtain ⟨F, hxF⟩ := x.2
        rw [ContinuousMap.coe_mk, honO_stratum F t x hxF]
        exact (LF F).proj_eq t ⟨x.1, hxF⟩
      zero_eq := fun x ↦ by
        obtain ⟨F, hxF⟩ := x.2
        rw [ContinuousMap.coe_mk, honO_stratum F 0 x hxF]
        exact (LF F).zero_eq ⟨x.1, hxF⟩
      const_of_ge := fun t x ht ↦ by
        obtain ⟨F, hxF⟩ := x.2
        rw [ContinuousMap.coe_mk, ContinuousMap.restrict_apply,
          honO_stratum F t x hxF, honO_stratum F (τ₂ x.1) x hxF]
        exact (LF F).const_of_ge t ⟨x.1, hxF⟩ ht }
  refine L.extendFromOpen hτ hO hclos_sub LO fun t x heq ↦ ?_
  obtain ⟨F, hxF⟩ := x.2
  exact (honO_stratum F t x hxF).trans (hLF F t ⟨x.1, hxF⟩ heq)

end SequentialSchedule

section PublicAPI

variable {ι : Type*} {E : Type u} {B : Type v} {A : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace A]

/-- **Dold's local-to-global homotopy lifting theorem.** Let `p : E → B` be a map and
`(U i)_{i ∈ ι}` a numerable cover of `B`, witnessed by a partition of unity
`ρ : PartitionOfUnity ι B` with `support (ρ i) ⊆ U i` for every `i`. If each restriction
`p ⁻¹' U i → U i` has the homotopy lifting property with respect to every open subset of `A`, then
`p` has the homotopy lifting property with respect to `A`. -/
theorem HasHomotopyLiftingProperty.of_partitionOfUnity {p : E → B}
    {U : ι → Set B} (ρ : PartitionOfUnity ι B) (hρ : ∀ i, support (ρ i) ⊆ U i)
    (hlift : ∀ i (W : Set A), IsOpen W →
      HasHomotopyLiftingProperty
        (Set.MapsTo.restrict p (p ⁻¹' U i) (U i) (mapsTo_preimage p (U i))) W) :
    HasHomotopyLiftingProperty p A := by
  intro f H hH
  classical
  let μ := (tubePartition ρ H).gapPartition.shrink
  let stepChoice : ∀ (n : ℕ) (Ln : PartialLift p f H (cumTime μ n)),
      {L' : PartialLift p f H (cumTime μ (n + 1)) //
        ∀ t a, cumTime μ n a = cumTime μ (n + 1) a → L'.map (t, a) = Ln.map (t, a)} :=
    fun n Ln ↦ ⟨(Ln.advanceGapStep ρ hρ hlift n).choose,
      (Ln.advanceGapStep ρ hρ hlift n).choose_spec⟩
  let L : ∀ n : ℕ, PartialLift p f H (cumTime μ n) :=
    Nat.rec ((PartialLift.initial f H hH).congrTime fun a ↦ (cumTime_zero_apply μ a).symm)
      fun n Ln ↦ (stepChoice n Ln).1
  have hL_eq : ∀ n t a, cumTime μ n a = cumTime μ (n + 1) a →
      (L (n + 1)).map (t, a) = (L n).map (t, a) :=
    fun n ↦ (stepChoice n (L n)).2
  have hL_stable : ∀ {N n : ℕ} (hNn : N ≤ n) {a : A}
      (hsupp : μ.finsupport a ⊆ Finset.range N) (t : I),
      (L n).map (t, a) = (L N).map (t, a) := by
    intro N n hNn a hsupp t
    induction n, hNn using Nat.le_induction with
    | base => rfl
    | succ m hNm ih =>
      have h1 : cumTime μ m a = 1 := cumTime_eq_one_of_finsupport_subset μ
        (hsupp.trans (Finset.range_mono hNm))
      have h2 : cumTime μ (m + 1) a = 1 := cumTime_eq_one_of_finsupport_subset μ
        (hsupp.trans (Finset.range_mono (hNm.trans (Nat.le_succ m))))
      exact (hL_eq m t a (h1.trans h2.symm)).trans ih
  let stopIdx (a : A) : ℕ := (μ.finsupport a).sup id + 1
  have hstop_sub : ∀ a, μ.finsupport a ⊆ Finset.range (stopIdx a) := fun a j hj ↦
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  let Gfun (z : I × A) : E := (L (stopIdx z.2)).map z
  have hG_cont : Continuous Gfun := by
    refine continuous_iff_continuousAt.2 fun ⟨t₀, a₀⟩ ↦ ?_
    obtain ⟨J, hJ⟩ := μ.locallyFinite.exists_finset_support a₀
    let N : ℕ := J.sup id + 1
    have hnhds : univ ×ˢ {a : A | support (μ · a) ⊆ J} ∈ 𝓝 (t₀, a₀) :=
      prod_mem_nhds univ_mem hJ
    refine (L N).map.continuous.continuousAt.congr
      (Filter.eventually_of_mem hnhds fun ⟨t, a⟩ hz ↦ ?_)
    have hfin_sub : μ.finsupport a ⊆ J := fun j hj ↦
      hz.2 ((μ.mem_finsupport a).1 hj)
    have hle : stopIdx a ≤ N :=
      Nat.succ_le_succ (Finset.sup_mono hfin_sub)
    exact hL_stable hle (hstop_sub a) t
  refine ⟨⟨Gfun, hG_cont⟩, funext fun ⟨t, a⟩ ↦ ?_, fun a ↦ (L (stopIdx a)).zero_eq a⟩
  dsimp only [Function.comp_apply, Gfun]
  rw [ContinuousMap.coe_mk, (L (stopIdx a)).proj_eq,
    cumTime_eq_one_of_finsupport_subset μ (hstop_sub a), min_eq_left unitInterval.le_one']

/-- Over a normal paracompact base, a map whose restrictions to the members of an open cover have
the homotopy lifting property with respect to every open subset of `A` has the homotopy lifting
property globally with respect to `A`. -/
theorem HasHomotopyLiftingProperty.of_isOpenCover [NormalSpace B] [ParacompactSpace B]
    {p : E → B} {U : ι → Set B} (hU : ∀ i, IsOpen (U i)) (hcov : ∀ b, ∃ i, b ∈ U i)
    (hlift : ∀ i (W : Set A), IsOpen W →
      HasHomotopyLiftingProperty
        (Set.MapsTo.restrict p (p ⁻¹' U i) (U i) (mapsTo_preimage p (U i))) W) :
    HasHomotopyLiftingProperty p A := by
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hU
    fun b _ ↦ mem_iUnion.2 (hcov b)
  exact HasHomotopyLiftingProperty.of_partitionOfUnity ρ
    (fun i ↦ (subset_tsupport _).trans (hρ i)) hlift

/-- **Dold's local-to-global theorem for Hurewicz fibrations.** A continuous map `p : E → B` whose
restrictions `p ⁻¹' U i → U i` over a numerable cover `(U i)_{i ∈ ι}` of `B` (witnessed by a
partition of unity `ρ` with `support (ρ i) ⊆ U i`) are Hurewicz fibrations is itself a Hurewicz
fibration. -/
theorem isHurewiczFibration_of_partitionOfUnity {p : E → B} (hp : Continuous p)
    {U : ι → Set B} (ρ : PartitionOfUnity ι B) (hρ : ∀ i, support (ρ i) ⊆ U i)
    (hpU : ∀ i, IsHurewiczFibration.{w}
      (Set.MapsTo.restrict p (p ⁻¹' U i) (U i) (mapsTo_preimage p (U i)))) :
    IsHurewiczFibration.{w} p :=
  isHurewiczFibration_iff.2 ⟨hp, fun _ _ ↦
    HasHomotopyLiftingProperty.of_partitionOfUnity ρ hρ
      fun i W _ ↦ (hpU i).hasHomotopyLiftingProperty W⟩

/-- Convenience form of `TauCeti.isHurewiczFibration_of_partitionOfUnity` for a partition of unity
subordinate to `U` in the closed-support sense (`PartitionOfUnity.IsSubordinate`). -/
theorem isHurewiczFibration_of_isSubordinate {p : E → B} (hp : Continuous p)
    {U : ι → Set B} {ρ : PartitionOfUnity ι B} (hρ : ρ.IsSubordinate U)
    (hpU : ∀ i, IsHurewiczFibration.{w}
      (Set.MapsTo.restrict p (p ⁻¹' U i) (U i) (mapsTo_preimage p (U i)))) :
    IsHurewiczFibration.{w} p :=
  isHurewiczFibration_of_partitionOfUnity hp ρ
    (fun i ↦ (subset_tsupport _).trans (hρ i)) hpU

/-- Over a normal paracompact base (including every paracompact Hausdorff base), a continuous map
that is locally a Hurewicz fibration over an open cover is globally a Hurewicz fibration. -/
theorem isHurewiczFibration_of_isOpenCover [NormalSpace B] [ParacompactSpace B]
    {p : E → B} (hp : Continuous p) {U : ι → Set B} (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ b, ∃ i, b ∈ U i)
    (hpU : ∀ i, IsHurewiczFibration.{w}
      (Set.MapsTo.restrict p (p ⁻¹' U i) (U i) (mapsTo_preimage p (U i)))) :
    IsHurewiczFibration.{w} p :=
  isHurewiczFibration_iff.2 ⟨hp, fun _ _ ↦
    HasHomotopyLiftingProperty.of_isOpenCover hU hcov
      fun i W _ ↦ (hpU i).hasHomotopyLiftingProperty W⟩

end PublicAPI

end TauCeti
