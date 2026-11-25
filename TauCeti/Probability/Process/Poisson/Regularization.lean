/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.SimpleCountingPath
public import TauCeti.Probability.Process.Poisson.Augmentation
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Probability.Distributions.Poisson.SmallRate
import TauCeti.Probability.HasLaw
import TauCeti.Probability.Process.MonotoneAE
import TauCeti.Probability.Process.Poisson.Microscopic
import TauCeti.Topology.Instances.Real.DyadicGrid

/-!
# Regularization of filtered Poisson processes

`IsFilteredPoissonProcess.exists_isSimpleCountingPath_version` constructs from any filtered Poisson
process `N` a measurable `ℕ`-valued modification `M` such that *every* sample path `M · ω` (not
merely almost every path) satisfies `TauCeti.Probability.IsSimpleCountingPath`—so it is càdlàg,
continuous at `0`, has only finitely many discontinuities on each interval `[0, T]`, jumps by `+1`
at every discontinuity, and attains each level `c` at any finite first hitting time of `Set.Ici c`,
which then strictly precedes the hit of `c + 1`—while `(M t · : ℝ) =ᵐ[P] N t` at every time `t` and
`(t, ω) ↦ (M t ω : ℝ)` is a filtered Poisson process of the same rate on
`ℱ.ambientNullAugmentation P` (hence also on `(ℱ.ambientNullAugmentation P).rightCont` via
`IsFilteredPoissonProcess.rightCont`).

Conversely, if `M : ℝ≥0 → Ω → ℕ` already has real cast a filtered Poisson process and almost surely
right-continuous paths, `ae_monotone_of_isRightContinuous` and
`ae_isSimpleCountingPath_of_isRightContinuous` show that almost every trajectory of `M` is monotone
and in fact a simple counting path.

The regularization restricts `N` to dyadic times `j / 2 ^ m`, isolates an explicit measurable event
of full measure on which dyadic samples are natural-valued, monotone, zero near `0`, and jump by at
most `1` across overlapping double cells `[k / 2 ^ m, (k + 2) / 2 ^ m]`, and defines `M t ω` as the
right-hand dyadic infimum on that event and `0` outside it.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §3, and §4, Theorem 30.
* O. Kallenberg, *Foundations of Modern Probability*, third edition, Springer, 2021, Theorem 15.2.
-/

public section

open Filter Function MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability.IsFilteredPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {α : ℝ≥0} {N : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- Almost-sure right-continuity of a natural-valued filtered Poisson process implies almost-sure
monotonicity of its sample paths. -/
theorem ae_monotone_of_isRightContinuous {M : ℝ≥0 → Ω → ℕ}
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) :
    ∀ᵐ ω ∂P, Monotone (M · ω) :=
  ae_monotone_of_ae_le_of_isRightContinuous
    (fun _ _ hst ↦ (h.ae_le hst).mono fun _ ↦ Nat.cast_le.mp) hrc

/-- Almost-sure right-continuity upgrades a natural-valued filtered Poisson process to have almost
surely simple counting paths. -/
theorem ae_isSimpleCountingPath_of_isRightContinuous {M : ℝ≥0 → Ω → ℕ}
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) :
    ∀ᵐ ω ∂P, IsSimpleCountingPath (M · ω) := by
  have hmono := h.ae_monotone_of_isRightContinuous hrc
  have hjump := ae_count_le_add_one_of_hasLaw_sub_poissonMeasure (P := P) (N := M) hmono α
    fun s t _ ↦ h.hasLaw_sub_nat s t
  filter_upwards [h.eval_zero_ae_eq_zero, hmono, hrc, hjump] with ω h0 hm hr hj
  exact ⟨Nat.cast_eq_zero.mp h0, hm, hr, hj⟩

/-- For any times `s` and `t`, the probability that `N t - N s` exceeds `1` is at most
`(α * (t - s)) ^ 2 / 2` (using truncated subtraction on `ℝ≥0` when `t ≤ s`). -/
theorem measure_sub_gt_one_le (h : IsFilteredPoissonProcess ℱ α N P) (s t : ℝ≥0) :
    P {ω | 1 < N t ω - N s ω} ≤ (((α * (t - s)) ^ 2 / 2 : ℝ≥0) : ℝ≥0∞) := by
  rcases le_total s t with hst | hts
  · have := h.isProbabilityMeasure
    have hfloor := (h.hasLaw_sub hst).natFloor_of_map_natCast
    have hae : ({ω | 1 < N t ω - N s ω} : Set Ω) =ᵐ[P] {ω | 2 ≤ ⌊(N t - N s) ω⌋₊} := by
      filter_upwards [(h.hasLaw_sub hst).ae_exists_nat_eq_of_map_natCast] with ω ⟨n, hn⟩
      rw [Pi.sub_apply] at hn
      simp only [Pi.sub_apply, hn, Nat.floor_natCast, Nat.one_lt_cast]
      omega
    rw [← ofReal_measureReal (measure_ne_top P _), ENNReal.ofReal_le_coe,
      measureReal_congr hae, hfloor.measureReal_eq (p := fun n ↦ 2 ≤ n) .of_discrete]
    simpa only [Ici_def, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using
      poissonMeasure_real_Ici_two_le (α * (t - s))
  · have hzero : P {ω | 1 < N t ω - N s ω} = 0 := by
      have hae : ∀ᵐ ω ∂P, ¬ (1 < N t ω - N s ω) :=
        (h.ae_le hts).mono fun _ hle hgt ↦ by linarith
      simpa only [ae_iff, Classical.not_not] using hae
    simp [hzero]

/-! ### Dyadic grid and good sample-path event -/

private instance (t : ℝ≥0) : Nonempty {p : ℕ × ℕ // t < dyadicNNReal p.1 p.2} :=
  ⟨⟨(0, ⌊(t : ℝ)⌋₊ + 1), by simpa using lt_dyadicNNReal_floor_add_one 0 t⟩⟩

private structure IsDyadicGood (N : ℝ≥0 → Ω → ℝ) (ω : Ω) : Prop where
  exists_nat (m j : ℕ) : ∃ n : ℕ, N (dyadicNNReal m j) ω = n
  mono ⦃m₁ j₁ m₂ j₂ : ℕ⦄ :
    dyadicNNReal m₁ j₁ ≤ dyadicNNReal m₂ j₂ → N (dyadicNNReal m₁ j₁) ω ≤ N (dyadicNNReal m₂ j₂) ω
  zero : ∃ m : ℕ, N (dyadicNNReal m 1) ω = 0
  jump (T : ℕ) : ∃ m : ℕ, ∀ k < (T + 1) * 2 ^ m,
    N (dyadicNNReal m (k + 2)) ω - N (dyadicNNReal m k) ω ≤ 1

private lemma measurableSet_isDyadicGood (hN : ∀ t, Measurable (N t)) :
    MeasurableSet {ω | IsDyadicGood N ω} := by
  have heq : {ω | IsDyadicGood N ω} =
      (⋂ (m : ℕ) (j : ℕ), ⋃ n : ℕ, {ω | N (dyadicNNReal m j) ω = n}) ∩
      (⋂ (m₁ : ℕ) (j₁ : ℕ) (m₂ : ℕ) (j₂ : ℕ) (_ : dyadicNNReal m₁ j₁ ≤ dyadicNNReal m₂ j₂),
        {ω | N (dyadicNNReal m₁ j₁) ω ≤ N (dyadicNNReal m₂ j₂) ω}) ∩
      (⋃ m : ℕ, {ω | N (dyadicNNReal m 1) ω = 0}) ∩
      (⋂ T : ℕ, ⋃ m : ℕ, ⋂ (k : ℕ) (_ : k < (T + 1) * 2 ^ m),
        {ω | N (dyadicNNReal m (k + 2)) ω - N (dyadicNNReal m k) ω ≤ 1}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
    exact ⟨fun h ↦ ⟨⟨⟨h.exists_nat, h.mono⟩, h.zero⟩, h.jump⟩,
      fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ ↦ ⟨h1, h2, h3, h4⟩⟩
  have h1 : MeasurableSet (⋂ (m : ℕ) (j : ℕ), ⋃ n : ℕ, {ω | N (dyadicNNReal m j) ω = n}) :=
    .iInter fun _ ↦ .iInter fun _ ↦ .iUnion fun _ ↦ measurableSet_eq_fun (hN _) measurable_const
  have h2 : MeasurableSet
      (⋂ (m₁ : ℕ) (j₁ : ℕ) (m₂ : ℕ) (j₂ : ℕ) (_ : dyadicNNReal m₁ j₁ ≤ dyadicNNReal m₂ j₂),
        {ω | N (dyadicNNReal m₁ j₁) ω ≤ N (dyadicNNReal m₂ j₂) ω}) :=
    .iInter fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦
      measurableSet_le (hN _) (hN _)
  have h3 : MeasurableSet (⋃ m : ℕ, {ω | N (dyadicNNReal m 1) ω = 0}) :=
    .iUnion fun _ ↦ measurableSet_eq_fun (hN _) measurable_const
  have h4 : MeasurableSet (⋂ T : ℕ, ⋃ m : ℕ, ⋂ (k : ℕ) (_ : k < (T + 1) * 2 ^ m),
      {ω | N (dyadicNNReal m (k + 2)) ω - N (dyadicNNReal m k) ω ≤ 1}) :=
    .iInter fun _ ↦ .iUnion fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦
      measurableSet_le ((hN _).sub (hN _)) measurable_const
  rw [heq]
  exact ((h1.inter h2).inter h3).inter h4

private lemma ae_dyadic_double_cell_le_one (h : IsFilteredPoissonProcess ℱ α N P) (T : ℕ) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, ∀ k < (T + 1) * 2 ^ m,
      N (dyadicNNReal m (k + 2)) ω - N (dyadicNNReal m k) ω ≤ 1 := by
  let bad : ℕ → Set Ω := fun m ↦
    ⋃ k ∈ Finset.range ((T + 1) * 2 ^ m),
      {ω | 1 < N (dyadicNNReal m (k + 2)) ω - N (dyadicNNReal m k) ω}
  have hbad (m : ℕ) :
      P (bad m) ≤ ((2 * (T + 1) * α ^ 2 : ℝ≥0) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hterm (k : ℕ) :
        P {ω | 1 < N (dyadicNNReal m (k + 2)) ω - N (dyadicNNReal m k) ω} ≤
          (((α * (2 * (2⁻¹ : ℝ≥0) ^ m)) ^ 2 / 2 : ℝ≥0) : ℝ≥0∞) := by
      simpa only [dyadicNNReal_add_two_sub] using
        h.measure_sub_gt_one_le (dyadicNNReal m k) (dyadicNNReal m (k + 2))
    refine (Finset.sum_le_sum fun k _ ↦ hterm k).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hnn : (((T + 1) * 2 ^ m : ℕ) : ℝ≥0) * ((α * (2 * (2⁻¹ : ℝ≥0) ^ m)) ^ 2 / 2) =
        (2 * (T + 1) * α ^ 2) * (2⁻¹ : ℝ≥0) ^ m := by
      push_cast
      simp only [inv_pow]
      field_simp
    refine le_of_eq ?_
    have hcoe := congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hnn
    push_cast at hcoe ⊢
    exact hcoe
  have hsum : (∑' m, P (bad m)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hbad)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by norm_num)
  filter_upwards [MeasureTheory.ae_eventually_notMem hsum] with ω hω
  obtain ⟨m, hm⟩ := hω.exists
  refine ⟨m, fun k hk ↦ not_lt.mp fun hgt ↦ hm ?_⟩
  exact mem_biUnion (Finset.mem_range.mpr hk) hgt

private lemma ae_isDyadicGood (h : IsFilteredPoissonProcess ℱ α N P) :
    ∀ᵐ ω ∂P, IsDyadicGood N ω := by
  have hnat : ∀ᵐ ω ∂P, ∀ m j : ℕ, ∃ n : ℕ, N (dyadicNNReal m j) ω = n :=
    ae_all_iff.mpr fun m ↦ ae_all_iff.mpr fun j ↦ h.ae_exists_nat_eq (dyadicNNReal m j)
  have hmono : ∀ᵐ ω ∂P, ∀ m₁ j₁ m₂ j₂ : ℕ, dyadicNNReal m₁ j₁ ≤ dyadicNNReal m₂ j₂ →
      N (dyadicNNReal m₁ j₁) ω ≤ N (dyadicNNReal m₂ j₂) ω :=
    ae_all_iff.mpr fun m₁ ↦ ae_all_iff.mpr fun j₁ ↦ ae_all_iff.mpr fun m₂ ↦
      ae_all_iff.mpr fun j₂ ↦ by
        by_cases hle : dyadicNNReal m₁ j₁ ≤ dyadicNNReal m₂ j₂
        · exact (h.ae_le hle).mono fun _ hω _ ↦ hω
        · exact ae_of_all _ fun _ hbad ↦ False.elim (hle hbad)
  have hzero : ∀ᵐ ω ∂P, ∃ m : ℕ, N (dyadicNNReal m 1) ω = 0 := by
    filter_upwards [h.ae_eventually_eval_add_two_inv_pow_eq 0, h.eval_zero_ae_eq_zero] with ω hω h0
    obtain ⟨m, hm⟩ := hω.exists
    exact ⟨m, by simpa [dyadicNNReal_one, h0] using hm⟩
  have hjump : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ m : ℕ, ∀ k < (T + 1) * 2 ^ m,
      N (dyadicNNReal m (k + 2)) ω - N (dyadicNNReal m k) ω ≤ 1 :=
    ae_all_iff.mpr fun T ↦ ae_dyadic_double_cell_le_one h T
  filter_upwards [hnat, hmono, hzero, hjump] with ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩

/-! ### Dyadic right-hand regularization -/

@[irreducible]
private noncomputable def dyadicReg (N : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : Ω → ℕ :=
  {ω | IsDyadicGood N ω}.indicator fun ω ↦
    ⨅ p : {p : ℕ × ℕ // t < dyadicNNReal p.1 p.2}, ⌊N (dyadicNNReal p.val.1 p.val.2) ω⌋₊

private lemma dyadicReg_of_good {ω : Ω} (hω : IsDyadicGood N ω) (t : ℝ≥0) :
    dyadicReg N t ω =
      ⨅ p : {p : ℕ × ℕ // t < dyadicNNReal p.1 p.2}, ⌊N (dyadicNNReal p.val.1 p.val.2) ω⌋₊ := by
  unfold dyadicReg
  exact indicator_of_mem hω _

private lemma dyadicReg_of_not_good {ω : Ω} (hω : ¬ IsDyadicGood N ω) (t : ℝ≥0) :
    dyadicReg N t ω = 0 := by
  unfold dyadicReg
  exact indicator_of_notMem hω _

private lemma measurable_dyadicReg (hN : ∀ t, Measurable (N t)) (t : ℝ≥0) :
    Measurable (dyadicReg N t) := by
  unfold dyadicReg
  exact (Measurable.iInf fun (p : {p : ℕ × ℕ // t < dyadicNNReal p.1 p.2}) ↦
    (hN (dyadicNNReal p.val.1 p.val.2)).nat_floor).indicator (measurableSet_isDyadicGood hN)

private lemma dyadicReg_le_of_lt {ω : Ω} (hω : IsDyadicGood N ω) {t : ℝ≥0} {m j : ℕ}
    (ht : t < dyadicNNReal m j) :
    dyadicReg N t ω ≤ ⌊N (dyadicNNReal m j) ω⌋₊ := by
  rw [dyadicReg_of_good hω]
  exact ciInf_le (OrderBot.bddBelow _) (⟨(m, j), ht⟩ : {p : ℕ × ℕ // t < dyadicNNReal p.1 p.2})

private lemma le_dyadicReg_of_le {ω : Ω} (hω : IsDyadicGood N ω) {s : ℝ≥0} {m k : ℕ}
    (hs : dyadicNNReal m k ≤ s) :
    ⌊N (dyadicNNReal m k) ω⌋₊ ≤ dyadicReg N s ω := by
  rw [dyadicReg_of_good hω]
  exact le_ciInf fun p ↦ Nat.floor_mono (hω.mono (hs.trans p.property.le))

private lemma floor_dyadicNNReal_add_two_le {ω : Ω} (hω : IsDyadicGood N ω) {m k : ℕ}
    (hle : N (dyadicNNReal m (k + 2)) ω - N (dyadicNNReal m k) ω ≤ 1) :
    ⌊N (dyadicNNReal m (k + 2)) ω⌋₊ ≤ ⌊N (dyadicNNReal m k) ω⌋₊ + 1 := by
  obtain ⟨a, ha⟩ := hω.exists_nat m k
  obtain ⟨b, hb⟩ := hω.exists_nat m (k + 2)
  rw [ha, hb, Nat.floor_natCast, Nat.floor_natCast]
  have : (b : ℝ) - (a : ℝ) ≤ 1 := by rwa [← ha, ← hb]
  exact_mod_cast (by linarith : (b : ℝ) ≤ (a : ℝ) + 1)

private lemma dyadicReg_monotone {ω : Ω} (hω : IsDyadicGood N ω) :
    Monotone (dyadicReg N · ω) := by
  intro s t hst
  dsimp only
  rw [dyadicReg_of_good hω t]
  exact le_ciInf fun p ↦ dyadicReg_le_of_lt hω (hst.trans_lt p.property)

private lemma dyadicReg_isRightContinuous {ω : Ω} (hω : IsDyadicGood N ω) :
    IsRightContinuous (dyadicReg N · ω) := fun t ↦ by
  let F : {p : ℕ × ℕ // t < dyadicNNReal p.1 p.2} → ℕ :=
    fun p ↦ ⌊N (dyadicNNReal p.val.1 p.val.2) ω⌋₊
  obtain ⟨p, hp⟩ := mem_range.mp (ciInf_mem F)
  rw [← dyadicReg_of_good hω] at hp
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT p.property] with s hs
  exact le_antisymm (dyadicReg_monotone hω hs.1.le) ((dyadicReg_le_of_lt hω hs.2).trans_eq hp)

private lemma dyadicReg_le_add_one {ω : Ω} (hω : IsDyadicGood N ω) ⦃t : ℝ≥0⦄ (ht : 0 < t) :
    ∃ s < t, dyadicReg N t ω ≤ dyadicReg N s ω + 1 := by
  let T : ℕ := ⌊(t : ℝ)⌋₊
  obtain ⟨m, hm⟩ := hω.jump T
  by_cases hsmall : t < dyadicNNReal m 1
  · refine ⟨0, ht, ?_⟩
    have hlt2 : t < dyadicNNReal m 2 := hsmall.trans (dyadicNNReal_strictMono m one_lt_two)
    exact (dyadicReg_le_of_lt hω hlt2).trans
      ((floor_dyadicNNReal_add_two_le hω (hm 0 (by positivity))).trans
        (Nat.add_le_add_right (le_dyadicReg_of_le hω (dyadicNNReal_zero m).le) 1))
  · let j : ℕ := ⌊(t : ℝ) * (2 : ℝ) ^ m⌋₊
    have hj1 : 1 ≤ j := Nat.le_floor <| by
      have h1 : dyadicNNReal m 1 ≤ t := not_lt.mp hsmall
      simpa only [Nat.cast_one] using
        (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)).mp
          (by simpa [dyadicNNReal_def] using NNReal.coe_le_coe.mpr h1)
    have hjT : j < (T + 1) * 2 ^ m := by
      rw [← Nat.cast_lt (α := ℝ)]
      calc
        (j : ℝ) ≤ (t : ℝ) * (2 : ℝ) ^ m := Nat.floor_le (by positivity)
        _ < ((T : ℝ) + 1) * (2 : ℝ) ^ m :=
          mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (t : ℝ)) (by positivity)
        _ = (((T + 1) * 2 ^ m : ℕ) : ℝ) := by push_cast; ring
    have hst : dyadicNNReal m (j - 1) < t :=
      (dyadicNNReal_strictMono m (by omega : j - 1 < j)).trans_le (dyadicNNReal_floor_le m t)
    have htk2 : t < dyadicNNReal m (j - 1 + 2) := by
      convert lt_dyadicNNReal_floor_add_one m t using 2
      omega
    refine ⟨dyadicNNReal m (j - 1), hst, ?_⟩
    exact (dyadicReg_le_of_lt hω htk2).trans
      ((floor_dyadicNNReal_add_two_le hω (hm (j - 1) (by omega))).trans
        (Nat.add_le_add_right (le_dyadicReg_of_le hω le_rfl) 1))

private lemma isSimpleCountingPath_dyadicReg (ω : Ω) :
    IsSimpleCountingPath (dyadicReg N · ω) := by
  by_cases hω : IsDyadicGood N ω
  · refine ⟨?_, dyadicReg_monotone hω, dyadicReg_isRightContinuous hω, dyadicReg_le_add_one hω⟩
    obtain ⟨m, hm⟩ := hω.zero
    have hpos : (0 : ℝ≥0) < dyadicNNReal m 1 := by
      rw [dyadicNNReal_one]
      positivity
    exact Nat.eq_zero_of_le_zero ((dyadicReg_le_of_lt hω hpos).trans_eq (by simp [hm]))
  · simp [dyadicReg_of_not_good hω]

private lemma dyadicReg_ae_eq (h : IsFilteredPoissonProcess ℱ α N P) (t : ℝ≥0) :
    (fun ω ↦ (dyadicReg N t ω : ℝ)) =ᵐ[P] N t := by
  have habove : ∀ᵐ ω ∂P, ∀ p : {p : ℕ × ℕ // t < dyadicNNReal p.1 p.2},
      N t ω ≤ N (dyadicNNReal p.val.1 p.val.2) ω :=
    ae_all_iff.mpr fun p ↦ h.ae_le p.property.le
  filter_upwards [ae_isDyadicGood h, h.ae_exists_nat_eq t, habove,
    h.ae_eventually_eval_eq_of_sub_le_two_inv_pow
      (fun n ↦ (lt_dyadicNNReal_floor_add_one n t).le)
      (fun n ↦ dyadicNNReal_floor_add_one_sub_le n t)] with ω hω ⟨c, hc⟩ hle hev
  obtain ⟨n, hn⟩ := hev.exists
  have hupper : dyadicReg N t ω ≤ c := by
    refine (dyadicReg_le_of_lt hω (lt_dyadicNNReal_floor_add_one n t)).trans_eq ?_
    rw [hn, hc, Nat.floor_natCast]
  have hlower : c ≤ dyadicReg N t ω := by
    rw [dyadicReg_of_good hω]
    refine le_ciInf fun p ↦ ?_
    simpa only [hc, Nat.floor_natCast] using Nat.floor_mono (hle p)
  rw [le_antisymm hupper hlower, hc]

/-- **Pathwise regularization of a filtered Poisson process.** Every homogeneous Poisson process `N`
relative to `ℱ` admits a measurable `ℕ`-valued modification `M` whose *every* sample path is a
simple counting path and whose real cast is a filtered Poisson process of the same rate on
`ℱ.ambientNullAugmentation P` (and hence also on `(ℱ.ambientNullAugmentation P).rightCont` by
`IsFilteredPoissonProcess.rightCont`). -/
theorem exists_isSimpleCountingPath_version (h : IsFilteredPoissonProcess ℱ α N P) :
    ∃ M : ℝ≥0 → Ω → ℕ,
      (∀ t, Measurable (M t)) ∧
      (∀ ω, IsSimpleCountingPath (M · ω)) ∧
      (∀ t, (fun ω ↦ (M t ω : ℝ)) =ᵐ[P] N t) ∧
      IsFilteredPoissonProcess (ℱ.ambientNullAugmentation P) α
        (fun t ω ↦ (M t ω : ℝ)) P := by
  refine ⟨dyadicReg N, measurable_dyadicReg h.measurable, isSimpleCountingPath_dyadicReg,
    dyadicReg_ae_eq h, ?_⟩
  have hcast : Continuous (Nat.cast : ℕ → ℝ) := continuous_of_discreteTopology
  have hmeasR (t : ℝ≥0) : Measurable fun ω ↦ (dyadicReg N t ω : ℝ) :=
    hcast.measurable.comp (measurable_dyadicReg h.measurable t)
  have hadapt : Adapted (ℱ.ambientNullAugmentation P) (fun t ω ↦ (dyadicReg N t ω : ℝ)) :=
    h.adapted.ambientNullAugmentation_of_ae_eq hmeasR fun t ↦ (dyadicReg_ae_eq h t).symm
  exact h.ambientNullAugmentation.congr (fun t ↦ (hadapt t).stronglyMeasurable)
    fun t ↦ (dyadicReg_ae_eq h t).symm

end TauCeti.Probability.IsFilteredPoissonProcess
