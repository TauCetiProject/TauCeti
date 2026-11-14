/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.HittingTime
public import TauCeti.Probability.Process.Poisson.Augmentation
public import TauCeti.Topology.Order.Cadlag
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Probability.Distributions.Poisson.SmallRate

/-!
# Pathwise simple counting paths and regularization of filtered Poisson processes

`TauCeti.Probability.IsSimpleCountingPath` packages the pathwise regularity of a standard counting
trajectory `f : ℝ≥0 → ℕ`: it starts at `0`, is monotone and right-continuous, and has jumps from the
left of size at most `1` at every positive time. From these four properties it follows that `f` is
càdlàg, continuous at `0`, has only finitely many discontinuities on each bounded interval `[0, T]`,
satisfies `leftLim f t + 1 = f t` at every discontinuity, and attains each level `c` exactly at its
first hitting time of `Set.Ici c`, which strictly precedes the hit of `c + 1`.

On the probabilistic side, `IsFilteredPoissonProcess.exists_isSimpleCountingPath_version` constructs
from any filtered Poisson process `N` a measurable `ℕ`-valued modification `M` such that *every*
sample path `M · ω` (not merely almost every path) is a simple counting path,
`(M t · : ℝ) =ᵐ[P] N t` at every time `t`, and `(t, ω) ↦ (M t ω : ℝ)` is a filtered Poisson process
of the same rate on `ℱ.ambientNullAugmentation P` (hence also on
`(ℱ.ambientNullAugmentation P).rightCont` via `IsFilteredPoissonProcess.rightCont`).

The construction restricts `N` to dyadic times `j / 2 ^ m`, isolates an explicit measurable event of
full measure on which dyadic samples are natural-valued, monotone, zero near `0`, and jump by at
most `1` across overlapping double cells `[k / 2 ^ m, (k + 2) / 2 ^ m]`, and defines `M t ω` as the
right-hand dyadic infimum on that event and `0` outside it.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §3, Theorem 31.
* O. Kallenberg, *Foundations of Modern Probability*, third edition, Springer, 2021, Theorem 15.2.
-/

public section

open Filter Function MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability

/-! ### Simple counting paths -/

/-- A trajectory `f : ℝ≥0 → ℕ` is a **simple counting path** if it starts at `0`, is monotone and
right-continuous, and jumps from the left by at most `1` at every positive time. -/
structure IsSimpleCountingPath (f : ℝ≥0 → ℕ) : Prop where
  /-- The count at time `0` is `0`. -/
  apply_zero : f 0 = 0
  /-- The count is nondecreasing in time. -/
  monotone : Monotone f
  /-- The count is right-continuous at every time. -/
  isRightContinuous : IsRightContinuous f
  /-- At every positive time `t`, some strictly earlier time `s < t` satisfies `f t ≤ f s + 1`. -/
  le_add_one ⦃t : ℝ≥0⦄ : 0 < t → ∃ s < t, f t ≤ f s + 1

namespace IsSimpleCountingPath

/-- The identically zero path is a simple counting path. -/
@[simp]
theorem zero : IsSimpleCountingPath 0 where
  apply_zero := rfl
  monotone := monotone_const
  isRightContinuous _ := tendsto_const_nhds
  le_add_one _ ht := ⟨0, ht, by simp⟩

/-- Every simple counting path is càdlàg. -/
theorem isCadlag {f : ℝ≥0 → ℕ} (hf : IsSimpleCountingPath f) : IsCadlag f :=
  hf.monotone.isCadlag hf.isRightContinuous

/-- Coercing a simple counting path to `ℝ` preserves the càdlàg property. -/
theorem isCadlag_real {f : ℝ≥0 → ℕ} (hf : IsSimpleCountingPath f) :
    IsCadlag fun t ↦ (f t : ℝ) := by
  have hc : Continuous (Nat.cast : ℕ → ℝ) := continuous_of_discreteTopology
  have hmono : Monotone fun t ↦ (f t : ℝ) := fun _ _ h ↦ Nat.cast_le.mpr (hf.monotone h)
  exact hmono.isCadlag fun t ↦ hc.continuousAt.tendsto.comp (hf.isRightContinuous t)

/-- A simple counting path is continuous at `0`. -/
theorem continuousAt_zero {f : ℝ≥0 → ℕ} (hf : IsSimpleCountingPath f) : ContinuousAt f 0 :=
  hf.isRightContinuous.continuousAt_of_isBot fun _ ↦ zero_le

/-- A simple counting path has only finitely many discontinuities on each interval `[0, T]`. -/
theorem finite_Iic_not_continuousAt {f : ℝ≥0 → ℕ} (hf : IsSimpleCountingPath f) (T : ℝ≥0) :
    {t ∈ Iic T | ¬ ContinuousAt f t}.Finite := by
  have hIic : (Iic T : Set ℝ≥0) = Icc 0 T := by
    ext t
    simp
  rw [hIic]
  exact hf.monotone.finite_Icc_not_continuousAt 0 T

/-- At every discontinuity of a simple counting path, its left limit is one below its current
value. Positivity of `t` is automatic because a simple counting path is continuous at `0`. -/
theorem leftLim_add_one_eq_of_not_continuousAt {f : ℝ≥0 → ℕ} (hf : IsSimpleCountingPath f)
    {t : ℝ≥0} (ht : ¬ ContinuousAt f t) :
    leftLim f t + 1 = f t := by
  have ht0 : 0 < t := pos_iff_ne_zero.mpr fun h ↦ ht (h ▸ hf.continuousAt_zero)
  exact hf.monotone.leftLim_add_one_eq_of_not_continuousAt hf.isRightContinuous ht
    (hf.le_add_one ht0)

/-- A simple counting path hits a positive level `c` only at a strictly positive time. -/
theorem hittingAfter_Ici_pos {Ω : Type*} {M : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (hf : IsSimpleCountingPath (M · ω)) {c : ℕ} (hc : 0 < c) :
    0 < hittingAfter M (Ici c) 0 ω :=
  isClosed_Ici.lt_hittingAfter_of_isRightContinuous hf.isRightContinuous
    (by simp [hf.apply_zero, hc.ne'])

/-- At a finite hitting time of `Set.Ici c`, a simple counting path takes the exact value `c`. -/
theorem apply_untopA_hittingAfter_Ici {Ω : Type*} {M : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (hf : IsSimpleCountingPath (M · ω)) {c : ℕ}
    (hfin : hittingAfter M (Ici c) 0 ω ≠ ⊤) :
    M (hittingAfter M (Ici c) 0 ω).untopA ω = c := by
  refine hf.isRightContinuous.apply_untopA_hittingAfter_Ici_of_le_add_one
    (by simp [hf.apply_zero]) (fun t ht ↦ ?_) hfin
  obtain ⟨s, hst, hfs⟩ := hf.le_add_one ht
  exact ⟨s, ⟨zero_le, hst⟩, hfs⟩

/-- Along a simple counting path, any finite hitting time of `Set.Ici c` strictly precedes the
hitting time of `Set.Ici (c + 1)`. -/
theorem hittingAfter_Ici_lt_succ {Ω : Type*} {M : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (hf : IsSimpleCountingPath (M · ω)) {c : ℕ}
    (hfin : hittingAfter M (Ici c) 0 ω ≠ ⊤) :
    hittingAfter M (Ici c) 0 ω < hittingAfter M (Ici (c + 1)) 0 ω := by
  refine hf.isRightContinuous.hittingAfter_Ici_lt_succ_of_le_add_one
    (by simp [hf.apply_zero]) (fun t ht ↦ ?_) hfin
  obtain ⟨s, hst, hfs⟩ := hf.le_add_one ht
  exact ⟨s, ⟨zero_le, hst⟩, hfs⟩

end IsSimpleCountingPath

/-! ### Floor laws and integer-valuedness of Poisson increments -/

/-- Taking the natural floor of a real random variable with law `Po(ℝ, r)` recovers the native
Poisson law `Po(r)` on `ℕ`. -/
theorem hasLaw_natFloor_of_hasLaw_map_cast_poissonMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {r : ℝ≥0} (hX : HasLaw X Po(ℝ, r) P) :
    HasLaw (fun ω ↦ ⌊X ω⌋₊) Po(r) P := by
  have hc : Measurable (Nat.cast : ℕ → ℝ) := continuous_of_discreteTopology.measurable
  have hmap : Po(ℝ, r).map Nat.floor = Po(r) := by
    rw [Measure.map_map Nat.measurable_floor hc]
    simp [Function.comp_def]
  simpa only [Function.comp_def, hmap] using
    (hasLaw_map Nat.measurable_floor.aemeasurable).comp hX

/-- A real random variable with law `Po(ℝ, r)` almost surely takes natural-number values. -/
theorem ae_exists_nat_eq_of_hasLaw_map_cast_poissonMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {r : ℝ≥0} (hX : HasLaw X Po(ℝ, r) P) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, X ω = n := by
  have hc : Measurable (Nat.cast : ℕ → ℝ) := continuous_of_discreteTopology.measurable
  have hm : MeasurableSet (range (Nat.cast : ℕ → ℝ))ᶜ :=
    (countable_range (Nat.cast : ℕ → ℝ)).measurableSet.compl
  rw [ae_iff]
  have hpre : {ω | ¬ ∃ n : ℕ, X ω = n} = X ⁻¹' (range (Nat.cast : ℕ → ℝ))ᶜ := by
    ext ω
    simp [eq_comm]
  rw [hpre, ← Measure.map_apply_of_aemeasurable hX.aemeasurable hm, hX.map_eq,
    Measure.map_apply hc hm]
  convert measure_empty (μ := Po(r))
  ext n
  simp

namespace IsFilteredPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {α : ℝ≥0} {N : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- At each fixed time `t`, `N t` almost surely takes natural-number values. -/
theorem ae_exists_nat_eq (h : IsFilteredPoissonProcess ℱ α N P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, N t ω = n :=
  ae_exists_nat_eq_of_hasLaw_map_cast_poissonMeasure (h.hasLaw_eval t)

/-- Between any two fixed times `s ≤ t`, a filtered Poisson process is almost surely nondecreasing.
-/
theorem ae_le (h : IsFilteredPoissonProcess ℱ α N P) {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, N s ω ≤ N t ω := by
  filter_upwards [ae_exists_nat_eq_of_hasLaw_map_cast_poissonMeasure (h.hasLaw_sub hst)] with ω
    ⟨n, hn⟩
  have hsub : N t ω - N s ω = n := hn
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- For any times `s` and `t`, the probability that `N t - N s` exceeds `1` is at most
`(α * (t - s)) ^ 2 / 2` (using truncated subtraction on `ℝ≥0` when `t ≤ s`). -/
theorem measure_sub_gt_one_le (h : IsFilteredPoissonProcess ℱ α N P) (s t : ℝ≥0) :
    P {ω | 1 < N t ω - N s ω} ≤ (((α * (t - s)) ^ 2 / 2 : ℝ≥0) : ℝ≥0∞) := by
  rcases le_total s t with hst | hts
  · have := h.isProbabilityMeasure
    have hfloor := hasLaw_natFloor_of_hasLaw_map_cast_poissonMeasure (h.hasLaw_sub hst)
    have hae : ({ω | 1 < N t ω - N s ω} : Set Ω) =ᵐ[P] {ω | 2 ≤ ⌊(N t - N s) ω⌋₊} := by
      filter_upwards [ae_exists_nat_eq_of_hasLaw_map_cast_poissonMeasure (h.hasLaw_sub hst)] with ω
        ⟨n, hn⟩
      change 1 < N t ω - N s ω ↔ 2 ≤ ⌊N t ω - N s ω⌋₊
      have hsub : N t ω - N s ω = n := hn
      rw [hsub, Nat.floor_natCast, show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Nat.cast_lt]
      omega
    have hreal : P.real {ω | 1 < N t ω - N s ω} ≤ ((α * (t - s) : ℝ≥0) : ℝ) ^ 2 / 2 := by
      rw [measureReal_congr hae, hfloor.measureReal_eq (p := fun n ↦ 2 ≤ n) .of_discrete]
      exact poissonMeasure_real_Ici_two_le (α * (t - s))
    calc
      P {ω | 1 < N t ω - N s ω} = ENNReal.ofReal (P.real {ω | 1 < N t ω - N s ω}) :=
        (ofReal_measureReal (measure_ne_top P _)).symm
      _ ≤ ENNReal.ofReal (((α * (t - s) : ℝ≥0) : ℝ) ^ 2 / 2) := ENNReal.ofReal_le_ofReal hreal
      _ = (((α * (t - s)) ^ 2 / 2 : ℝ≥0) : ℝ≥0∞) := by
        rw [← NNReal.coe_pow, ← NNReal.coe_ofNat, ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal]
  · have hzero : P {ω | 1 < N t ω - N s ω} = 0 := by
      have hae : ∀ᵐ ω ∂P, ¬ (1 < N t ω - N s ω) :=
        (h.ae_le hts).mono fun _ hle hgt ↦ by linarith
      simpa only [ae_iff, Classical.not_not] using hae
    simp [hzero]

/-! ### Dyadic grid and good sample-path event -/

private noncomputable def dyadicTime (m j : ℕ) : ℝ≥0 :=
  (j : ℝ≥0) / (2 : ℝ≥0) ^ m

private lemma dyadicTime_zero (m : ℕ) : dyadicTime m 0 = 0 := by
  simp [dyadicTime]

private lemma dyadicTime_one (m : ℕ) : dyadicTime m 1 = (2⁻¹ : ℝ≥0) ^ m := by
  rw [dyadicTime, Nat.cast_one, one_div, inv_pow]

private lemma dyadicTime_strictMono (m : ℕ) : StrictMono (dyadicTime m) := fun _ _ hj ↦
  div_lt_div_of_pos_right (Nat.cast_lt.mpr hj) (by positivity)

private lemma dyadicTime_add_two_sub (m k : ℕ) :
    dyadicTime m (k + 2) - dyadicTime m k = 2 * (2⁻¹ : ℝ≥0) ^ m := by
  have hadd : dyadicTime m (k + 2) = dyadicTime m k + 2 * (2⁻¹ : ℝ≥0) ^ m := by
    simp only [dyadicTime, Nat.cast_add, Nat.cast_ofNat, div_eq_mul_inv, inv_pow]
    ring
  rw [hadd, add_tsub_cancel_left]

private lemma dyadicTime_floor_le (m : ℕ) (t : ℝ≥0) :
    dyadicTime m ⌊(t : ℝ) * (2 : ℝ) ^ m⌋₊ ≤ t := by
  rw [← NNReal.coe_le_coe, dyadicTime, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_ofNat, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

private lemma lt_dyadicTime_floor_add_one (m : ℕ) (t : ℝ≥0) :
    t < dyadicTime m (⌊(t : ℝ) * (2 : ℝ) ^ m⌋₊ + 1) := by
  rw [← NNReal.coe_lt_coe, dyadicTime, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_ofNat, lt_div_iff₀ (by positivity), Nat.cast_add, Nat.cast_one]
  exact Nat.lt_floor_add_one _

private lemma dyadicTime_floor_add_one_sub_le (m : ℕ) (t : ℝ≥0) :
    dyadicTime m (⌊(t : ℝ) * (2 : ℝ) ^ m⌋₊ + 1) - t ≤ (2⁻¹ : ℝ≥0) ^ m := by
  have hstep : dyadicTime m (⌊(t : ℝ) * (2 : ℝ) ^ m⌋₊ + 1) =
      dyadicTime m ⌊(t : ℝ) * (2 : ℝ) ^ m⌋₊ + (2⁻¹ : ℝ≥0) ^ m := by
    simp only [dyadicTime, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, inv_pow]
    ring
  exact (tsub_le_tsub_left (dyadicTime_floor_le m t) _).trans_eq
    (by rw [hstep, add_tsub_cancel_left])

private instance (t : ℝ≥0) : Nonempty {p : ℕ × ℕ // t < dyadicTime p.1 p.2} :=
  ⟨⟨(0, ⌊(t : ℝ)⌋₊ + 1), by simpa using lt_dyadicTime_floor_add_one 0 t⟩⟩

private structure IsDyadicGood (N : ℝ≥0 → Ω → ℝ) (ω : Ω) : Prop where
  exists_nat (m j : ℕ) : ∃ n : ℕ, N (dyadicTime m j) ω = n
  mono ⦃m₁ j₁ m₂ j₂ : ℕ⦄ :
    dyadicTime m₁ j₁ ≤ dyadicTime m₂ j₂ → N (dyadicTime m₁ j₁) ω ≤ N (dyadicTime m₂ j₂) ω
  zero : ∃ m : ℕ, N (dyadicTime m 1) ω = 0
  jump (T : ℕ) : ∃ m : ℕ, ∀ k < (T + 1) * 2 ^ m,
    N (dyadicTime m (k + 2)) ω - N (dyadicTime m k) ω ≤ 1

private lemma measurableSet_isDyadicGood (hN : ∀ t, Measurable (N t)) :
    MeasurableSet {ω | IsDyadicGood N ω} := by
  have heq : {ω | IsDyadicGood N ω} =
      (⋂ (m : ℕ) (j : ℕ), ⋃ n : ℕ, {ω | N (dyadicTime m j) ω = n}) ∩
      (⋂ (m₁ : ℕ) (j₁ : ℕ) (m₂ : ℕ) (j₂ : ℕ) (_ : dyadicTime m₁ j₁ ≤ dyadicTime m₂ j₂),
        {ω | N (dyadicTime m₁ j₁) ω ≤ N (dyadicTime m₂ j₂) ω}) ∩
      (⋃ m : ℕ, {ω | N (dyadicTime m 1) ω = 0}) ∩
      (⋂ T : ℕ, ⋃ m : ℕ, ⋂ (k : ℕ) (_ : k < (T + 1) * 2 ^ m),
        {ω | N (dyadicTime m (k + 2)) ω - N (dyadicTime m k) ω ≤ 1}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
    exact ⟨fun h ↦ ⟨⟨⟨h.1, h.2⟩, h.3⟩, h.4⟩, fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ ↦ ⟨h1, h2, h3, h4⟩⟩
  have h1 : MeasurableSet (⋂ (m : ℕ) (j : ℕ), ⋃ n : ℕ, {ω | N (dyadicTime m j) ω = n}) :=
    .iInter fun _ ↦ .iInter fun _ ↦ .iUnion fun _ ↦ measurableSet_eq_fun (hN _) measurable_const
  have h2 : MeasurableSet
      (⋂ (m₁ : ℕ) (j₁ : ℕ) (m₂ : ℕ) (j₂ : ℕ) (_ : dyadicTime m₁ j₁ ≤ dyadicTime m₂ j₂),
        {ω | N (dyadicTime m₁ j₁) ω ≤ N (dyadicTime m₂ j₂) ω}) :=
    .iInter fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦
      measurableSet_le (hN _) (hN _)
  have h3 : MeasurableSet (⋃ m : ℕ, {ω | N (dyadicTime m 1) ω = 0}) :=
    .iUnion fun _ ↦ measurableSet_eq_fun (hN _) measurable_const
  have h4 : MeasurableSet (⋂ T : ℕ, ⋃ m : ℕ, ⋂ (k : ℕ) (_ : k < (T + 1) * 2 ^ m),
      {ω | N (dyadicTime m (k + 2)) ω - N (dyadicTime m k) ω ≤ 1}) :=
    .iInter fun _ ↦ .iUnion fun _ ↦ .iInter fun _ ↦ .iInter fun _ ↦
      measurableSet_le ((hN _).sub (hN _)) measurable_const
  rw [heq]
  exact ((h1.inter h2).inter h3).inter h4

private lemma ae_dyadic_double_cell_le_one (h : IsFilteredPoissonProcess ℱ α N P) (T : ℕ) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, ∀ k < (T + 1) * 2 ^ m,
      N (dyadicTime m (k + 2)) ω - N (dyadicTime m k) ω ≤ 1 := by
  let bad : ℕ → Set Ω := fun m ↦
    ⋃ k ∈ Finset.range ((T + 1) * 2 ^ m),
      {ω | 1 < N (dyadicTime m (k + 2)) ω - N (dyadicTime m k) ω}
  have hbad (m : ℕ) :
      P (bad m) ≤ ((2 * (T + 1) * α ^ 2 : ℝ≥0) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ m := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hterm (k : ℕ) :
        P {ω | 1 < N (dyadicTime m (k + 2)) ω - N (dyadicTime m k) ω} ≤
          (((α * (2 * (2⁻¹ : ℝ≥0) ^ m)) ^ 2 / 2 : ℝ≥0) : ℝ≥0∞) := by
      simpa only [dyadicTime_add_two_sub] using
        h.measure_sub_gt_one_le (dyadicTime m k) (dyadicTime m (k + 2))
    refine (Finset.sum_le_sum fun k _ ↦ hterm k).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hnn : (((T + 1) * 2 ^ m : ℕ) : ℝ≥0) * ((α * (2 * (2⁻¹ : ℝ≥0) ^ m)) ^ 2 / 2) =
        (2 * (T + 1) * α ^ 2) * (2⁻¹ : ℝ≥0) ^ m := by
      have h2 : (2 : ℝ≥0) ^ m * (2⁻¹ : ℝ≥0) ^ m = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
      rw [div_eq_mul_inv, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      calc
        ((T : ℝ≥0) + 1) * 2 ^ m * ((α * (2 * (2⁻¹ : ℝ≥0) ^ m)) ^ 2 * 2⁻¹) =
            2 * ((T : ℝ≥0) + 1) * α ^ 2 * ((2 : ℝ≥0) ^ m * (2⁻¹ : ℝ≥0) ^ m) *
              (2⁻¹ : ℝ≥0) ^ m * (2 * 2⁻¹) := by ring
        _ = (2 * (T + 1) * α ^ 2) * (2⁻¹ : ℝ≥0) ^ m := by
          rw [h2, mul_inv_cancel₀ two_ne_zero, mul_one, mul_one]
    exact le_of_eq <| by
      rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul, hnn, ENNReal.coe_mul, ENNReal.coe_pow,
        ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]
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
  have hnat : ∀ᵐ ω ∂P, ∀ m j : ℕ, ∃ n : ℕ, N (dyadicTime m j) ω = n :=
    ae_all_iff.mpr fun m ↦ ae_all_iff.mpr fun j ↦ h.ae_exists_nat_eq (dyadicTime m j)
  have hmono : ∀ᵐ ω ∂P, ∀ m₁ j₁ m₂ j₂ : ℕ, dyadicTime m₁ j₁ ≤ dyadicTime m₂ j₂ →
      N (dyadicTime m₁ j₁) ω ≤ N (dyadicTime m₂ j₂) ω :=
    ae_all_iff.mpr fun m₁ ↦ ae_all_iff.mpr fun j₁ ↦ ae_all_iff.mpr fun m₂ ↦
      ae_all_iff.mpr fun j₂ ↦ by
        by_cases hle : dyadicTime m₁ j₁ ≤ dyadicTime m₂ j₂
        · exact (h.ae_le hle).mono fun _ hω _ ↦ hω
        · exact ae_of_all _ fun _ hbad ↦ False.elim (hle hbad)
  have hzero : ∀ᵐ ω ∂P, ∃ m : ℕ, N (dyadicTime m 1) ω = 0 := by
    filter_upwards [h.ae_eventually_eval_add_two_inv_pow_eq 0, h.eval_zero_ae_eq_zero] with ω hω h0
    obtain ⟨m, hm⟩ := hω.exists
    exact ⟨m, by simpa [dyadicTime_one, h0] using hm⟩
  have hjump : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ m : ℕ, ∀ k < (T + 1) * 2 ^ m,
      N (dyadicTime m (k + 2)) ω - N (dyadicTime m k) ω ≤ 1 :=
    ae_all_iff.mpr fun T ↦ ae_dyadic_double_cell_le_one h T
  filter_upwards [hnat, hmono, hzero, hjump] with ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩

/-! ### Dyadic right-hand regularization -/

@[irreducible]
private noncomputable def dyadicReg (N : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : Ω → ℕ :=
  {ω | IsDyadicGood N ω}.indicator fun ω ↦
    ⨅ p : {p : ℕ × ℕ // t < dyadicTime p.1 p.2}, ⌊N (dyadicTime p.val.1 p.val.2) ω⌋₊

private lemma dyadicReg_of_good {ω : Ω} (hω : IsDyadicGood N ω) (t : ℝ≥0) :
    dyadicReg N t ω =
      ⨅ p : {p : ℕ × ℕ // t < dyadicTime p.1 p.2}, ⌊N (dyadicTime p.val.1 p.val.2) ω⌋₊ := by
  unfold dyadicReg
  exact indicator_of_mem hω _

private lemma dyadicReg_of_not_good {ω : Ω} (hω : ¬ IsDyadicGood N ω) (t : ℝ≥0) :
    dyadicReg N t ω = 0 := by
  unfold dyadicReg
  exact indicator_of_notMem hω _

private lemma measurable_dyadicReg (hN : ∀ t, Measurable (N t)) (t : ℝ≥0) :
    Measurable (dyadicReg N t) := by
  unfold dyadicReg
  exact (Measurable.iInf fun (p : {p : ℕ × ℕ // t < dyadicTime p.1 p.2}) ↦
    (hN (dyadicTime p.val.1 p.val.2)).nat_floor).indicator (measurableSet_isDyadicGood hN)

private lemma dyadicReg_le_of_lt {ω : Ω} (hω : IsDyadicGood N ω) {t : ℝ≥0} {m j : ℕ}
    (ht : t < dyadicTime m j) :
    dyadicReg N t ω ≤ ⌊N (dyadicTime m j) ω⌋₊ := by
  rw [dyadicReg_of_good hω]
  exact ciInf_le (OrderBot.bddBelow _) (⟨(m, j), ht⟩ : {p : ℕ × ℕ // t < dyadicTime p.1 p.2})

private lemma le_dyadicReg_of_le {ω : Ω} (hω : IsDyadicGood N ω) {s : ℝ≥0} {m k : ℕ}
    (hs : dyadicTime m k ≤ s) :
    ⌊N (dyadicTime m k) ω⌋₊ ≤ dyadicReg N s ω := by
  rw [dyadicReg_of_good hω]
  exact le_ciInf fun p ↦ Nat.floor_mono (hω.mono (hs.trans p.property.le))

private lemma floor_dyadicTime_add_two_le {ω : Ω} (hω : IsDyadicGood N ω) {m k : ℕ}
    (hle : N (dyadicTime m (k + 2)) ω - N (dyadicTime m k) ω ≤ 1) :
    ⌊N (dyadicTime m (k + 2)) ω⌋₊ ≤ ⌊N (dyadicTime m k) ω⌋₊ + 1 := by
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
  let F : {p : ℕ × ℕ // t < dyadicTime p.1 p.2} → ℕ :=
    fun p ↦ ⌊N (dyadicTime p.val.1 p.val.2) ω⌋₊
  obtain ⟨p, hp⟩ := mem_range.mp (Nat.sInf_mem (range_nonempty F))
  have hp' : F p = dyadicReg N t ω := by
    simpa only [dyadicReg_of_good hω, iInf] using hp
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT p.property] with s hs
  exact le_antisymm (dyadicReg_monotone hω hs.1.le) ((dyadicReg_le_of_lt hω hs.2).trans_eq hp')

private lemma dyadicReg_le_add_one {ω : Ω} (hω : IsDyadicGood N ω) ⦃t : ℝ≥0⦄ (ht : 0 < t) :
    ∃ s < t, dyadicReg N t ω ≤ dyadicReg N s ω + 1 := by
  let T : ℕ := ⌊(t : ℝ)⌋₊
  obtain ⟨m, hm⟩ := hω.jump T
  by_cases hsmall : t < dyadicTime m 1
  · refine ⟨0, ht, ?_⟩
    have hlt2 : t < dyadicTime m 2 := hsmall.trans (dyadicTime_strictMono m one_lt_two)
    exact (dyadicReg_le_of_lt hω hlt2).trans
      ((floor_dyadicTime_add_two_le hω (hm 0 (by positivity))).trans
        (Nat.add_le_add_right (le_dyadicReg_of_le hω (dyadicTime_zero m).le) 1))
  · let j : ℕ := ⌊(t : ℝ) * (2 : ℝ) ^ m⌋₊
    have hj1 : 1 ≤ j := Nat.le_floor <| by
      have h1 : dyadicTime m 1 ≤ t := not_lt.mp hsmall
      simpa only [Nat.cast_one] using
        (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)).mp
          (by simpa [dyadicTime] using NNReal.coe_le_coe.mpr h1)
    have hjT : j < (T + 1) * 2 ^ m := by
      rw [← Nat.cast_lt (α := ℝ)]
      calc
        (j : ℝ) ≤ (t : ℝ) * (2 : ℝ) ^ m := Nat.floor_le (by positivity)
        _ < ((T : ℝ) + 1) * (2 : ℝ) ^ m :=
          mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (t : ℝ)) (by positivity)
        _ = (((T + 1) * 2 ^ m : ℕ) : ℝ) := by push_cast; ring
    have hst : dyadicTime m (j - 1) < t :=
      (dyadicTime_strictMono m (by omega : j - 1 < j)).trans_le (dyadicTime_floor_le m t)
    have htk2 : t < dyadicTime m (j - 1 + 2) := by
      simpa only [show j - 1 + 2 = j + 1 by omega] using lt_dyadicTime_floor_add_one m t
    refine ⟨dyadicTime m (j - 1), hst, ?_⟩
    exact (dyadicReg_le_of_lt hω htk2).trans
      ((floor_dyadicTime_add_two_le hω (hm (j - 1) (by omega))).trans
        (Nat.add_le_add_right (le_dyadicReg_of_le hω le_rfl) 1))

private lemma isSimpleCountingPath_dyadicReg (ω : Ω) :
    IsSimpleCountingPath (dyadicReg N · ω) := by
  by_cases hω : IsDyadicGood N ω
  · refine ⟨?_, dyadicReg_monotone hω, dyadicReg_isRightContinuous hω, dyadicReg_le_add_one hω⟩
    obtain ⟨m, hm⟩ := hω.zero
    have hpos : (0 : ℝ≥0) < dyadicTime m 1 := by
      rw [dyadicTime_one]
      positivity
    exact Nat.eq_zero_of_le_zero ((dyadicReg_le_of_lt hω hpos).trans_eq (by simp [hm]))
  · have hzero : (dyadicReg N · ω) = 0 := funext fun t ↦ dyadicReg_of_not_good hω t
    rw [hzero]
    exact IsSimpleCountingPath.zero

private lemma dyadicReg_ae_eq (h : IsFilteredPoissonProcess ℱ α N P) (t : ℝ≥0) :
    (fun ω ↦ (dyadicReg N t ω : ℝ)) =ᵐ[P] N t := by
  let u : ℕ → ℝ≥0 := fun n ↦ dyadicTime n (⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊ + 1)
  have hsum : (∑' n, ((u n - t : ℝ≥0) : ℝ≥0∞)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ?_
    rw [← ENNReal.tsum_geometric_two]
    exact tsum_le_tsum fun n ↦
      (ENNReal.coe_le_coe.mpr (dyadicTime_floor_add_one_sub_le n t)).trans_eq
        (by simp only [ENNReal.coe_pow, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat])
  have habove : ∀ᵐ ω ∂P, ∀ p : {p : ℕ × ℕ // t < dyadicTime p.1 p.2},
      N t ω ≤ N (dyadicTime p.val.1 p.val.2) ω :=
    ae_all_iff.mpr fun p ↦ h.ae_le p.property.le
  filter_upwards [ae_isDyadicGood h, h.ae_exists_nat_eq t, habove,
    h.ae_eventually_eval_eq_of_tsum_sub_ne_top
      (fun n ↦ (lt_dyadicTime_floor_add_one n t).le) hsum] with ω hω ⟨c, hc⟩ hle hev
  obtain ⟨n, hn⟩ := hev.exists
  have hupper : dyadicReg N t ω ≤ c := by
    refine (dyadicReg_le_of_lt hω (lt_dyadicTime_floor_add_one n t)).trans_eq ?_
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

end IsFilteredPoissonProcess

end TauCeti.Probability
