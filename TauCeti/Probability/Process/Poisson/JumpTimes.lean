/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Process.Poisson.Regularization
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Probability.Distributions.Poisson.Tail
import TauCeti.Probability.Process.Poisson.Microscopic

/-!
# Arrival times and gamma laws for filtered Poisson processes

For a natural-valued counting process `M : ℝ≥0 → Ω → ℕ` whose real cast is a homogeneous Poisson
process of rate `α` relative to `ℱ`:

* `M t` has the native Poisson law `Po(α * t)` and `M t - M s` has law `Po(α * (t - s))` for all
  `s, t`, without any pathwise hypothesis;
* `M` is adapted to `ℱ`, so when its paths are everywhere right-continuous (for instance, when
  every path is a simple counting path), the arrival time `hittingAfter M (Set.Ici c) 0` is a
  stopping time on the raw filtration `ℱ`;
* assuming only almost-sure right-continuity `∀ᵐ ω ∂P, IsRightContinuous (M · ω)`, sample paths of
  `M` are automatically almost surely monotone and almost surely simple counting paths, and
  `hittingAfter M (Set.Ici (k + 1)) 0` is `P`-almost everywhere measurable and satisfies the
  Poisson–gamma duality
  `P.real {ω | hittingAfter M (Set.Ici (k + 1)) 0 ω ≤ t} = regularizedGamma (k + 1) (α * t)`;
* for `0 < α` every arrival time is almost surely finite (without any pathwise hypothesis), whereas
  at rate `α = 0` under almost-sure right-continuity every positive arrival time is almost surely
  `⊤`; when `0 < α` and `M` is almost surely right-continuous,
  `((hittingAfter M (Set.Ici (k + 1)) 0 ω).untopA : ℝ)` has law `gammaMeasure (k + 1) α` (in
  particular, `expMeasure α` at `k = 0`).

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §3.
* J. F. C. Kingman, *Poisson Processes*, Oxford University Press, 1993, §4.1.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability.IsFilteredPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {α : ℝ≥0} {M : ℝ≥0 → Ω → ℕ} {P : Measure Ω}

/-! ### Native natural-valued marginals and adaptedness -/

/-- A natural-valued process whose real cast is a filtered Poisson process relative to `ℱ` is
adapted to `ℱ`. -/
theorem adapted_nat (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P) :
    Adapted ℱ M := fun t ↦ by
  let : MeasurableSpace Ω := ℱ t
  simpa only [Nat.floor_natCast] using (h.adapted t).nat_floor

/-- Each fixed-time count `M t` of a natural-valued filtered Poisson process is ambient-measurable.
-/
theorem measurable_eval_nat (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (t : ℝ≥0) : Measurable (M t) :=
  (h.adapted_nat t).mono (ℱ.le t) le_rfl

/-- The count `M t` has the native Poisson law `Po(α * t)` on `ℕ`. -/
theorem hasLaw_eval_nat (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P) (t : ℝ≥0) :
    HasLaw (M t) Po(α * t) P := by
  simpa only [Nat.floor_natCast] using
    hasLaw_natFloor_of_hasLaw_map_cast_poissonMeasure (h.hasLaw_eval t)

/-- For any times `s` and `t`, the truncated natural-number increment `M t - M s` has the native
Poisson law `Po(α * (t - s))` (both sides reducing to the point mass at `0` when `t ≤ s`). -/
theorem hasLaw_sub_nat (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (s t : ℝ≥0) :
    HasLaw (fun ω ↦ M t ω - M s ω) Po(α * (t - s)) P := by
  rcases le_total s t with hst | hts
  · refine (hasLaw_natFloor_of_hasLaw_map_cast_poissonMeasure (h.hasLaw_sub hst)).congr ?_
    filter_upwards [h.ae_le hst] with ω hω
    have hle : M s ω ≤ M t ω := Nat.cast_le.mp hω
    change M t ω - M s ω = ⌊(M t ω : ℝ) - (M s ω : ℝ)⌋₊
    rw [← Nat.cast_sub hle, Nat.floor_natCast]
  · have h0 : Po(α * (t - s)) = Po(α * (s - s)) := by
      rw [tsub_eq_zero_of_le hts, tsub_self]
    rw [h0]
    refine (hasLaw_natFloor_of_hasLaw_map_cast_poissonMeasure
      (h.hasLaw_sub (le_rfl : s ≤ s))).congr ?_
    filter_upwards [h.ae_le hts] with ω hω
    have hle : M t ω ≤ M s ω := Nat.cast_le.mp hω
    change M t ω - M s ω = ⌊(M s ω : ℝ) - (M s ω : ℝ)⌋₊
    simp [Nat.sub_eq_zero_of_le hle]

/-- When every sample path of `M` is right-continuous, the `c`-th arrival time is a stopping time
on the raw filtration `ℱ`. Monotonicity is not needed because `Ici c` is clopen in `ℕ` and `ℝ≥0` is
densely ordered and separable. -/
theorem isStoppingTime_hittingAfter_Ici
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ ω, IsRightContinuous (M · ω)) (c : ℕ) :
    IsStoppingTime ℱ (hittingAfter M (Ici c) 0) := by
  let q : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0
  have hdense : DenseRange q := TopologicalSpace.denseRange_denseSeq ℝ≥0
  intro t
  have heq : {ω | hittingAfter M (Ici c) 0 ω ≤ t} =
      {ω | c ≤ M t ω} ∪ ⋃ (n : ℕ) (_ : q n ≤ t), {ω | c ≤ M (q n) ω} := by
    ext ω
    simp only [mem_ofPred_eq, isClosed_Ici.hittingAfter_le_iff_of_isRightContinuous (hrc ω),
      mem_Icc, zero_le, true_and, mem_Ici, mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨u, hut, hcu⟩
      rcases hut.eq_or_lt with rfl | hut
      · exact Or.inl hcu
      · obtain ⟨u', hu', huu'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hut).mp
          ((hrc ω u) ((isOpen_discrete (Ici c)).mem_nhds hcu))
        obtain ⟨n, hn⟩ := hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr (lt_min hu' hut))
        exact Or.inr ⟨n, (hn.2.trans_le (min_le_right _ _)).le,
          huu' ⟨hn.1, hn.2.trans_le (min_le_left _ _)⟩⟩
    · rintro (hct | ⟨n, hqn, hcn⟩)
      · exact ⟨t, le_rfl, hct⟩
      · exact ⟨q n, hqn, hcn⟩
  rw [heq]
  exact (h.adapted_nat t measurableSet_Ici).union
    (.iUnion fun n ↦ .iUnion fun hqn ↦
      ((h.adapted_nat (q n)).mono (ℱ.mono hqn) le_rfl) measurableSet_Ici)

/-! ### Almost-sure path regularity and measurability under right-continuity -/

/-- Almost-sure right-continuity of a natural-valued filtered Poisson process implies almost-sure
monotonicity of its sample paths. -/
theorem ae_monotone_of_isRightContinuous
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) :
    ∀ᵐ ω ∂P, Monotone (M · ω) := by
  let q : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0
  have hdense : DenseRange q := TopologicalSpace.denseRange_denseSeq ℝ≥0
  have hqmono : ∀ᵐ ω ∂P, ∀ i j : ℕ, q i ≤ q j → M (q i) ω ≤ M (q j) ω :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ by
      by_cases hle : q i ≤ q j
      · exact (h.ae_le hle).mono fun _ hω _ ↦ Nat.cast_le.mp hω
      · exact ae_of_all _ fun _ hbad ↦ False.elim (hle hbad)
  filter_upwards [hrc, hqmono] with ω hrcω hq s t hst
  rcases hst.eq_or_lt with rfl | hst
  · exact le_rfl
  · obtain ⟨s', hs', hss'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hst).mp
      ((hrcω s) ((isOpen_discrete {M s ω}).mem_nhds rfl))
    obtain ⟨i, hi⟩ := hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr (lt_min hs' hst))
    have hsi : M (q i) ω = M s ω := hss' ⟨hi.1, hi.2.trans_le (min_le_left _ _)⟩
    obtain ⟨t', ht', htt'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (lt_add_one t)).mp
      ((hrcω t) ((isOpen_discrete {M t ω}).mem_nhds rfl))
    obtain ⟨j, hj⟩ := hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr ht')
    have htj : M (q j) ω = M t ω := htt' hj
    have hij : q i ≤ q j := ((hi.2.trans_le (min_le_right _ _)).trans hj.1).le
    exact hsi.symm.trans_le ((hq i j hij).trans_eq htj)

/-- Almost-sure right-continuity upgrades a natural-valued filtered Poisson process to have almost
surely simple counting paths. -/
theorem ae_isSimpleCountingPath_of_isRightContinuous
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) :
    ∀ᵐ ω ∂P, IsSimpleCountingPath (M · ω) := by
  have hmono := h.ae_monotone_of_isRightContinuous hrc
  have hjump := ae_count_le_add_one_of_hasLaw_sub_poissonMeasure (P := P) (N := M) hmono α
    fun s t _ ↦ h.hasLaw_sub_nat s t
  filter_upwards [h.eval_zero_ae_eq_zero, hmono, hrc, hjump] with ω h0 hm hr hj
  exact ⟨Nat.cast_eq_zero.mp h0, hm, hr, hj⟩

private lemma hittingAfter_Ici_eq_iInf_denseSeq {ω : Ω} (hrc : IsRightContinuous (M · ω)) (c : ℕ) :
    hittingAfter M (Ici c) 0 ω =
      ⨅ n : ℕ, if c ≤ M (TopologicalSpace.denseSeq ℝ≥0 n) ω
        then (TopologicalSpace.denseSeq ℝ≥0 n : WithTop ℝ≥0) else ⊤ := by
  let q : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0
  have hdense : DenseRange q := TopologicalSpace.denseRange_denseSeq ℝ≥0
  let g : WithTop ℝ≥0 := ⨅ n : ℕ, if c ≤ M (q n) ω then (q n : WithTop ℝ≥0) else ⊤
  refine le_antisymm ?_ ?_
  · refine le_iInf fun n ↦ ?_
    split_ifs with hqn
    · exact hittingAfter_le_of_mem zero_le hqn
    · exact le_top
  · by_cases hfin : hittingAfter M (Ici c) 0 ω = ⊤
    · simp [hfin]
    · obtain ⟨u, hu, -, hcu⟩ :=
        isClosed_Ici.exists_hittingAfter_eq_of_isRightContinuous hrc hfin
      rw [hu]
      have hg_le (ε : ℝ≥0) (hε : 0 < ε) : g ≤ ((u + ε : ℝ≥0) : WithTop ℝ≥0) := by
        obtain ⟨u', hu', huu'⟩ :=
          (mem_nhdsGT_iff_exists_Ioo_subset' (lt_add_of_pos_right u hε)).mp
            ((hrc u) ((isOpen_discrete (Ici c)).mem_nhds hcu))
        obtain ⟨n, hn⟩ := hdense.exists_mem_open isOpen_Ioo
          (nonempty_Ioo.mpr (lt_min hu' (lt_add_of_pos_right u hε)))
        have hcn : c ≤ M (q n) ω := huu' ⟨hn.1, hn.2.trans_le (min_le_left _ _)⟩
        refine (iInf_le _ n).trans ?_
        simp only [hcn, ↓reduceIte, WithTop.coe_le_coe]
        exact (hn.2.trans_le (min_le_right _ _)).le
      have hg_ne_top : g ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (hg_le 1 one_pos)
      obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hg_ne_top
      change g ≤ ↑u
      rw [← hv, WithTop.coe_le_coe]
      refine le_of_not_gt fun huv ↦ ?_
      have hpos : 0 < (v - u) / 2 := div_pos (tsub_pos_of_lt huv) two_pos
      have hvle : v ≤ u + (v - u) / 2 := WithTop.coe_le_coe.mp (hv ▸ hg_le _ hpos)
      have hlt : u + (v - u) / 2 < v := by
        rw [← NNReal.coe_lt_coe]
        push_cast [NNReal.coe_sub huv.le]
        linarith [NNReal.coe_lt_coe.mpr huv]
      exact hlt.not_ge hvle

/-- Under almost-sure right-continuity of `M`, the arrival time `hittingAfter M (Set.Ici c) 0` is
`P`-almost everywhere measurable. -/
theorem aemeasurable_hittingAfter_Ici
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) (c : ℕ) :
    AEMeasurable (hittingAfter M (Ici c) 0) P := by
  let q : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0
  have hm : Measurable fun ω ↦
      ⨅ n : ℕ, if c ≤ M (q n) ω then (q n : WithTop ℝ≥0) else ⊤ :=
    Measurable.iInf fun n ↦ Measurable.ite
      ((h.measurable_eval_nat (q n)) measurableSet_Ici) measurable_const measurable_const
  exact hm.aemeasurable.congr
    (hrc.mono fun _ hrcω ↦ (hittingAfter_Ici_eq_iInf_denseSeq hrcω c).symm)

/-! ### Arrival-time distributions -/

/-- **Poisson–gamma arrival-time duality.** For a right-continuous natural-valued filtered Poisson
process of rate `α`, the `(k + 1)`-st arrival occurs by time `t` with probability
`regularizedGamma (k + 1) (α * t)`. -/
theorem measureReal_hittingAfter_Ici_le
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) (k : ℕ) (t : ℝ≥0) :
    P.real {ω | hittingAfter M (Ici (k + 1)) 0 ω ≤ t} = regularizedGamma (k + 1) (α * t) := by
  have hae : ({ω | hittingAfter M (Ici (k + 1)) 0 ω ≤ t} : Set Ω) =ᵐ[P] {ω | k < M t ω} := by
    filter_upwards [h.ae_monotone_of_isRightContinuous hrc, hrc] with ω hmonoω hrcω
    simp only [hrcω.hittingAfter_Ici_le_iff_of_monotone hmonoω, zero_le, true_and]
    omega
  rw [measureReal_congr hae]
  simpa only [NNReal.coe_mul] using
    measureReal_lt_of_hasLaw_poissonMeasure (h.hasLaw_eval_nat t) k

/-- At rate `0`, every positive arrival time `(k + 1)` is almost surely `⊤`. -/
theorem hittingAfter_Ici_ae_eq_top
    (h : IsFilteredPoissonProcess ℱ 0 (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) (k : ℕ) :
    ∀ᵐ ω ∂P, hittingAfter M (Ici (k + 1)) 0 ω = ⊤ := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, (M n ω : ℝ) = 0 :=
    ae_all_iff.mpr fun n ↦ h.eval_ae_eq_zero n
  filter_upwards [h.ae_monotone_of_isRightContinuous hrc, hall] with ω hmono hzero
  rw [hittingAfter_eq_top_iff]
  intro t _ ht
  obtain ⟨n, htn⟩ := exists_nat_gt t
  have hn0 : M n ω = 0 := Nat.cast_eq_zero.mp (hzero n)
  have ht0 : M t ω = 0 := Nat.eq_zero_of_le_zero ((hmono htn.le).trans_eq hn0)
  exact (Nat.succ_ne_zero k) (Nat.eq_zero_of_le_zero (ht0 ▸ ht))

/-- At positive rate `0 < α`, every arrival time `(k + 1)` is almost surely finite, without any
pathwise regularity assumption. This fails at `α = 0` by `hittingAfter_Ici_ae_eq_top`. -/
theorem hittingAfter_Ici_ae_ne_top
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hα : 0 < α) (k : ℕ) :
    ∀ᵐ ω ∂P, hittingAfter M (Ici (k + 1)) 0 ω ≠ ⊤ := by
  have := h.isProbabilityMeasure
  let B : ℕ → Set Ω := fun n ↦ {ω | M n ω ≤ k}
  have hlim : Tendsto (fun n : ℕ ↦ P.real (B n)) atTop (𝓝 0) := by
    have hBn (n : ℕ) : P.real (B n) = 1 - regularizedGamma (k + 1) ((α : ℝ) * n) := by
      simpa only [B, NNReal.coe_mul, NNReal.coe_natCast] using
        measureReal_le_of_hasLaw_poissonMeasure (h.hasLaw_eval_nat n) k
    simp_rw [hBn]
    have hscale : Tendsto (fun n : ℕ ↦ (α : ℝ) * n) atTop atTop :=
      Tendsto.const_mul_atTop (NNReal.coe_pos.mpr hα) tendsto_natCast_atTop_atTop
    have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_regularizedGamma_atTop (by positivity : (0 : ℝ) < k + 1)).comp hscale)
    simpa only [Function.comp_def, sub_self] using hsub
  have hnull : P (⋂ n : ℕ, B n) = 0 := by
    rw [← measureReal_eq_zero_iff]
    refine le_antisymm (ge_of_tendsto hlim (Eventually.of_forall fun n ↦ ?_)) measureReal_nonneg
    exact measureReal_mono (iInter_subset B n)
  have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ n : ℕ, B n := by
    rw [ae_iff]
    simpa only [Classical.not_not, ofPred_mem_eq] using hnull
  filter_upwards [hae] with ω hnot htop
  refine hnot (mem_iInter.mpr fun n ↦ ?_)
  change M n ω ≤ k
  exact not_lt.mp fun hlt ↦
    WithTop.coe_ne_top (top_unique (htop ▸ hittingAfter_le_of_mem zero_le hlt))

/-- **Gamma law of the `(k + 1)`-st arrival time.** For `0 < α`, the real-valued `(k + 1)`-st
arrival time `((hittingAfter M (Set.Ici (k + 1)) 0 ω).untopA : ℝ)` has law
`gammaMeasure (k + 1) α`. -/
theorem hasLaw_untopA_hittingAfter_Ici_gammaMeasure
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) (hα : 0 < α) (k : ℕ) :
    HasLaw (fun ω ↦ ((hittingAfter M (Ici (k + 1)) 0 ω).untopA : ℝ))
      (gammaMeasure (k + 1) α) P := by
  have := h.isProbabilityMeasure
  let Y : Ω → ℝ := fun ω ↦ ((hittingAfter M (Ici (k + 1)) 0 ω).untopA : ℝ)
  have hY : AEMeasurable Y P :=
    (NNReal.continuous_coe.measurable.comp WithTop.measurable_untopA).comp_aemeasurable
      (h.aemeasurable_hittingAfter_Ici hrc (k + 1))
  have hshape : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hrate : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα
  have : IsProbabilityMeasure (gammaMeasure (k + 1) α) :=
    isProbabilityMeasure_gammaMeasure hshape hrate
  refine ⟨hY, Measure.eq_of_cdf (P.map Y) (gammaMeasure (k + 1) α)
    (StieltjesFunction.ext fun x ↦ ?_)⟩
  rw [Measure.cdf_map P Y hY x, cdf_gammaMeasure_eq hshape hrate x]
  rcases lt_or_ge x 0 with hx | hx
  · have hemp : Y ⁻¹' Iic x = ∅ :=
      eq_empty_of_forall_notMem fun ω hω ↦ hx.not_ge ((NNReal.coe_nonneg _).trans hω)
    rw [hemp, measureReal_empty, regularizedGamma_eq_zero_of_nonpos_right _
      (mul_nonpos_of_nonneg_of_nonpos α.coe_nonneg hx.le)]
  · let t : ℝ≥0 := ⟨x, hx⟩
    have hae : (Y ⁻¹' Iic x : Set Ω) =ᵐ[P] {ω | hittingAfter M (Ici (k + 1)) 0 ω ≤ t} := by
      filter_upwards [h.hittingAfter_Ici_ae_ne_top hα k] with ω hfin
      change ((hittingAfter M (Ici (k + 1)) 0 ω).untopA : ℝ) ≤ (t : ℝ) ↔
        hittingAfter M (Ici (k + 1)) 0 ω ≤ t
      exact NNReal.coe_le_coe.trans (WithTop.untopA_le_iff hfin)
    rw [measureReal_congr hae, h.measureReal_hittingAfter_Ici_le hrc k t]
    rfl

/-- **Exponential law of the first arrival time.** For `0 < α`, the first arrival time
`((hittingAfter M (Set.Ici 1) 0 ω).untopA : ℝ)` has law `expMeasure α`. -/
theorem hasLaw_untopA_hittingAfter_Ici_one_expMeasure
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) (hα : 0 < α) :
    HasLaw (fun ω ↦ ((hittingAfter M (Ici 1) 0 ω).untopA : ℝ)) (expMeasure α) P := by
  simpa [expMeasure] using h.hasLaw_untopA_hittingAfter_Ici_gammaMeasure hrc hα 0

end TauCeti.Probability.IsFilteredPoissonProcess
