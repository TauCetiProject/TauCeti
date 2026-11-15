/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.AttainedMinimum
public import TauCeti.Probability.Process.HittingTime.Countable
public import TauCeti.Probability.Process.HittingTime.Grid
public import TauCeti.Probability.Process.ExitExhaustion
public import Mathlib.Probability.Process.LocalProperty
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import TauCeti.Data.Set.Countable
import TauCeti.Probability.Process.HittingTime
import TauCeti.Probability.Process.Stopping

/-!
# Countable-range level localizers on raw filtrations

For an adapted process with almost-surely continuous paths, construct countable-range
stopping times which localize its centered norm. Each time lies between the first hits of
half its level and its full level, almost surely. Finite maxima make the times increasing;
they exhaust every finite horizon and bound all centered stopped paths simultaneously.
Neither completeness nor right continuity of the filtration is assumed, and the initial
value needs no moment assumption.

The continuous-path level hits are comparison times only: they need not be stopping times
on a raw filtration. The actual stopping times are attained minima of dyadic grid hits,
with infinity on exceptional paths where no minimum exists. Countable-range optional
sampling can therefore be applied without completing the filtration.

## Main results

* `MeasureTheory.StronglyAdapted.exists_isLocalizingSequence_countable_range_level`
  constructs a native localizing sequence with countable ranges and centered stopped-path bounds.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.StronglyAdapted

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [SFinite P]
  {ℱ : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ}

/-- There is a countable-range stopping time on the raw filtration which, almost surely,
lies between the continuous-path hits of half a positive level and that level. Path continuity
is only almost sure; no stopping-time property of the comparison hits is asserted. -/
theorem exists_countable_range_isStoppingTime_between_level_hits
    (hX : StronglyAdapted ℱ X) (hc : ∀ᵐ ω ∂P, Continuous (X · ω))
    {C : ℝ} (hC : 0 < C) :
    ∃ ρ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ ρ ∧ (range ρ).Countable ∧
      ∀ᵐ ω ∂P, hittingAfter X (Ici (C / 2)) 0 ω ≤ ρ ω ∧
        ρ ω ≤ hittingAfter X (Ici C) 0 ω := by
  let θ : ℕ → ℝ := fun j ↦ C * (1 - (1 / 2 : ℝ) ^ (j + 1))
  have hθlt (j : ℕ) : θ j < C := by
    dsimp [θ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (j + 1)]
  have hθhalf (j : ℕ) : C / 2 ≤ θ j := by
    have hp : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
      simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.succ_le_succ (Nat.zero_le j))
    dsimp [θ]
    nlinarith
  have hθlim : Tendsto θ atTop (𝓝 C) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp
      (tendsto_add_atTop_nat 1)
    simpa [θ] using (tendsto_const_nhds (x := C)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)
  obtain ⟨σ, hσ, hσeq⟩ := TauCeti.Probability.exists_measurable_eq_hittingAfter_Ici
    (fun t ↦ (hX t).measurable.mono (ℱ.le t) le_rfl) C
  have hlevel (j : ℕ) : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, σ ω = t → θ j < X t ω := by
    filter_upwards [hc] with ω hω t ht
    have hhit := (hσeq ω hω).symm.trans ht
    obtain ⟨u, hu, _, huc⟩ := isClosed_Ici.exists_hittingAfter_eq hω
      (hhit.trans_ne WithTop.coe_ne_top)
    have hut : u = t := WithTop.coe_injective (hu.symm.trans hhit)
    exact (hθlt j).trans_le (hut ▸ huc)
  have hcFinite : ∀ᵐ ω ∂P.toFinite, Continuous (X · ω) := by
    rwa [ae_toFinite]
  obtain ⟨q, _, hq⟩ := TauCeti.exists_gridLevelHit_summable_misses
    (fun t ↦ (hX t).measurable.mono (ℱ.le t) le_rfl) hcFinite hσ
    (fun j ↦ by simpa only [ae_toFinite] using hlevel j)
  obtain ⟨ρ, hρ, hcount, heq⟩ := TauCeti.exists_countable_range_isStoppingTime_ae_eq_iInf
    (fun j ↦ TauCeti.isStoppingTime_gridLevelHit hX (θ j) (q j))
    (fun j ↦ TauCeti.countable_range_gridLevelHit X (θ j) (q j))
    (hcFinite.mono fun ω hω ↦ (hσeq ω hω).symm ▸
      hω.tendsto_hittingAfter_Ici (fun j ↦ (hθlt j).le) hθlim)
    (Eventually.of_forall fun ω j ↦ TauCeti.hittingAfter_Ici_le_gridLevelHit) hq.ne
  rw [ae_toFinite] at heq
  refine ⟨ρ, hρ, hcount, ?_⟩
  filter_upwards [hc, heq] with ω hω hρω
  refine ⟨?_, (hρω.2.trans_eq (hσeq ω hω))⟩
  rw [hρω.1]
  exact le_iInf fun j ↦ (hittingAfter_apply_anti X 0 ω
    (Ici_subset_Ici.mpr (hθhalf j))).trans TauCeti.hittingAfter_Ici_le_gridLevelHit

private theorem exists_monotone_level_stopping_times
    (hX : StronglyAdapted ℱ X) (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    ∃ ρ : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsStoppingTime ℱ (ρ n)) ∧ (∀ n, (range (ρ n)).Countable) ∧
      (∀ ω, Monotone (ρ · ω)) ∧ ∀ᵐ ω ∂P, ∀ n : ℕ,
        hittingAfter X (Ici (((n : ℝ) + 1) / 2)) 0 ω ≤ ρ n ω ∧
          ρ n ω ≤ hittingAfter X (Ici ((n : ℝ) + 1)) 0 ω := by
  classical
  have hex (n : ℕ) := hX.exists_countable_range_isStoppingTime_between_level_hits hc
    (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  choose η hη hcount hbounds using hex
  let ρ (n : ℕ) (ω : Ω) := (Finset.range (n + 1)).sup (fun j ↦ η j ω)
  have hmono (ω : Ω) : Monotone (ρ · ω) := fun i j hij ↦
    Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hij 1))
  refine ⟨ρ, fun n ↦ (Finset.range (n + 1)).isStoppingTime_sup (fun j _ ↦ hη j),
    fun n ↦ (Finset.range (n + 1)).countable_range_sup (fun j _ ↦ hcount j), hmono, ?_⟩
  filter_upwards [ae_all_iff.mpr hbounds] with ω hω n
  refine ⟨(hω n).1.trans (Finset.le_sup (f := fun j ↦ η j ω)
    (Finset.mem_range.mpr (Nat.lt_succ_self n))), ?_⟩
  apply Finset.sup_le
  intro j hj
  have hjn : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) 1
  exact (hω j).2.trans (hittingAfter_apply_anti X 0 ω (Ici_subset_Ici.mpr hjn))

end MeasureTheory.StronglyAdapted

namespace MeasureTheory.StronglyAdapted

variable {Ω E : Type*} [NormedAddCommGroup E] {m : MeasurableSpace Ω}
  {P : Measure Ω} [SFinite P] {ℱ : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → E}

/-- Every strongly adapted process with almost-surely continuous paths has countable-range
level localizers on its original filtration. The times are pointwise increasing; on one
common full-measure event they lie between the half-level and full-level centered-norm hits
and bound the entire centered stopped path. No integrability of the initial value is needed. -/
theorem exists_isLocalizingSequence_countable_range_level (hX : StronglyAdapted ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    ∃ ρ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence ℱ ρ P ∧
      (∀ n, (range (ρ n)).Countable) ∧ (∀ ω, Monotone (ρ · ω)) ∧
      ∀ᵐ ω ∂P, ∀ n : ℕ,
        (hittingAfter (fun t ω ↦ ‖X t ω - X 0 ω‖) (Ici (((n : ℝ) + 1) / 2)) 0 ω ≤
          ρ n ω ∧ ρ n ω ≤
            hittingAfter (fun t ω ↦ ‖X t ω - X 0 ω‖) (Ici ((n : ℝ) + 1)) 0 ω) ∧
        ∀ t, ‖MeasureTheory.stoppedProcess X (ρ n) t ω - X 0 ω‖ ≤ (n : ℝ) + 1 := by
  let Y (t : ℝ≥0) (ω : Ω) := ‖X t ω - X 0 ω‖
  have hY : StronglyAdapted ℱ Y := fun t ↦
    ((hX t).sub ((hX 0).mono (ℱ.mono bot_le))).norm
  have hcY : ∀ᵐ ω ∂P, Continuous (Y · ω) :=
    hc.mono fun ω hω ↦ (hω.sub continuous_const).norm
  obtain ⟨ρ, hρ, hcount, hmono, hb⟩ := exists_monotone_level_stopping_times hY hcY
  have hlim : ∀ᵐ ω ∂P, Tendsto (ρ · ω) atTop (𝓝 ⊤) := by
    filter_upwards [hcY, hb] with ω hω hbound
    have hex (t : ℝ≥0) : ∃ n : ℕ, Y t ω < ((n : ℝ) + 1) / 2 := by
      obtain ⟨n, hn⟩ := exists_nat_gt (2 * Y t ω)
      exact ⟨n, by linarith⟩
    have hhit := hω.tendsto_hittingAfter_compl
      (fun n : ℕ ↦ isOpen_Iio (a := ((n : ℝ) + 1) / 2))
      (fun i j hij ↦ Iio_subset_Iio (by gcongr)) hex
    apply (WithTop.tendsto_nhds_top_iff _).mpr
    intro t
    filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp hhit t] with n hn
    exact hn.trans_le (by simpa only [compl_Iio] using (hbound n).1)
  refine ⟨ρ, ⟨⟨hρ, hlim⟩, Eventually.of_forall hmono⟩, hcount, hmono, ?_⟩
  filter_upwards [hc, hb] with ω hω hbound n
  refine ⟨hbound n, fun t ↦ ?_⟩
  have hpath : Continuous (Y · ω) := (hω.sub continuous_const).norm
  have hle (s : ℝ≥0) (hs : (s : WithTop ℝ≥0) ≤ ρ n ω) : Y s ω ≤ (n : ℝ) + 1 :=
    hpath.le_of_le_hittingAfter_Ici (X := Y) (a := 0) (t := s) bot_le
      (by simp only [Y, sub_self, norm_zero]; positivity) (hs.trans (hbound n).2)
  exact stoppedProcess_mem (s := {x | ‖x - X 0 ω‖ ≤ (n : ℝ) + 1}) hle t

end MeasureTheory.StronglyAdapted
