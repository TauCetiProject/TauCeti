/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Zero.Truncation
public import TauCeti.Probability.Quantile.Discrete
import TauCeti.Probability.Distributions.Dirac

/-!
# Endpoint limits of zero-truncated count quantiles

Removing zero from a natural-valued probability law moves the lower quantile endpoint to one
when the original law gives positive mass to one. The upper endpoint is unchanged: the
probability rescaling `u ↦ p₀ + u * (1 - p₀)` approaches one from below whenever `p₀ < 1`.
The upper-limit theorem allows finite and infinite endpoints through `EReal`.

These results apply in particular to zero-truncated Poisson and negative-binomial laws.
They concern limits through interior probability levels, not values of totalized quantiles
at zero or one. If truncation removes all mass, the result is a zero measure rather than a
probability law.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace MeasureTheory.Measure

variable (ν : Measure ℕ) [IsProbabilityMeasure ν]

/-- If count one has positive mass, zero-truncated quantiles tend to one as the level tends
to zero from above. No assumption on the other positive counts is needed. -/
theorem tendsto_quantile_map_natCast_cond_compl_zero_nhdsGT_zero (h₁ : ν {1} ≠ 0) :
    Tendsto (fun u ↦ (((ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 1) := by
  have h₀ : ν {0} ≠ 1 := by
    intro h
    have hcompl : ν ({0} : Set ℕ)ᶜ = 0 := by
      rw [prob_compl_eq_one_sub (measurableSet_singleton 0), h, tsub_self]
    have hsub : ({1} : Set ℕ) ⊆ {0}ᶜ := by simp
    have hle : ν {1} ≤ ν ({0} : Set ℕ)ᶜ := measure_mono hsub
    exact h₁ (le_zero_iff.1 (hle.trans_eq hcompl))
  have := isProbabilityMeasure_cond_compl_singleton h₀
  have hmass : (ν[|{0}ᶜ]) {1} ≠ 0 := by
    rw [cond_compl_singleton_apply_singleton one_ne_zero]
    exact mul_ne_zero
      (ENNReal.inv_ne_zero.2 (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)) h₁
  have hpos : 0 < (ν[|{0}ᶜ]).real (Iic 1) :=
    (ENNReal.toReal_pos hmass (measure_ne_top _ _)).trans_le
      (measureReal_mono (singleton_subset_iff.2 (mem_Iic.2 le_rfl)))
  have hzero : (ν[|{0}ᶜ]).real (Iic 0) = 0 := by
    rw [← Nat.bot_eq_zero, Iic_bot]
    simp [measureReal_def]
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT hpos, Ioo_mem_nhdsGT zero_lt_one] with u hu hu'
  have hq : ((ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u = (1 : ℕ) := by
    rw [quantile_map_natCast_eq_succ_iff _ hu' 0]
    exact ⟨by simpa [hzero] using hu.1, hu.2.le⟩
  exact_mod_cast hq.symm

/-- Zero truncation preserves any finite or infinite upper quantile endpoint. When it removes
all mass, both the original Dirac law and the resulting zero measure have quantile limit zero. -/
theorem tendsto_quantile_map_natCast_cond_compl_zero_nhdsLT_one
    {c : EReal}
    (hc : Tendsto (fun u ↦ ((ν.map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 c)) :
    Tendsto (fun u ↦ (((ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 c) := by
  by_cases h₀ : ν {0} = 1
  · have hae : ∀ᵐ n ∂ν, n = 0 := by
      rw [ae_iff]
      have hcompl : ν ({0} : Set ℕ)ᶜ = 0 := by
        rw [prob_compl_eq_one_sub (measurableSet_singleton 0), h₀, tsub_self]
      exact hcompl
    have hmap : ν.map (Nat.cast : ℕ → ℝ) = Measure.dirac 0 := by
      calc
        _ = ν.map (fun _ : ℕ ↦ (0 : ℝ)) :=
          Measure.map_congr (hae.mono fun n hn ↦ by simp [hn])
        _ = _ := by simp
    have hlimzero : Tendsto (fun u ↦ ((ν.map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
        (𝓝[<] 1) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
      simp [hmap, Measure.quantile_dirac 0 hu.1 hu.2.le]
    rw [tendsto_nhds_unique hc hlimzero, cond_compl_singleton_eq_zero_iff.2 h₀]
    simp
  have hlt : ν.real {0} < 1 :=
    lt_of_le_of_ne measureReal_le_one fun h ↦ h₀ (by
      rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h)
  have hcontinuous : Continuous (fun u : ℝ ↦ ν.real {0} + u * (1 - ν.real {0})) := by
    fun_prop
  have hlim : Tendsto (fun u : ℝ ↦ ν.real {0} + u * (1 - ν.real {0}))
      (𝓝[<] 1) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa using (hcontinuous.tendsto 1).mono_left
        (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with u hu
      have hprod := mul_pos (sub_pos.2 (hu : u < 1)) (sub_pos.2 hlt)
      simp only [mem_Iio]
      nlinarith
  apply (hc.comp hlim).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal))
    (quantile_map_natCast_cond_compl_zero ν h₀ hu).symm

end MeasureTheory.Measure
