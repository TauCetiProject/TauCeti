/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.StrongLaw

/-!
# Almost-sure bounds for maxima of identically distributed variables

A finite absolute moment controls maxima over prefixes whose lengths grow at most as the
corresponding power of the comparison scale. Dependence within the sequence is allowed.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] {P : Measure Ω} {X : ℕ → Ω → E} {Y : Ω → E}

/-- If the prefix length is at most the `p`-th power of a divergent scale, its maximal
absolute entry divided by that scale tends to zero almost surely. The variables need only
have the same distribution and a finite `p)-th absolute moment. -/
theorem ae_eventually_forall_lt_norm_le_mul_of_identDistrib [IsProbabilityMeasure P]
    (hX : ∀ i, IdentDistrib (X i) Y P P) {p : ℕ} (hY : MemLp Y p P)
    {m : ℕ → ℕ} {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : ∀ᶠ n in atTop, (m n : ℝ) ≤ s n ^ p) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ i < m n, ‖X i ω‖ ≤ ε * s n := by
  rcases eq_or_ne p 0 with rfl | hp
  · refine .of_forall fun ω ε hε ↦ ?_
    filter_upwards [hm, (tendsto_atTop.1 hs) (‖X 0 ω‖ / ε)] with n hn hs' i hi
    have hm' : m n ≤ 1 := by exact_mod_cast (by simpa only [pow_zero] using hn : (m n : ℝ) ≤ 1)
    have hi' : i = 0 := by omega
    rw [hi', mul_comm]
    exact (div_le_iff₀ hε).1 hs'
  have htail (δ : ℝ) (hδ : 0 < δ) :
      ∀ᵐ ω ∂P, ∀ᶠ i in atTop, (‖X i ω‖ / δ) ^ p ≤ (i : ℝ) := by
    let f (x : E) := (‖x‖ / δ) ^ p
    have hf : Measurable f := by
      unfold f
      fun_prop
    have hint : Integrable (fun ω ↦ f (Y ω)) P := by
      simpa only [f, div_eq_mul_inv, mul_pow, inv_pow] using
        (hY.integrable_norm_pow hp).mul_const (δ ^ p)⁻¹
    have heq (i : ℕ) : P {ω | f (X i ω) ∈ Ioi (i : ℝ)} =
        P {ω | f (Y ω) ∈ Ioi (i : ℝ)} :=
      ((hX i).comp hf).measure_mem_eq measurableSet_Ioi
    have hfinite : (∑' i : ℕ, P {ω | f (X i ω) ∈ Ioi (i : ℝ)}) < ∞ := by
      simp_rw [heq]
      let : MeasureSpace Ω := ⟨P⟩
      have hnonneg : 0 ≤ fun ω ↦ f (Y ω) := fun ω ↦ by unfold f; positivity
      exact tsum_prob_mem_Ioi_lt_top hint hnonneg
    simpa only [f, mem_ofPred_eq, mem_Ioi, not_lt] using ae_eventually_notMem hfinite.ne
  filter_upwards [ae_all_iff.2 (fun k : ℕ ↦ htail (1 / (k + 1)) (by positivity))] with ω hω
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω k)
  let δ : ℝ := 1 / (k + 1)
  have hδ : 0 < δ := by positivity
  have hsmall (i : Fin N) : ∀ᶠ n in atTop, ‖X i ω‖ / δ ≤ s n :=
    (tendsto_atTop.1 hs) _
  filter_upwards [hm, (tendsto_atTop.1 hs) 0, eventually_all.2 hsmall] with n hn hs₀ hsmall' i hi
  have hle : ‖X i ω‖ / δ ≤ s n := by
    by_cases hiN : i < N
    · exact hsmall' ⟨i, hiN⟩
    · by_contra! h
      exact (not_lt_of_ge ((hN i (by omega)).trans
        ((Nat.cast_le.2 hi.le).trans hn))) (pow_lt_pow_left₀ h hs₀ hp)
  exact ((div_le_iff₀ hδ).1 hle).trans (by
    rw [mul_comm (s n) δ]
    exact mul_le_mul_of_nonneg_right hk.le hs₀)

end ProbabilityTheory
