/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# Identically distributed random variables

If every member of a countable family of random variables is identically distributed with a
random variable that is almost surely equal to a constant, then almost surely every member of the
family equals that constant, on one event for all indices at once.

Two identically distributed variables, possibly defined on different spaces, have equal
integrals after each is kept only where its norm is at most a common real level `R`. In
particular, truncated variables recentred by their integrals use the same centring constant
whenever the original variables have the same law.

An integrable common law also gives an eventual almost-sure bound on real variables by
their indices, and controls the prefix maxima of variables with finite absolute moments.

## Main results

* `TauCeti.Probability.ae_forall_eq_of_identDistrib` — a countable family of random variables,
  each identically distributed with an almost surely constant random variable, is almost surely
  equal to that constant at every index simultaneously.
* `ProbabilityTheory.IdentDistrib.integral_indicator_setOf_norm_le_eq` — identically distributed
  variables have equal integrals after cutting off the values of norm greater than `R`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- **Random variables identically distributed with an almost surely constant one are almost surely
constant simultaneously.** If each `T i` of a countable family has the same law as `X`, and `X`
equals `c` almost surely, then almost surely all of the `T i` equal `c`. The family and `X` may live
on different measure spaces. -/
theorem ae_forall_eq_of_identDistrib {ι : Sort*} [Countable ι] {Ω Ω' Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {P : Measure Ω} {Q : Measure Ω'} {T : ι → Ω → Z} {X : Ω' → Z}
    (hid : ∀ i, IdentDistrib (T i) X P Q) {c : Z} (h : X =ᵐ[Q] fun _ ↦ c) :
    ∀ᵐ ω ∂P, ∀ i, T i ω = c :=
  ae_all_iff.2 fun i ↦ (hid i).symm.ae_mem_snd (measurableSet_singleton c) h

open Filter Set
open scoped ENNReal

/-- A sequence of real variables with a common integrable law is eventually bounded above
by the index almost surely. The variables may be dependent, and the reference law may be
represented on another measure space. -/
theorem ae_eventually_le_natCast_of_identDistrib {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {Z : ℕ → Ω → ℝ} {Y : Ω' → ℝ} (hid : ∀ i, IdentDistrib (Z i) Y P Q)
    (hint : Integrable Y Q) :
    ∀ᵐ ω ∂P, ∀ᶠ i in atTop, Z i ω ≤ (i : ℝ) := by
  have heq (i : ℕ) : P {ω | Z (i + 1) ω ∈ Ioi ((i + 1 : ℕ) : ℝ)} =
      Q {ω | Y ω ∈ Ioi ((i + 1 : ℕ) : ℝ)} :=
    (hid (i + 1)).measure_mem_eq measurableSet_Ioi
  have hfinite : (∑' i : ℕ, P {ω | Z (i + 1) ω ∈ Ioi ((i + 1 : ℕ) : ℝ)}) < ∞ := by
    simpa only [heq] using hint.tsum_measure_mem_Ioi_nat_succ_lt_top
  filter_upwards [ae_eventually_notMem hfinite.ne] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine eventually_atTop.2 ⟨N + 1, fun i hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  exact not_lt.1 (hN j (by omega))

section PrefixMaxima

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] {P : Measure Ω} {X : ℕ → Ω → E} {Y : Ω → E}

/-- If the prefix length is at most the `p`-th power of a divergent scale, its maximal
absolute entry divided by that scale tends to zero almost surely. The variables need only
have the same distribution and a finite `p`-th absolute moment. The tail-summability
and Borel–Cantelli argument follows Mathlib's `ProbabilityTheory.strong_law_aux5`. -/
theorem ae_eventually_forall_lt_norm_le_mul_of_identDistrib
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
  have htail (δ : ℝ) :
      ∀ᵐ ω ∂P, ∀ᶠ i in atTop, (‖X i ω‖ / δ) ^ p ≤ (i : ℝ) := by
    let f (x : E) := (‖x‖ / δ) ^ p
    have hf : Measurable f := by
      unfold f
      fun_prop
    have hint : Integrable (fun ω ↦ f (Y ω)) P := by
      simpa only [f, div_eq_mul_inv, mul_pow, inv_pow] using
        (hY.integrable_norm_pow hp).mul_const (δ ^ p)⁻¹
    exact ae_eventually_le_natCast_of_identDistrib (fun i ↦ (hX i).comp hf) hint
  filter_upwards [ae_all_iff.2 (fun k : ℕ ↦ htail (1 / (k + 1)))] with ω hω
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

end PrefixMaxima

end TauCeti.Probability

namespace ProbabilityTheory.IdentDistrib

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure α} {ν : Measure β} {f : α → E} {g : β → E}

/-- Identically distributed variables have equal integrals after cutting off the values of
norm greater than `R`. -/
theorem integral_indicator_setOf_norm_le_eq (h : IdentDistrib f g μ ν) (R : ℝ) :
    ∫ x, {x | ‖f x‖ ≤ R}.indicator f x ∂μ = ∫ x, {x | ‖g x‖ ≤ R}.indicator g x ∂ν := by
  simpa only [Function.comp_def, Set.indicator_apply, Set.mem_ofPred_eq, id_eq] using
    (h.comp (measurable_id.indicator_setOf_norm_le R)).integral_eq

end ProbabilityTheory.IdentDistrib
