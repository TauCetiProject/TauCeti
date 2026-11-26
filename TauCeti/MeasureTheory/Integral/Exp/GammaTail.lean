/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Gamma kernel mass outside an interval

Exponential tilts bound the two tails of `u ^ n * exp (-a * u) / n!`. For a fixed window ratio
`λ > 1` and a fixed loss of rate `A`, one can choose a rate `σ > A` and a degree `n ≥ U` so that
the mass at rate `σ - A` outside `[U, λ * U]` is bounded by `C / σ ^ n`, with `C` independent
of the window. This compensates for the loss of rate when bounding the part of a Laplace moment
off the window for an input of exponential growth.

The interval bound and the scale-window estimate at `A = 2` are stated in Levent Alpöge's
[formalization of the Riemann hypothesis for Dirichlet L-functions](https://github.com/leanprover-community/riemann-hypothesis)
(`Deduction.landau_tails_chernoff` and `Deduction.landau_tails`, `LandauTheorems/landauTails.lean`).
-/

public section

open Filter MeasureTheory Real Set

namespace TauCeti

/-- Exponential tilting bounds the mass of the normalized Gamma kernel outside any interval
`[U, V]`, by the full masses of the kernels at rates `a - l` and `a + l` with endpoint factors. -/
theorem integral_gammaKernel_sdiff_Icc_le (n : ℕ) {a l : ℝ} (hl : 0 ≤ l) (hla : l < a)
    (U V : ℝ) :
    ∫ u : ℝ in Ioi 0 \ Icc U V, u ^ n * exp (-(a * u)) / n.factorial ≤
      exp (-(l * V)) / (a - l) ^ (n + 1) + exp (l * U) / (a + l) ^ (n + 1) := by
  let S := Ioi (0 : ℝ) \ Icc U V
  have hS : MeasurableSet S := measurableSet_Ioi.diff measurableSet_Icc
  have hsub : S ⊆ Ioi 0 := sdiff_subset
  have ha : 0 < a := hl.trans_lt hla
  have hm : 0 < a - l := sub_pos.mpr hla
  have hp : 0 < a + l := add_pos_of_pos_of_nonneg ha hl
  let f (r u : ℝ) := u ^ n * exp (-(r * u)) / n.factorial
  have hint (r : ℝ) (hr : 0 < r) : IntegrableOn (f r) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_mul_Ioi n hr).div_const _
  have hnonneg (r : ℝ) {u : ℝ} (hu : u ∈ Ioi (0 : ℝ)) : 0 ≤ f r u := by
    have hu' : 0 < u := hu
    dsimp [f]
    positivity
  let g (u : ℝ) := exp (-(l * V)) * f (a - l) u + exp (l * U) * f (a + l) u
  have hg : IntegrableOn g (Ioi 0) := ((hint _ hm).const_mul _).add ((hint _ hp).const_mul _)
  have hmass (r : ℝ) (hr : 0 < r) : (∫ u in Ioi 0, f r u) = (r ^ (n + 1))⁻¹ := by
    simp only [f, integral_div, integral_pow_mul_exp_neg_mul_Ioi n hr]
    field_simp
  have htilt {u r x : ℝ} (hu : 0 ≤ u) (hx : -(a * u) ≤ x + -(r * u)) :
      f a u ≤ exp x * f r u := by
    have he := exp_le_exp.mpr hx
    rw [exp_add] at he
    dsimp [f]
    rw [← mul_div_assoc, mul_left_comm (exp x)]
    gcongr
  calc
    ∫ u in S, f a u ≤ ∫ u in S, g u := by
      refine setIntegral_mono_on ((hint _ ha).mono_set hsub) (hg.mono_set hsub) hS ?_
      intro u hu
      have hu0 : 0 < u := hu.1
      have hout : ¬ (U ≤ u ∧ u ≤ V) := hu.2
      rcases (not_and_or.mp hout).imp lt_of_not_ge lt_of_not_ge with hleft | hright
      · refine le_add_of_nonneg_of_le (mul_nonneg (exp_pos _).le (hnonneg _ hu.1)) (htilt hu0.le ?_)
        linarith [mul_le_mul_of_nonneg_left hleft.le hl]
      · refine le_add_of_le_of_nonneg (htilt hu0.le ?_) (mul_nonneg (exp_pos _).le (hnonneg _ hu.1))
        linarith [mul_le_mul_of_nonneg_left hright.le hl]
    _ ≤ ∫ u in Ioi 0, g u :=
      setIntegral_mono_set hg (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        dsimp [g]
        positivity [hnonneg (a - l) hu, hnonneg (a + l) hu]) (Eventually.of_forall hsub)
    _ = _ := by
      dsimp [g]
      rw [integral_add ((hint _ hm).const_mul _) ((hint _ hp).const_mul _)]
      simp [integral_const_mul, hmass _ hm, hmass _ hp, div_eq_mul_inv]

/-- Rates for the two tilts: a degree near `m U` cancels the factors at both endpoints. -/
private theorem exists_gammaKernel_window_tilts (A : ℝ) {L : ℝ} (hL : 1 < L) :
    ∃ σ > max 1 A, ∃ m ≥ 1, ∃ l ≥ 0, l < σ - A ∧
      σ / (σ - A + l) ≤ exp (-(l / m)) ∧
      σ / (σ - A - l) ≤ exp (l * L / m) := by
  let t := (L + 1) / 2
  have ht : 1 < t := by dsimp [t]; linarith
  obtain ⟨l, hl⟩ := exists_gt (max 0 (t * A / (t - 1)))
  have hl0 : 0 < l := (le_max_left _ _).trans_lt hl
  -- Taking `t` midway between `1` and `L` gives both tails the same linear margin in `σ`.
  let d := (t - 1) * l - t * A
  have hd : 0 < d := sub_pos.mpr <| by
    have h := (div_lt_iff₀ (sub_pos.mpr ht)).mp ((le_max_right _ _).trans_lt hl)
    simpa only [mul_comm l] using h
  obtain ⟨σ, hσ⟩ := exists_gt
    (max (max 1 (A + l)) (max (l * (l - A) / d) (l * L * (l + A) / d)))
  rw [max_lt_iff, max_lt_iff, max_lt_iff] at hσ
  obtain ⟨⟨hσ1, hσA⟩, h₁, h₂⟩ := hσ
  let m := t * σ
  have hm : 1 ≤ m := by dsimp [m]; nlinarith [mul_pos (sub_pos.mpr ht) (sub_pos.mpr hσ1)]
  have hm0 := zero_lt_one.trans_le hm
  have hlσ : l < σ - A := by linarith
  have hleft : l * (σ - A + l) ≤ (l - A) * m := by
    have h := (div_lt_iff₀ hd).mp h₁
    dsimp [d] at h
    dsimp [m]
    linarith only [h]
  have hright : (l + A) * m ≤ l * L * (σ - A - l) := by
    have h := (div_lt_iff₀ hd).mp h₂
    have htL : L - t = t - 1 := by dsimp [t]; ring
    dsimp [d] at h
    dsimp [m]
    linarith only [h, congrArg (fun x ↦ x * l * σ) htL]
  refine ⟨σ, max_lt hσ1 (by linarith), m, hm, l, hl0.le, hlσ, ?_, ?_⟩
  · have hb : 0 < σ - A + l := by linarith
    calc
      σ / (σ - A + l) = 1 - (l - A) / (σ - A + l) := by field_simp; ring
      _ ≤ 1 + -(l / m) := by
        have h := (div_le_div_iff₀ hm0 hb).mpr hleft
        linarith
      _ ≤ exp (-(l / m)) := by simpa [add_comm] using add_one_le_exp (-(l / m))
  · have hc : 0 < σ - A - l := sub_pos.mpr hlσ
    calc
      σ / (σ - A - l) = 1 + (l + A) / (σ - A - l) := by field_simp; ring
      _ ≤ 1 + l * L / m := add_le_add_right ((div_le_div_iff₀ hc hm0).mpr hright) 1
      _ ≤ exp (l * L / m) := by simpa [add_comm] using add_one_le_exp (l * L / m)

/-- At fixed ratio `L > 1`, the Gamma kernel of a suitable degree `n ≥ U` has mass at most
`C / σ ^ n` outside `[U, L * U]` at rate `σ - A`. The rate `σ` and the constant `C` depend on
`A` and `L`, not on the window. -/
theorem exists_integral_gammaKernel_sdiff_Icc_mul_le (A : ℝ) {L : ℝ} (hL : 1 < L) :
    ∃ σ > max 1 A, ∃ C > 0, ∀ U : ℝ, ∃ n : ℕ, U ≤ n ∧
      ∫ u : ℝ in Ioi 0 \ Icc U (L * U), u ^ n * exp (-((σ - A) * u)) / n.factorial ≤
        C / σ ^ n := by
  obtain ⟨σ, hσ, m, hm, l, hl, hla, hleft, hright⟩ := exists_gammaKernel_window_tilts A hL
  let a := σ - A
  have hσ0 : 0 < σ := zero_lt_one.trans (lt_of_le_of_lt (le_max_left ..) hσ)
  have ha : 0 < a := hl.trans_lt hla
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hb : 0 < a + l := add_pos_of_pos_of_nonneg ha hl
  have hc : 0 < a - l := sub_pos.mpr hla
  let C := exp (l * L / m) / (a - l) + 1 / (a + l)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨σ, hσ, max C (1 / a), lt_of_lt_of_le hC (le_max_left ..), fun U ↦ ?_⟩
  rcases le_or_gt 0 U with hU | hU
  · let n := ⌈m * U⌉₊
    have hn : m * U ≤ (n : ℝ) := Nat.le_ceil _
    have hn' : (n : ℝ) ≤ m * U + 1 := (Nat.ceil_lt_add_one (mul_nonneg hm0.le hU)).le
    refine ⟨n, (le_mul_of_one_le_left hU hm).trans hn, ?_⟩
    refine (integral_gammaKernel_sdiff_Icc_le n hl hla U (L * U)).trans ?_
    have tilt {r t X B : ℝ} (hr : 0 < r) (h : σ / r ≤ exp t) (hB : X + t * n ≤ B) :
        exp X / r ^ (n + 1) ≤ (exp B / r) / σ ^ n := by
      calc
        exp X / r ^ (n + 1) = (exp X * (σ / r) ^ n / r) / σ ^ n := by
          rw [div_pow, pow_succ]; field_simp
        _ ≤ (exp X * (exp t) ^ n / r) / σ ^ n := by gcongr
        _ ≤ (exp B / r) / σ ^ n := by
          rw [← exp_natCast_mul, ← exp_add]
          gcongr
          simpa only [mul_comm t] using hB
    -- Rounding up improves the left-tail exponent and costs at most one step on the right.
    have hlo : l * U + -(l / m) * n ≤ 0 := by
      have hh := mul_le_mul_of_nonneg_left hn (div_nonneg hl hm0.le)
      rw [← mul_assoc, div_mul_cancel₀ _ hm0.ne'] at hh
      linarith only [hh]
    have hhi : -(l * (L * U)) + (l * L / m) * n ≤ l * L / m := by
      have hh := mul_le_mul_of_nonneg_left hn' (div_nonneg (mul_nonneg hl hL0.le) hm0.le)
      rw [mul_add, ← mul_assoc, div_mul_cancel₀ _ hm0.ne', mul_one] at hh
      linarith only [hh]
    calc
      _ ≤ (exp (l * L / m) / (a - l)) / σ ^ n + (exp 0 / (a + l)) / σ ^ n :=
        add_le_add (tilt hc hright hhi) (tilt hb hleft hlo)
      _ = C / σ ^ n := by rw [exp_zero, ← add_div]
      _ ≤ max C (1 / a) / σ ^ n := by gcongr; exact le_max_left ..
  · refine ⟨0, by simpa using hU.le, ?_⟩
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, div_one]
    have hint := integrableOn_pow_mul_exp_neg_mul_Ioi 0 ha
    calc
      _ ≤ ∫ u : ℝ in Ioi 0, exp (-(a * u)) :=
        setIntegral_mono_set (by simpa using hint)
          (ae_of_all _ fun _ ↦ (exp_pos _).le) (Eventually.of_forall sdiff_subset)
      _ = 1 / a := by simpa using integral_pow_mul_exp_neg_mul_Ioi 0 ha
      _ ≤ _ := le_max_right ..

end TauCeti
