/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Integrating complementary power bounds

A singular integrand can have two useful estimates: a power integrable at zero, and a power
integrable at infinity. Splitting at an arbitrary positive scale gives a bound independent of
the upper integration endpoint. This is useful for Hölder estimates of heat potentials, where
the scale is the square of the spatial separation.

The endpoint-singular form `TauCeti.norm_integral_le_of_ae_norm_le_rpow` reverses time and
specializes the scale to obtain a bound proportional to the spatial separation to the Hölder
exponent.
-/

public section

namespace TauCeti

open MeasureTheory Set Real

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrate two complementary power bounds by splitting at `d`. The first power is integrable
at zero and the second at infinity; the resulting bound is uniform in the endpoint `t ≥ 0`. -/
theorem norm_intervalIntegral_le_of_rpow_bounds {f : ℝ → F} {a b A B d t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 < d) (ht : 0 ≤ t)
    (hf : IntervalIntegrable f volume 0 t)
    (hnear : ∀ᵐ r ∂volume.restrict (Ioo 0 t), ‖f r‖ ≤ A * r ^ (a - 1))
    (hfar : ∀ᵐ r ∂volume.restrict (Ioo 0 t), ‖f r‖ ≤ B * r ^ (-b - 1)) :
    ‖∫ r in 0..t, f r‖ ≤ A / a * d ^ a + B / b * d ^ (-b) := by
  have hnear' : ∀ᵐ r ∂volume, r ∈ Ioc 0 t → ‖f r‖ ≤ A * r ^ (a - 1) := by
    rwa [restrict_Ioo_eq_restrict_Ioc, ae_restrict_iff' measurableSet_Ioc] at hnear
  have hfar' : ∀ᵐ r ∂volume, r ∈ Ioc 0 t → ‖f r‖ ≤ B * r ^ (-b - 1) := by
    rwa [restrict_Ioo_eq_restrict_Ioc, ae_restrict_iff' measurableSet_Ioc] at hfar
  have hsmall {s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
      ‖∫ r in 0..s, f r‖ ≤ A / a * s ^ a := by
    have hr : -1 < a - 1 := by linarith
    calc
      ‖∫ r in 0..s, f r‖ ≤ ∫ r in 0..s, A * r ^ (a - 1) :=
        intervalIntegral.norm_integral_le_of_norm_le hs
          (hnear'.mono fun r hr hrs => hr ⟨hrs.1, hrs.2.trans hst⟩)
          ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul A)
      _ = A / a * s ^ a := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr)]
        rw [sub_add_cancel, Real.zero_rpow ha.ne', sub_zero]
        ring
  by_cases htd : t ≤ d
  · exact (hsmall ht le_rfl).trans <| le_add_of_le_of_nonneg
      (mul_le_mul_of_nonneg_left (rpow_le_rpow ht htd ha.le) (div_nonneg hA ha.le))
      (by positivity)
  · have hdt : d ≤ t := (lt_of_not_ge htd).le
    have hp : ∀ r ∈ uIcc d t, r ≠ (0 : ℝ) := by
      intro r hr
      rw [uIcc_of_le hdt] at hr
      exact (hd.trans_le hr.1).ne'
    have htail : ‖∫ r in d..t, f r‖ ≤ B / b * d ^ (-b) := by
      calc
        ‖∫ r in d..t, f r‖ ≤ ∫ r in d..t, B * r ^ (-b - 1) :=
          intervalIntegral.norm_integral_le_of_norm_le hdt
            (hfar'.mono fun r hr hrs => hr ⟨hd.trans hrs.1, hrs.2⟩)
            (((continuousOn_id.rpow_const (fun r hr => Or.inl (hp r hr))).intervalIntegrable)
              |>.const_mul B)
        _ = B / b * (d ^ (-b) - t ^ (-b)) := by
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inr ⟨by linarith, fun h => hp 0 h rfl⟩)]
          simp only [sub_add_cancel]
          field_simp
          ring
        _ ≤ B / b * d ^ (-b) := by
          exact mul_le_mul_of_nonneg_left (sub_le_self _ (rpow_nonneg ht _))
            (div_nonneg hB hb.le)
    have hfd : IntervalIntegrable f volume 0 d := hf.mono_set (by
      rw [uIcc_of_le hd.le, uIcc_of_le ht]
      exact Icc_subset_Icc le_rfl hdt)
    have hft : IntervalIntegrable f volume d t := hf.mono_set (by
      rw [uIcc_of_le hdt, uIcc_of_le ht]
      exact Icc_subset_Icc hd.le le_rfl)
    rw [← intervalIntegral.integral_add_adjacent_intervals hfd hft]
    exact (norm_add_le _ _).trans (add_le_add (hsmall hd.le hdt) htail)

open scoped Interval in
/-- Splitting a singular integral at distance `δ²` from its singular endpoint. If the integrand
is `O(A (t - s)^((α - 2)/2))`, which is integrable, and also `O(B δ (t - s)^((α - 3)/2))`, which is
integrable away from `s = t`, then using the first bound on `t - δ² < s < t` and the second on
`0 < s < t - δ²` bounds the integral over `[0, t]` by `(2A/α + 2B/(1 - α)) δ^α`. This is the time
integration behind parabolic Hölder estimates at two points at distance `δ`. -/
theorem norm_integral_le_of_ae_norm_le_rpow {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : ℝ → F} {α δ t A B : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (ht : 0 < t)
    (hδ : 0 < δ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hΦ : IntervalIntegrable Φ volume 0 t)
    (hΦA : ∀ᵐ s, s ∈ Ioc 0 t → ‖Φ s‖ ≤ A * (t - s) ^ ((α - 2) / 2))
    (hΦB : ∀ᵐ s, s ∈ Ioc 0 t → ‖Φ s‖ ≤ B * (t - s) ^ ((α - 3) / 2) * δ) :
    ‖∫ s in 0..t, Φ s‖ ≤ (2 / α * A + 2 / (1 - α) * B) * δ ^ α := by
  -- Reverse time to put the singular endpoint at zero, then split at scale `δ²`.
  have hrev : ∀ᵐ r ∂volume.restrict (Ioo 0 t),
      ‖Φ (t - r)‖ ≤ A * r ^ (α / 2 - 1) ∧
        ‖Φ (t - r)‖ ≤ (B * δ) * r ^ (-((1 - α) / 2) - 1) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [((volume : Measure ℝ).measurePreserving_sub_left t).quasiMeasurePreserving.ae
      (hΦA.and hΦB)] with r hr hrI
    have hmem : t - r ∈ Ioc 0 t := ⟨by linarith [hrI.2], by linarith [hrI.1]⟩
    have hnear := hr.1 hmem
    have hfar := hr.2 hmem
    rw [sub_sub_cancel] at hnear hfar
    constructor
    · have hexp : (α - 2) / 2 = α / 2 - 1 := by ring
      simpa only [hexp] using hnear
    · have hexp : (α - 3) / 2 = -((1 - α) / 2) - 1 := by ring
      rw [hexp] at hfar
      exact hfar.trans_eq (by ring)
  have hi := norm_intervalIntegral_le_of_rpow_bounds (by linarith : 0 < α / 2)
    (by linarith : 0 < (1 - α) / 2) hA (mul_nonneg hB hδ.le)
    (sq_pos_of_pos hδ) ht.le (by simpa using (hΦ.comp_sub_left t).symm)
    (hrev.mono fun _ h => h.1) (hrev.mono fun _ h => h.2)
  have heq : (∫ r in 0..t, Φ (t - r)) = ∫ s in 0..t, Φ s := by
    rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  rw [heq] at hi
  have hsq : (δ ^ 2) ^ (α / 2) = δ ^ α := by
    rw [← rpow_natCast_mul hδ.le]
    congr 1
    push_cast
    ring
  have hpow : (δ ^ 2) ^ (-((1 - α) / 2)) * δ = δ ^ α := by
    rw [← rpow_natCast_mul hδ.le, ← rpow_add_one hδ.ne']
    congr 1
    push_cast
    ring
  refine hi.trans_eq ?_
  rw [hsq]
  calc
    _ = 2 / α * A * δ ^ α + 2 / (1 - α) * B *
        ((δ ^ 2) ^ (-((1 - α) / 2)) * δ) := by field_simp
    _ = (2 / α * A + 2 / (1 - α) * B) * δ ^ α := by rw [hpow]; ring

/-- Both integrals are of size `O(c h ^ β)` when `t' ≤ t - t'`, since then `t ≤ 2 (t - t')`. -/
theorem norm_intervalIntegral_sub_le_of_le_sub {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {g₁ g₂ : ℝ → V} {c β t t' : ℝ} (hc : 0 ≤ c) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (ht' : 0 ≤ t') (htt' : t' ≤ t) (hsmall : t' ≤ t - t')
    (h₁ : ‖∫ s in 0..t, g₁ s‖ ≤ c * (t - 0) ^ β) (h₂ : ‖∫ s in 0..t', g₂ s‖ ≤ c * (t' - 0) ^ β) :
    ‖(∫ s in 0..t, g₁ s) - ∫ s in 0..t', g₂ s‖ ≤ 3 * c * (t - t') ^ β := by
  have h₃ : t ^ β ≤ 2 * (t - t') ^ β :=
    rpow_le_two_mul_rpow_of_le_two_mul (ht'.trans htt') (by linarith) hβ₀ hβ₁
  have h₄ : t' ^ β ≤ (t - t') ^ β := rpow_le_rpow ht' hsmall hβ₀
  rw [sub_zero] at h₁ h₂
  calc ‖(∫ s in 0..t, g₁ s) - ∫ s in 0..t', g₂ s‖
      ≤ ‖∫ s in 0..t, g₁ s‖ + ‖∫ s in 0..t', g₂ s‖ := norm_sub_le _ _
    _ ≤ c * t ^ β + c * t' ^ β := add_le_add h₁ h₂
    _ ≤ c * (2 * (t - t') ^ β) + c * (t - t') ^ β := by gcongr
    _ = 3 * c * (t - t') ^ β := by ring

open scoped Interval in
/-- Splitting both integrals at `s₀ = 2 t' - t = t' - (t - t')`: the part below `s₀` is controlled
by the difference of the integrands, and the two parts above `s₀` are of size `O(c h ^ β)`. -/
theorem norm_intervalIntegral_sub_le_of_sub_lt {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {g₁ g₂ : ℝ → V} {c β t t' D : ℝ} (hc : 0 ≤ c) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hs₀ : 0 ≤ 2 * t' - t) (htt' : t' ≤ t) (hg₁ : IntervalIntegrable g₁ volume 0 t)
    (hg₂ : IntervalIntegrable g₂ volume 0 t')
    (hfar : ‖∫ s in 0..2 * t' - t, (g₁ s - g₂ s)‖ ≤ D)
    (h₁ : ‖∫ s in (2 * t' - t)..t, g₁ s‖ ≤ c * (t - (2 * t' - t)) ^ β)
    (h₂ : ‖∫ s in (2 * t' - t)..t', g₂ s‖ ≤ c * (t' - (2 * t' - t)) ^ β) :
    ‖(∫ s in 0..t, g₁ s) - ∫ s in 0..t', g₂ s‖ ≤ D + 3 * c * (t - t') ^ β := by
  have hmem {τ : ℝ} (hτ : 2 * t' - t ≤ τ) : 2 * t' - t ∈ [[0, τ]] := by
    rw [uIcc_of_le (hs₀.trans hτ)]
    exact ⟨hs₀, hτ⟩
  have hsplit {τ : ℝ} {g : ℝ → V} (hg : IntervalIntegrable g volume 0 τ) (hτ : 2 * t' - t ≤ τ) :
      ∫ s in 0..τ, g s = (∫ s in 0..2 * t' - t, g s) + ∫ s in (2 * t' - t)..τ, g s :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hg.mono_set (uIcc_subset_uIcc left_mem_uIcc (hmem hτ)))
      (hg.mono_set (uIcc_subset_uIcc (hmem hτ) right_mem_uIcc))).symm
  have hg₁' := hg₁.mono_set (uIcc_subset_uIcc left_mem_uIcc (hmem (by linarith)))
  have hg₂' := hg₂.mono_set (uIcc_subset_uIcc left_mem_uIcc (hmem (by linarith)))
  rw [hsplit hg₁ (by linarith), hsplit hg₂ (by linarith),
    show ∀ a b c d : V, a + b - (c + d) = (a - c) + b - d from fun a b c d => by abel,
    ← intervalIntegral.integral_sub hg₁' hg₂']
  have h₃ : (t - (2 * t' - t)) ^ β ≤ 2 * (t - t') ^ β :=
    rpow_le_two_mul_rpow_of_le_two_mul (by linarith) (by linarith) hβ₀ hβ₁
  rw [show t' - (2 * t' - t) = t - t' by ring] at h₂
  calc ‖(∫ s in 0..2 * t' - t, (g₁ s - g₂ s)) + (∫ s in (2 * t' - t)..t, g₁ s) -
        ∫ s in (2 * t' - t)..t', g₂ s‖
      ≤ ‖∫ s in 0..2 * t' - t, (g₁ s - g₂ s)‖ + ‖∫ s in (2 * t' - t)..t, g₁ s‖ +
          ‖∫ s in (2 * t' - t)..t', g₂ s‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ ≤ D + c * (2 * (t - t') ^ β) + c * (t - t') ^ β := by gcongr; exact h₁.trans (by gcongr)
    _ = D + 3 * c * (t - t') ^ β := by ring

end TauCeti
