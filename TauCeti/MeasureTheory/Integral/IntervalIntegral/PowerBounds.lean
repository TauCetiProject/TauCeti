/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrating complementary power bounds

A singular integrand can have two useful estimates: a power integrable at zero, and a power
integrable at infinity. Splitting at an arbitrary positive scale gives a bound independent of
the upper integration endpoint. This is useful for Hölder estimates of heat potentials, where
the scale is the square of the spatial separation.

The endpoint-singular form `TauCeti.norm_integral_le_of_ae_norm_le_rpow` reverses time and
specializes the scale to obtain a bound proportional to the spatial separation to the Hölder
exponent.

The one-sided estimates `TauCeti.intervalIntegral.intervalIntegrable_of_norm_le_mul_sub_rpow_right`
and `TauCeti.intervalIntegral.norm_integral_le_of_norm_le_mul_sub_rpow_right` treat `a ≤ b` and a
function with values in a normed group whose norm is bounded almost everywhere on `(a, b]` by
`K * (s - a) ^ u` with `-1 < u`. If the function is a.e. strongly measurable on `(a, b]`, it is
interval integrable; without any measurability assumption, the norm of its integral over `[a, b]`
is at most `K * ((b - a) ^ (u + 1) / (u + 1))`. Both use `TauCeti.intervalIntegrable_sub_const_rpow`
and `TauCeti.integral_sub_const_rpow`. The `_left` forms treat the singularity at `b`, with bound
`K * (b - s) ^ u`, using `TauCeti.intervalIntegrable_sub_rpow` and `TauCeti.integral_sub_rpow`.

`TauCeti.norm_intervalIntegral_sub_le_of_sub_le` compares two oriented interval integrals, with
respect to any measure on `ℝ`, that start at a common endpoint, by splitting both at a common
point. Each integrand must be interval integrable on its two pieces: from the starting endpoint to
the split point, and from the split point to its own final endpoint. No ordering of the endpoints
is assumed. The norm of the difference of the two integrals is then at most a bound for the
integral of the difference up to the split point plus bounds for the two tails.
-/

public section

namespace TauCeti

namespace intervalIntegral

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A function whose norm is bounded almost everywhere on `(a, b]` by `K * (s - a) ^ u` with
`-1 < u` is interval integrable on `[a, b]`, given that it is a.e. strongly measurable there. -/
theorem intervalIntegrable_of_norm_le_mul_sub_rpow_right {f : ℝ → E} {a b K u : ℝ}
    (hu : -1 < u) (hab : a ≤ b) (hmeas : AEStronglyMeasurable f (volume.restrict (Ioc a b)))
    (hbound : ∀ᵐ s ∂volume.restrict (Ioc a b), ‖f s‖ ≤ K * (s - a) ^ u) :
    IntervalIntegrable f volume a b := by
  rw [← uIoc_of_le hab] at hmeas hbound
  exact ((TauCeti.intervalIntegrable_sub_const_rpow hu a a b).const_mul K).mono_fun' hmeas hbound

/-- A function whose norm is bounded almost everywhere on `(a, b]` by `K * (s - a) ^ u` with
`-1 < u` has integral over `[a, b]` of norm at most `K * ((b - a) ^ (u + 1) / (u + 1))`. -/
theorem norm_integral_le_of_norm_le_mul_sub_rpow_right {f : ℝ → E} {a b K u : ℝ}
    (hu : -1 < u) (hab : a ≤ b)
    (hbound : ∀ᵐ s ∂volume.restrict (Ioc a b), ‖f s‖ ≤ K * (s - a) ^ u) :
    ‖∫ s in a..b, f s‖ ≤ K * ((b - a) ^ (u + 1) / (u + 1)) := by
  refine (intervalIntegral.norm_integral_le_of_norm_le hab
    ((ae_restrict_iff' measurableSet_Ioc).mp hbound)
    ((TauCeti.intervalIntegrable_sub_const_rpow hu a a b).const_mul K)).trans_eq ?_
  rw [intervalIntegral.integral_const_mul, TauCeti.integral_sub_const_rpow hu]

omit [NormedSpace ℝ E] in
/-- The mirror image of
`TauCeti.intervalIntegral.intervalIntegrable_of_norm_le_mul_sub_rpow_right`: the
singularity is at the right endpoint `b`. -/
theorem intervalIntegrable_of_norm_le_mul_sub_rpow_left {f : ℝ → E} {a b K u : ℝ}
    (hu : -1 < u) (hab : a ≤ b) (hmeas : AEStronglyMeasurable f (volume.restrict (Ioc a b)))
    (hbound : ∀ᵐ s ∂volume.restrict (Ioc a b), ‖f s‖ ≤ K * (b - s) ^ u) :
    IntervalIntegrable f volume a b := by
  rw [← uIoc_of_le hab] at hmeas hbound
  exact ((TauCeti.intervalIntegrable_sub_rpow hu a b).const_mul K).mono_fun' hmeas hbound

/-- The mirror image of
`TauCeti.intervalIntegral.norm_integral_le_of_norm_le_mul_sub_rpow_right`: the
singularity is at the right endpoint `b`. -/
theorem norm_integral_le_of_norm_le_mul_sub_rpow_left {f : ℝ → E} {a b K u : ℝ}
    (hu : -1 < u) (hab : a ≤ b)
    (hbound : ∀ᵐ s ∂volume.restrict (Ioc a b), ‖f s‖ ≤ K * (b - s) ^ u) :
    ‖∫ s in a..b, f s‖ ≤ K * ((b - a) ^ (u + 1) / (u + 1)) := by
  refine (intervalIntegral.norm_integral_le_of_norm_le hab
    ((ae_restrict_iff' measurableSet_Ioc).mp hbound)
    ((TauCeti.intervalIntegrable_sub_rpow hu a b).const_mul K)).trans_eq ?_
  rw [intervalIntegral.integral_const_mul, TauCeti.integral_sub_rpow hu]

end intervalIntegral

open MeasureTheory Set Real

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrate two complementary power bounds by splitting at `d`. The first power is integrable
at zero and the second at infinity; the resulting bound is uniform in the endpoint `t ≥ 0`. -/
theorem norm_intervalIntegral_le_of_rpow_bounds {f : ℝ → F} {a b A B d t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 < d) (ht : 0 ≤ t)
    (hnear : ∀ᵐ r ∂volume.restrict (Ioo 0 t), ‖f r‖ ≤ A * r ^ (a - 1))
    (hfar : ∀ᵐ r ∂volume.restrict (Ioo 0 t), ‖f r‖ ≤ B * r ^ (-b - 1)) :
    ‖∫ r in 0..t, f r‖ ≤ A / a * d ^ a + B / b * d ^ (-b) := by
  -- A non-integrable function has integral `0`.
  by_cases hf : IntervalIntegrable f volume 0 t
  swap
  · rw [intervalIntegral.integral_undef hf, norm_zero]
    positivity
  have hnear' : ∀ᵐ r ∂volume, r ∈ Ioc 0 t → ‖f r‖ ≤ A * r ^ (a - 1) := by
    rwa [restrict_Ioo_eq_restrict_Ioc, ae_restrict_iff' measurableSet_Ioc] at hnear
  have hfar' : ∀ᵐ r ∂volume, r ∈ Ioc 0 t → ‖f r‖ ≤ B * r ^ (-b - 1) := by
    rwa [restrict_Ioo_eq_restrict_Ioc, ae_restrict_iff' measurableSet_Ioc] at hfar
  have hsmall {s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
      ‖∫ r in 0..s, f r‖ ≤ A / a * s ^ a := by
    have hr : -1 < a - 1 := by linarith
    have hsub : Ioc 0 s ⊆ Ioc 0 t := Ioc_subset_Ioc_right hst
    have h := TauCeti.intervalIntegral.norm_integral_le_of_norm_le_mul_sub_rpow_right (f := f)
      (a := 0) (b := s) (K := A) hr hs
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (hnear'.mono fun r hr hrs => by simpa using hr (hsub hrs)))
    calc ‖∫ r in 0..s, f r‖ ≤ A * ((s - 0) ^ (a - 1 + 1) / (a - 1 + 1)) := h
      _ = A / a * s ^ a := by
        rw [sub_zero, sub_add_cancel]
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

/-- A constant bounding a norm almost everywhere against a function that is positive on
`(0, t)` is nonnegative. -/
private theorem nonneg_of_ae_norm_le_mul {F : Type*} [NormedAddCommGroup F] {Φ : ℝ → F}
    {w : ℝ → ℝ} {t C : ℝ} (ht : 0 < t) (hw : ∀ s ∈ Ioo 0 t, 0 < w s)
    (h : ∀ᵐ s, s ∈ Ioc 0 t → ‖Φ s‖ ≤ C * w s) : 0 ≤ C := by
  have h' : ∀ᵐ _ ∂volume.restrict (Ioo 0 t), 0 ≤ C := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h] with s hs hs'
    exact (mul_nonneg_iff_of_pos_right (hw s hs')).1 ((norm_nonneg _).trans (hs ⟨hs'.1, hs'.2.le⟩))
  have : (ae (volume.restrict (Ioo 0 t))).NeBot :=
    ae_neBot.2 (Measure.measure_univ_ne_zero.1 (by simp [ht]))
  exact h'.exists.elim fun _ h => h

open scoped Interval in
/-- Splitting a singular integral at distance `δ²` from its singular endpoint. If the integrand
is `O(A (t - s)^((α - 2)/2))`, which is integrable, and also `O(B δ (t - s)^((α - 3)/2))`, which is
integrable away from `s = t`, then using the first bound on `t - δ² < s < t` and the second on
`0 < s < t - δ²` bounds the integral over `[0, t]` by `(2A/α + 2B/(1 - α)) δ^α`. This is the time
integration behind parabolic Hölder estimates at two points at distance `δ`. -/
theorem norm_integral_le_of_ae_norm_le_rpow {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : ℝ → F} {α δ t A B : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (ht : 0 < t)
    (hδ : 0 < δ)
    (hΦA : ∀ᵐ s, s ∈ Ioc 0 t → ‖Φ s‖ ≤ A * (t - s) ^ ((α - 2) / 2))
    (hΦB : ∀ᵐ s, s ∈ Ioc 0 t → ‖Φ s‖ ≤ B * (t - s) ^ ((α - 3) / 2) * δ) :
    ‖∫ s in 0..t, Φ s‖ ≤ (2 / α * A + 2 / (1 - α) * B) * δ ^ α := by
  -- Both constants are nonnegative: the bounds hold at some point `s < t`, where `t - s > 0`.
  have hA : 0 ≤ A := nonneg_of_ae_norm_le_mul (Φ := Φ) (w := fun s => (t - s) ^ ((α - 2) / 2)) ht
    (fun _ hs => rpow_pos_of_pos (sub_pos.2 hs.2) _) hΦA
  have hB : 0 ≤ B := by
    refine (mul_nonneg_iff_of_pos_right hδ).1 (nonneg_of_ae_norm_le_mul (Φ := Φ)
      (w := fun s => (t - s) ^ ((α - 3) / 2)) (C := B * δ) ht
      (fun _ hs => rpow_pos_of_pos (sub_pos.2 hs.2) _) ?_)
    filter_upwards [hΦB] with s h hs
    exact (h hs).trans_eq (by ring)
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
    (sq_pos_of_pos hδ) ht.le
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

/-- **Difference of two integrals over nearby intervals.** Split `∫ₐ^t g₁ ∂μ` and
`∫ₐ^{t'} g₂ ∂μ` at a common point `s₀`, given that `g₁` is interval integrable for `μ` on
`[a, s₀]` and `[s₀, t]` and `g₂` on `[a, s₀]` and `[s₀, t']`. If `‖∫ₐ^{s₀} (g₁ - g₂) ∂μ‖ ≤ D`,
`‖∫_{s₀}^t g₁ ∂μ‖ ≤ B₁` and `‖∫_{s₀}^{t'} g₂ ∂μ‖ ≤ B₂`, then
`‖∫ₐ^t g₁ ∂μ - ∫ₐ^{t'} g₂ ∂μ‖ ≤ D + B₁ + B₂`. The integrals are oriented, and no ordering of `a`,
`s₀`, `t` and `t'` is assumed. -/
theorem norm_intervalIntegral_sub_le_of_sub_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {μ : Measure ℝ} {g₁ g₂ : ℝ → V} {a s₀ t t' D B₁ B₂ : ℝ}
    (hg₁ : IntervalIntegrable g₁ μ a s₀) (hg₁' : IntervalIntegrable g₁ μ s₀ t)
    (hg₂ : IntervalIntegrable g₂ μ a s₀) (hg₂' : IntervalIntegrable g₂ μ s₀ t')
    (hD : ‖∫ s in a..s₀, (g₁ s - g₂ s) ∂μ‖ ≤ D) (h₁ : ‖∫ s in s₀..t, g₁ s ∂μ‖ ≤ B₁)
    (h₂ : ‖∫ s in s₀..t', g₂ s ∂μ‖ ≤ B₂) :
    ‖(∫ s in a..t, g₁ s ∂μ) - ∫ s in a..t', g₂ s ∂μ‖ ≤ D + B₁ + B₂ :=
  calc ‖(∫ s in a..t, g₁ s ∂μ) - ∫ s in a..t', g₂ s ∂μ‖
      = ‖((∫ s in a..s₀, g₁ s ∂μ) - ∫ s in a..s₀, g₂ s ∂μ) + (∫ s in s₀..t, g₁ s ∂μ) -
          ∫ s in s₀..t', g₂ s ∂μ‖ := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hg₁ hg₁',
          ← intervalIntegral.integral_add_adjacent_intervals hg₂ hg₂']
        congr 1
        abel
    _ = ‖(∫ s in a..s₀, (g₁ s - g₂ s) ∂μ) + (∫ s in s₀..t, g₁ s ∂μ) -
          ∫ s in s₀..t', g₂ s ∂μ‖ := by
        rw [intervalIntegral.integral_sub hg₁ hg₂]
    _ ≤ D + B₁ + B₂ :=
        (norm_sub_le_of_le (norm_add_le _ _) le_rfl).trans (add_le_add (add_le_add hD h₁) h₂)

end TauCeti
