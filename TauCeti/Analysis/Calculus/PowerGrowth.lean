/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Power growth from a differential inequality

The inequality `α f(t) ≤ t f'(t)` makes `f(t) / t^α` nondecreasing on positive
intervals. It gives power bounds at smaller radii from data at a larger radius,
including when `f` vanishes. No division by `f` or positivity assumption on `f` is needed.

Conversely, the inequality `m(ρ) ^ (1 - a) ≤ K m'(ρ)`, holding only at almost every `ρ`, forces a
monotone function `m` which is positive on `(0, r)` to grow at least like a power:
`a r ≤ K m(r) ^ a` (`TauCeti.mul_le_mul_rpow_of_rpow_one_sub_le_mul_deriv`). No continuity of `m` is
needed: the derivative of the monotone function `m ^ a` integrates to at most its increment. This
is the integration step of the lower density estimates for sets of finite perimeter, where
`m(ρ)` is the volume of the set in the ball of radius `ρ`.
-/

public section

open Set MeasureTheory

namespace TauCeti

/-- An Euler differential inequality makes the power-normalized function nondecreasing
on any convex set of positive real numbers. Only continuity is required at boundary points;
the derivative and differential inequality are needed only on the interior. -/
theorem monotoneOn_div_rpow_of_mul_le_mul_deriv {f f' : ℝ → ℝ} {s : Set ℝ} {α : ℝ}
    (hs : Convex ℝ s) (hpos : ∀ t ∈ s, 0 < t)
    (hcont : ContinuousOn f s)
    (hf : ∀ t ∈ interior s, HasDerivAt f (f' t) t)
    (hle : ∀ t ∈ interior s, α * f t ≤ t * f' t) :
    MonotoneOn (fun t ↦ f t / t ^ α) s := by
  have hd (t : ℝ) (ht : t ∈ interior s) :=
    (hf t ht).div (Real.hasDerivAt_rpow_const (Or.inl (hpos t (interior_subset ht)).ne'))
      (Real.rpow_pos_of_pos (hpos t (interior_subset ht)) α).ne'
  have hpow : ContinuousOn (fun t : ℝ ↦ t ^ α) s :=
    continuousOn_id.rpow_const (fun t ht ↦ Or.inl (hpos t ht).ne')
  apply monotoneOn_of_deriv_nonneg hs
    (hcont.div hpow
      (fun t ht ↦ (Real.rpow_pos_of_pos (hpos t ht) α).ne'))
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t ht).deriv]
  apply div_nonneg _ (sq_nonneg _)
  rw [Real.rpow_sub_one (hpos t (interior_subset ht)).ne']
  have h := hle t ht
  have hp := Real.rpow_pos_of_pos (hpos t (interior_subset ht)) α
  have htpos := hpos t (interior_subset ht)
  convert div_nonneg (mul_nonneg (sub_nonneg.mpr h) hp.le) htpos.le using 1
  field_simp

/-- **Power growth from an almost-everywhere differential inequality.** Let `m` be monotone on
`[0, r]`, nonnegative at `0` and positive on `(0, r)`. If `m(ρ) ^ (1 - a) ≤ K m'(ρ)` for almost
every `ρ ∈ (0, r)`, where `a > 0` and `K ≥ 0`, then `a r ≤ K m(r) ^ a`. -/
theorem mul_le_mul_rpow_of_rpow_one_sub_le_mul_deriv {m : ℝ → ℝ} {a K r : ℝ} (hr : 0 ≤ r)
    (hm : MonotoneOn m (Icc 0 r)) (hm0 : 0 ≤ m 0) (hpos : ∀ ρ ∈ Ioo 0 r, 0 < m ρ)
    (ha : 0 < a) (hK : 0 ≤ K)
    (h : ∀ᵐ ρ, ρ ∈ Ioo 0 r → m ρ ^ (1 - a) ≤ K * deriv m ρ) :
    a * r ≤ K * m r ^ a := by
  rcases hr.eq_or_lt with rfl | hr'
  · simpa using mul_nonneg hK (Real.rpow_nonneg hm0 a)
  -- The inequality at a single point of `(0, r)` forces `K > 0`.
  replace hK : 0 < K := by
    refine hK.lt_of_ne fun hK0 => ?_
    have : (ae (volume.restrict (Ioo (0 : ℝ) r))).NeBot := ae_restrict_neBot.2 (by simp [hr'])
    have hev : ∀ᵐ ρ ∂volume.restrict (Ioo 0 r),
        ρ ∈ Ioo 0 r ∧ (ρ ∈ Ioo 0 r → m ρ ^ (1 - a) ≤ K * deriv m ρ) :=
      (ae_restrict_mem measurableSet_Ioo).and (ae_restrict_of_ae h)
    obtain ⟨ρ, hρ, hρ'⟩ := hev.exists
    have h0 := hρ' hρ
    rw [← hK0, zero_mul] at h0
    exact (Real.rpow_pos_of_pos (hpos ρ hρ) _).not_ge h0
  set g : ℝ → ℝ := fun ρ => m ρ ^ a
  have hg : MonotoneOn g (uIcc 0 r) := by
    rw [uIcc_of_le hr]
    intro ρ hρ ρ' hρ' hle
    exact Real.rpow_le_rpow (hm0.trans (hm ⟨le_rfl, hr⟩ hρ hρ.1)) (hm hρ hρ' hle) ha.le
  -- `a / K ≤ g'` at almost every point of `[0, r]`, where
  -- `K g' = a m ^ (a - 1) (K m') ≥ a m ^ (a - 1) m ^ (1 - a) = a`.
  have hlow : (fun _ => a / K) ≤ᵐ[volume.restrict (Icc 0 r)] deriv g := by
    rw [Filter.EventuallyLE, Measure.restrict_congr_set Ioo_ae_eq_Icc.symm,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h, (hm.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem]
      with ρ hρ hd hρI
    have hmρ := hpos ρ hρI
    have hd' := (hd hρI).differentiableAt (Ioo_mem_nhds hρI.1 hρI.2)
    rw [deriv_rpow_const hd' (Or.inl hmρ.ne'), div_le_iff₀ hK]
    calc a = a * (m ρ ^ (a - 1) * m ρ ^ (1 - a)) := by
          rw [← Real.rpow_add hmρ, sub_add_sub_cancel', sub_self, Real.rpow_zero, mul_one]
      _ ≤ a * (m ρ ^ (a - 1) * (K * deriv m ρ)) := by
          gcongr
          exact hρ hρI
      _ = deriv m ρ * a * m ρ ^ (a - 1) * K := by ring
  -- Integrating, `a r / K ≤ ∫₀^r g' ≤ g r - g 0 ≤ g r`.
  have hint := intervalIntegral.integral_mono_ae_restrict hr intervalIntegrable_const
    hg.intervalIntegrable_deriv hlow
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  have hup := hg.intervalIntegral_deriv_mem_uIcc
  rw [uIcc_of_le (sub_nonneg.2 (hg (by simp) (by simp [hr]) (by simp [hr])))] at hup
  have hgr := hint.trans (hup.2.trans (sub_le_self _ (Real.rpow_nonneg hm0 a)))
  rw [mul_div_assoc', div_le_iff₀ hK] at hgr
  linarith

end TauCeti

end
