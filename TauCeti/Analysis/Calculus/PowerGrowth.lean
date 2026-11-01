/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Power growth from a differential inequality

The inequality `α f(t) ≤ t f'(t)` makes `f(t) / t^α` nondecreasing on positive
intervals. It gives power bounds at smaller radii from data at a larger radius,
including when `f` vanishes. No division by `f` or positivity assumption on `f` is needed.

The inequality `m(ρ) ^ (1 - 1/n) ≤ K m'(ρ)`, for a monotone function `m` positive on `(0, δ)`,
gives the lower bound `(r / (n K)) ^ n ≤ m(r)` on `[0, δ]`
(`Monotone.div_pow_le_of_ae_rpow_le_mul_deriv`). It only needs to hold at almost every radius:
a monotone function grows by at least the integral of its derivative. This is the form in which
an isoperimetric inequality gives lower density bounds for `m(ρ) = μ(s ∩ ball x ρ)`.
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

/-- **Power growth from an isoperimetric-type differential inequality.** Let `m` be a monotone
function with `0 ≤ m 0` which is positive on `(0, δ)`, and suppose that
`m(ρ) ^ (1 - 1/n) ≤ K m'(ρ)` for almost every `ρ ∈ (0, δ)`, where `K ≥ 0`. Then
`(r / (n K)) ^ n ≤ m(r)` for every `r ∈ [0, δ]`. -/
theorem _root_.Monotone.div_pow_le_of_ae_rpow_le_mul_deriv {m : ℝ → ℝ} (hm : Monotone m)
    (hm0 : 0 ≤ m 0) {n : ℕ} (hn : n ≠ 0) {K δ : ℝ} (hK : 0 ≤ K)
    (hpos : ∀ ρ ∈ Ioo 0 δ, 0 < m ρ)
    (h : ∀ᵐ ρ, ρ ∈ Ioo 0 δ → m ρ ^ (1 - (n : ℝ)⁻¹) ≤ K * deriv m ρ) {r : ℝ} (hr : r ∈ Icc 0 δ) :
    (r / (n * K)) ^ n ≤ m r := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hmr : 0 ≤ m r := hm0.trans (hm hr.1)
  set f : ℝ → ℝ := fun ρ => m ρ ^ (n : ℝ)⁻¹
  have hf : MonotoneOn f (Ici 0) := fun a ha b _ hab =>
    Real.rpow_le_rpow (hm0.trans (hm ha)) (hm hab) (inv_nonneg.2 n.cast_nonneg)
  -- The differential inequality gives `(n K)⁻¹ ≤ f'` almost everywhere on `(0, δ)`.
  have hderiv : ∀ᵐ ρ, ρ ∈ Ioo 0 δ → (n * K)⁻¹ ≤ deriv f ρ := by
    filter_upwards [hm.ae_differentiableAt, h] with ρ hdiff hρ hρI
    have hmρ := hpos ρ hρI
    have hA : 0 < m ρ ^ (1 - (n : ℝ)⁻¹) := Real.rpow_pos_of_pos hmρ _
    have hd : 0 < deriv m ρ := pos_of_mul_pos_right (hA.trans_le (hρ hρI)) hK
    have hK0 : 0 < K := pos_of_mul_pos_left (hA.trans_le (hρ hρI)) hd.le
    have hneg : m ρ ^ ((n : ℝ)⁻¹ - 1) = (m ρ ^ (1 - (n : ℝ)⁻¹))⁻¹ := by
      rw [← Real.rpow_neg hmρ.le, neg_sub]
    rw [(hdiff.hasDerivAt.rpow_const (p := (n : ℝ)⁻¹) (Or.inl hmρ.ne')).deriv, hneg]
    calc (n * K)⁻¹ = deriv m ρ * (n : ℝ)⁻¹ * (K * deriv m ρ)⁻¹ := by field_simp
      _ ≤ deriv m ρ * (n : ℝ)⁻¹ * (m ρ ^ (1 - (n : ℝ)⁻¹))⁻¹ := by gcongr; exact hρ hρI
  -- A monotone function grows by at least the integral of its derivative.
  have hfI : MonotoneOn f (uIcc 0 r) := hf.mono (uIcc_of_le hr.1 ▸ Icc_subset_Ici_self)
  have hint := hfI.intervalIntegral_deriv_mem_uIcc
  rw [uIcc_of_le (sub_nonneg.2 (hf self_mem_Ici hr.1 hr.1))] at hint
  have hlow : r * (n * K)⁻¹ ≤ ∫ ρ in 0..r, deriv f ρ := by
    have h := intervalIntegral.integral_mono_ae_restrict hr.1 intervalIntegrable_const
      hfI.intervalIntegrable_deriv
      (f := fun _ => (n * K)⁻¹) (by
        rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
        exact (ae_restrict_iff' measurableSet_Ioo).2
          (hderiv.mono fun ρ hρ hρI => hρ ⟨hρI.1, hρI.2.trans_le hr.2⟩))
    rwa [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  have hfr : r / (n * K) ≤ f r := by
    rw [div_eq_mul_inv]
    linarith [hint.2, Real.rpow_nonneg hm0 (n : ℝ)⁻¹]
  calc (r / (n * K)) ^ n ≤ f r ^ n := pow_le_pow_left₀ (div_nonneg hr.1 (by positivity)) hfr n
    _ = m r := Real.rpow_inv_natCast_pow hmr hn

end TauCeti

end
