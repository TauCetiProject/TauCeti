/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
import TauCeti.Analysis.Asymptotics.Sum.ExponentialTail

/-!
# Weighted zero sums in Linnik's range

A log-free density bound controls the weighted sum of zeros of real part at least `1/2`.
Given both an ordinary zero-free region and the Deuring–Heilbronn repulsion, the saving
from the latter can be taken as a factor `min 1 D`, where `D` is the scaled exceptional gap.
This is the zero-sum step in the proof of the prime number theorem in Linnik's range;
see Iwaniec–Kowalski, *Analytic Number Theory*, Chapter 18.
-/

public section

open Real

namespace TauCeti

-- Use one quarter of the exponential rate for the ordinary region and another for repulsion.
private theorem exp_neg_mul_gap_le {V ℒ c κ D g : ℝ} (hℒ : 0 < ℒ) (hκ : 0 < κ)
    (hD : 0 < D) (hV : (4 / κ) * ℒ ≤ V) (hg : 0 ≤ g) (hbase : c / ℒ ≤ g)
    (hrep : κ / ℒ * log D⁻¹ ≤ g) :
    exp (-(V / 2) * g) ≤ min 1 D * exp (-(c / 4) * V / ℒ) := by
  have hV₀ : 0 ≤ V := le_trans (by positivity) hV
  have hVκ : 1 ≤ V / 4 * (κ / ℒ) := by
    rw [← mul_div_assoc, le_div_iff₀ hℒ, one_mul, div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
    calc
      ℒ * 4 = ((4 / κ) * ℒ) * κ := by field_simp
      _ ≤ V * κ := mul_le_mul_of_nonneg_right hV hκ.le
  have hbase' : exp (-(V / 4) * g) ≤ exp (-(c / 4) * V / ℒ) := by
    apply exp_le_exp.mpr
    calc
      _ ≤ -(V / 4) * (c / ℒ) := by
        simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hbase (by positivity))
      _ = _ := by ring
  have hrep' : exp (-(V / 4) * g) ≤ min 1 D := by
    have h₁ : exp (-(V / 4) * g) ≤ 1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by positivity)) hg)
    refine le_min h₁ ?_
    by_cases hD₁ : 1 ≤ D
    · exact h₁.trans hD₁
    have hlog : 0 ≤ log D⁻¹ := by
      rw [log_inv, neg_nonneg]
      exact log_nonpos hD.le (le_of_not_ge hD₁)
    rw [← exp_log hD, exp_le_exp]
    calc
      _ ≤ -(V / 4) * (κ / ℒ * log D⁻¹) := by
        simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hrep (by positivity))
      _ = -(V / 4 * (κ / ℒ) * log D⁻¹) := by ring
      _ ≤ -(1 * log D⁻¹) := by gcongr
      _ = log D := by simp
  rw [show -(V / 2) * g = (-(V / 4) * g) + (-(V / 4) * g) by ring, exp_add]
  exact mul_le_mul hrep' hbase' (exp_pos _).le (le_min zero_le_one hD.le)

/-- The normalized zero sum `∑ mρ x ^ (Re ρ - 1)` in Linnik's range. The index set
contains the retained zeros with real part at least `1/2` and can include zeros from many
L-functions. The count at each abscissa includes zeros on the boundary. In applications
`ℒ = log (q * (T + 2))` and `D = (1 - β₁) * ℒ / κ` for the exceptional zero `β₁`;
set `D = 1` when there is no exceptional zero. -/
theorem sum_rpow_re_sub_one_le_of_zeroDensity {ι : Type*} {s : Finset ι} (ρ : ι → ℂ)
    (m : ι → ℕ) {x ℒ A C c κ D : ℝ} (hℒ : 0 < ℒ) (hc : 0 ≤ c) (hκ : 0 < κ) (hD : 0 < D)
    (hx : exp (max (2 * A) (4 / κ) * ℒ) ≤ x) (hβ : ∀ i ∈ s, 1 / 2 ≤ (ρ i).re)
    (hgap : ∀ i ∈ s, max (c / ℒ) (κ / ℒ * log D⁻¹) ≤ 1 - (ρ i).re)
    (hcount : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      (∑ i ∈ s.filter (fun i ↦ σ ≤ (ρ i).re), (m i : ℝ)) ≤ C * exp (A * ℒ * (1 - σ))) :
    (∑ i ∈ s, (m i : ℝ) * x ^ ((ρ i).re - 1)) ≤
      2 * C * min 1 D * exp (-(c / 4) * log x / ℒ) := by
  let V := log x
  let B := max 0 (A * ℒ)
  let g := max (c / ℒ) (κ / ℒ * log D⁻¹)
  have hx₀ : 0 < x := (exp_pos _).trans_le hx
  have hsize : max (2 * A) (4 / κ) * ℒ ≤ V := (le_log_iff_exp_le hx₀).2 hx
  have hVκ : (4 / κ) * ℒ ≤ V := (mul_le_mul_of_nonneg_right (le_max_right ..) hℒ.le).trans hsize
  have hV : 0 < V := (by positivity : 0 < (4 / κ) * ℒ).trans_le hVκ
  have hBV : B ≤ V / 2 := by
    have hVA := (mul_le_mul_of_nonneg_right (le_max_left (2 * A) (4 / κ)) hℒ.le).trans hsize
    exact max_le (by positivity) (by linarith)
  have hg : 0 ≤ g := (div_nonneg hc hℒ.le).trans (le_max_left ..)
  have hC : 0 ≤ C := by
    have h := hcount 1 (by norm_num)
    simp only [sub_self, mul_zero, exp_zero, mul_one] at h
    exact le_trans (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) h
  have hcount' (u : ℝ) (hu : g < u) :
      (∑ i ∈ s.filter (fun i ↦ 1 - (ρ i).re ≤ u), (m i : ℝ)) ≤ C * exp (B * u) := by
    let v := min u (1 / 2)
    have hv₀ : 0 ≤ v := le_min (hg.trans hu.le) (by norm_num)
    have hv₁ : v ≤ 1 / 2 := min_le_right ..
    have hf : s.filter (fun i ↦ 1 - (ρ i).re ≤ u) = s.filter (fun i ↦ 1 - v ≤ (ρ i).re) := by
      refine Finset.filter_congr fun i hi ↦ ?_
      have hhalf : 1 - (ρ i).re ≤ 1 / 2 := by linarith [hβ i hi]
      calc
        _ ↔ 1 - (ρ i).re ≤ v := by simp only [v, le_min_iff, hhalf, and_true]
        _ ↔ _ := sub_le_comm
    rw [hf]
    refine (hcount (1 - v) ⟨by linarith, by linarith⟩).trans ?_
    rw [sub_sub_cancel]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) hC
    exact (mul_le_mul_of_nonneg_right (le_max_right 0 (A * ℒ)) hv₀).trans
      (mul_le_mul_of_nonneg_left (min_le_left ..) (le_max_left ..))
  have hdecay := s.sum_mul_exp_neg_mul_le_of_cumulative_le (fun i ↦ 1 - (ρ i).re)
    (fun i ↦ (m i : ℝ)) hV (by linarith : B < V) hgap hcount'
  have hfactor : V / (V - B) ≤ 2 := by
    rw [div_le_iff₀ (by linarith : 0 < V - B)]
    linarith
  calc
    _ = ∑ i ∈ s, (m i : ℝ) * exp (-V * (1 - (ρ i).re)) := by
      simp_rw [rpow_def_of_pos hx₀]
      exact Finset.sum_congr rfl fun i _ ↦ by congr 2; ring
    _ ≤ C * (V / (V - B)) * exp (-(V - B) * g) := hdecay
    _ ≤ C * 2 * exp (-(V / 2) * g) := by
      gcongr
      linarith
    _ ≤ _ := by
      rw [mul_comm C 2, mul_assoc (2 * C)]
      exact mul_le_mul_of_nonneg_left
        (exp_neg_mul_gap_le hℒ hκ hD hVκ hg (le_max_left ..) (le_max_right ..)) (by positivity)

end TauCeti
