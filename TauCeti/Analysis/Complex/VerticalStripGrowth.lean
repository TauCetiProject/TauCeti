/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Polynomial growth on vertical strips

`TauCeti.HasVerticalStripGrowth f` means that on each bounded interval of real parts,
`f` is bounded by a power of `1 + |Im s|` above some height. The height threshold may
depend on the strip. In particular, the definition does not demand boundedness near
poles at finite height.

We prove closure under sums, products, and conjugate reflection. These laws allow
strip estimates for completed L-functions to be assembled from simpler estimates.
Constants and exponentials with real slope have the property, whereas the entire
function `exp (-s²)` does not: it grows like `exp (t²)` on the imaginary axis.
-/

public section

open Complex ComplexConjugate Filter
open scoped Topology

namespace TauCeti

/-- Polynomial growth at large imaginary height on every closed vertical strip.
The constants, exponent, and height threshold may depend on the strip. No continuity
or meromorphy is required, and no bound is imposed below the threshold. -/
def HasVerticalStripGrowth (f : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ T : ℝ, 0 ≤ T ∧
    ∀ s : ℂ, s.re ∈ Set.Icc a b → T ≤ |s.im| →
      ‖f s‖ ≤ C * (1 + |s.im|) ^ A

variable {f g : ℂ → ℂ}

/-- The defining strip estimate, including its height threshold. -/
theorem hasVerticalStripGrowth_def : HasVerticalStripGrowth f ↔
    ∀ a b : ℝ, a < b → ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ s : ℂ, s.re ∈ Set.Icc a b → T ≤ |s.im| →
        ‖f s‖ ≤ C * (1 + |s.im|) ^ A := Iff.rfl

/-- A strip bound restricts to a smaller interval of real parts with exactly the
same constant, exponent, and height threshold. -/
theorem verticalStripBound_mono {a b a' b' C A T : ℝ}
    (h : ∀ s : ℂ, s.re ∈ Set.Icc a b → T ≤ |s.im| →
      ‖f s‖ ≤ C * (1 + |s.im|) ^ A) (ha : a ≤ a') (hb : b' ≤ b) :
    ∀ s : ℂ, s.re ∈ Set.Icc a' b' → T ≤ |s.im| →
      ‖f s‖ ≤ C * (1 + |s.im|) ^ A :=
  fun s hs ht ↦ h s (Set.Icc_subset_Icc ha hb hs) ht

/-- Pointwise equal functions have the same strip growth. -/
theorem HasVerticalStripGrowth.congr (hf : HasVerticalStripGrowth f)
    (h : ∀ s, f s = g s) : HasVerticalStripGrowth g := by
  simpa only [← funext h] using hf

/-- Constant functions have strip growth. -/
@[simp]
theorem hasVerticalStripGrowth_const (c : ℂ) : HasVerticalStripGrowth (fun _ ↦ c) := by
  intro a b hab
  refine ⟨‖c‖ + 1, by positivity, 0, le_rfl, 0, le_rfl, ?_⟩
  intro s hs ht
  simp

/-- Negation preserves strip growth. -/
theorem HasVerticalStripGrowth.neg (hf : HasVerticalStripGrowth f) :
    HasVerticalStripGrowth (fun s ↦ -f s) := by
  intro a b hab
  obtain ⟨C, hC, A, hA, T, hT, h⟩ := hf a b hab
  exact ⟨C, hC, A, hA, T, hT, fun s hs ht ↦ by simpa using h s hs ht⟩

/-- Sums of functions with strip growth have strip growth. -/
theorem HasVerticalStripGrowth.add (hf : HasVerticalStripGrowth f)
    (hg : HasVerticalStripGrowth g) : HasVerticalStripGrowth (fun s ↦ f s + g s) := by
  intro a b hab
  obtain ⟨C, hC, A, hA, T, hT, hf⟩ := hf a b hab
  obtain ⟨D, hD, B, hB, S, hS, hg⟩ := hg a b hab
  refine ⟨C + D, by positivity, max A B, le_max_of_le_left hA,
    max T S, le_max_of_le_left hT, ?_⟩
  intro s hs ht
  have hbase : 1 ≤ 1 + |s.im| := le_add_of_nonneg_right (abs_nonneg _)
  have hf' := (hf s hs ((le_max_left T S).trans ht)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase (le_max_left A B)) hC.le)
  have hg' := (hg s hs ((le_max_right T S).trans ht)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase (le_max_right A B)) hD.le)
  exact (norm_add_le _ _).trans (by nlinarith [add_le_add hf' hg'])

/-- Differences preserve strip growth. -/
theorem HasVerticalStripGrowth.sub (hf : HasVerticalStripGrowth f)
    (hg : HasVerticalStripGrowth g) : HasVerticalStripGrowth (fun s ↦ f s - g s) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Products of functions with strip growth have strip growth. -/
theorem HasVerticalStripGrowth.mul (hf : HasVerticalStripGrowth f)
    (hg : HasVerticalStripGrowth g) : HasVerticalStripGrowth (fun s ↦ f s * g s) := by
  intro a b hab
  obtain ⟨C, hC, A, hA, T, hT, hf⟩ := hf a b hab
  obtain ⟨D, hD, B, hB, S, hS, hg⟩ := hg a b hab
  refine ⟨C * D, mul_pos hC hD, A + B, add_nonneg hA hB,
    max T S, le_max_of_le_left hT, ?_⟩
  intro s hs ht
  have hbase : 0 < 1 + |s.im| := by positivity
  calc
    ‖f s * g s‖ = ‖f s‖ * ‖g s‖ := norm_mul _ _
    _ ≤ (C * (1 + |s.im|) ^ A) * (D * (1 + |s.im|) ^ B) :=
      mul_le_mul (hf s hs ((le_max_left T S).trans ht))
        (hg s hs ((le_max_right T S).trans ht)) (norm_nonneg _) (by positivity)
    _ = C * D * (1 + |s.im|) ^ (A + B) := by
      rw [Real.rpow_add hbase]
      ring

/-- Conjugate reflection preserves strip growth. -/
theorem HasVerticalStripGrowth.conj (hf : HasVerticalStripGrowth f) :
    HasVerticalStripGrowth (fun s ↦ conj (f (conj s))) := by
  intro a b hab
  obtain ⟨C, hC, A, hA, T, hT, h⟩ := hf a b hab
  refine ⟨C, hC, A, hA, T, hT, ?_⟩
  intro s hs ht
  simpa using h (conj s) (by simpa using hs) (by simpa using ht)

/-- Exponentials with real slope have strip growth. -/
theorem hasVerticalStripGrowth_cexp_real_mul (c : ℝ) :
    HasVerticalStripGrowth (fun s ↦ exp (c * s)) := by
  intro a b hab
  refine ⟨Real.exp (|c| * max |a| |b|), Real.exp_pos _, 0, le_rfl, 0, le_rfl, ?_⟩
  intro s hs ht
  have hre : |s.re| ≤ max |a| |b| := by
    exact abs_le.mpr ⟨(neg_le_neg (le_max_left |a| |b|)).trans
      ((neg_abs_le a).trans hs.1), hs.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  have hmul : c * s.re ≤ |c| * max |a| |b| :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hre (abs_nonneg c))
  simpa [Complex.norm_exp] using Real.exp_le_exp.mpr hmul

/-- Entirety does not imply strip growth: on the imaginary axis this function
has norm `exp (t²)`, which dominates every polynomial. -/
theorem not_hasVerticalStripGrowth_cexp_neg_sq :
    ¬ HasVerticalStripGrowth (fun s ↦ exp (-(s ^ 2))) := by
  intro hf
  obtain ⟨C, hC, A, hA, T, hT, h⟩ := hf 0 1 zero_lt_one
  have hlarge := (tendsto_exp_div_rpow_atTop A).eventually (eventually_gt_atTop C)
  obtain ⟨x, hx, hratio⟩ := ((eventually_ge_atTop (max (T + 1) 3)).and hlarge).exists
  have hxT : T ≤ x - 1 := by linarith [le_trans (le_max_left (T + 1) 3) hx]
  have hx3 : 3 ≤ x := (le_max_right (T + 1) 3).trans hx
  have hxpos : 0 < x := by linarith
  have hbound := h ((x - 1 : ℝ) * I) (by simp)
    (by simpa [abs_of_nonneg (by linarith : 0 ≤ x - 1)] using hxT)
  have hnorm : ‖exp (-(((x - 1 : ℝ) : ℂ) * I) ^ 2)‖ = Real.exp ((x - 1) ^ 2) := by
    simp [Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im]
  have hpoly : Real.exp ((x - 1) ^ 2) ≤ C * x ^ A := by
    rw [hnorm] at hbound
    simpa [abs_of_nonneg (by linarith : 0 ≤ x - 1)] using hbound
  have hexp : Real.exp x ≤ Real.exp ((x - 1) ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hratio' : Real.exp x ≤ C * x ^ A := hexp.trans hpoly
  exact (not_lt_of_ge ((div_le_iff₀ (Real.rpow_pos_of_pos hxpos A)).mpr hratio')) hratio

end TauCeti
