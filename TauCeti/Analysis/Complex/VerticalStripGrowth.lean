/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial growth on vertical strips

`TauCeti.HasVerticalStripGrowth f` says that on each bounded interval of real parts,
`f` is bounded by a power of `1 + |Im s|` at sufficiently large absolute height.
The height threshold depends on the strip: in particular, poles at nonzero heights
need not obstruct this property. No regularity of `f` is required.

The property is stable under addition and multiplication. Bounds extend to degenerate
strips, and real exponential functions provide nonconstant examples of vertical-strip growth.
These facts allow growth estimates for completed L-functions to be assembled from their factors.
-/

public section

namespace TauCeti

/-- Polynomial growth at large absolute height on every closed vertical strip.
The positive constant, nonnegative exponent, and nonnegative height threshold may all
depend on the strip. -/
def HasVerticalStripGrowth (f : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ T₀ : ℝ, 0 ≤ T₀ ∧
    ∀ s : ℂ, s.re ∈ Set.Icc a b → T₀ ≤ |s.im| →
      ‖f s‖ ≤ C * (1 + |s.im|) ^ A

/-- Unfolds `HasVerticalStripGrowth` into its quantifier form. -/
theorem hasVerticalStripGrowth_iff {f : ℂ → ℂ} :
    HasVerticalStripGrowth f ↔
      ∀ a b : ℝ, a < b → ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ T₀ : ℝ, 0 ≤ T₀ ∧
        ∀ s : ℂ, s.re ∈ Set.Icc a b → T₀ ≤ |s.im| →
          ‖f s‖ ≤ C * (1 + |s.im|) ^ A := Iff.rfl

namespace HasVerticalStripGrowth

variable {f g : ℂ → ℂ}

/-- Growth bounds hold on every closed strip `a ≤ re s ≤ b` with `a ≤ b`,
including a single vertical line. -/
theorem exists_bound (hf : HasVerticalStripGrowth f) {a b : ℝ} (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      ∀ s : ℂ, s.re ∈ Set.Icc a b → T₀ ≤ |s.im| →
        ‖f s‖ ≤ C * (1 + |s.im|) ^ A := by
  obtain ⟨C, hC, A, hA, T₀, hT₀, hbound⟩ := hf (a - 1) (b + 1) (by linarith)
  exact ⟨C, hC, A, hA, T₀, hT₀, fun s hs ht ↦
    hbound s ⟨by linarith [hs.1], by linarith [hs.2]⟩ ht⟩

/-- Pointwise domination of norms transfers vertical-strip growth. -/
theorem mono (hg : HasVerticalStripGrowth g) (hfg : ∀ s, ‖f s‖ ≤ ‖g s‖) :
    HasVerticalStripGrowth f := by
  intro a b hab
  obtain ⟨C, hC, A, hA, T₀, hT₀, hbound⟩ := hg a b hab
  exact ⟨C, hC, A, hA, T₀, hT₀, fun s hs ht ↦ (hfg s).trans (hbound s hs ht)⟩

/-- Vertical-strip growth is stable under addition. -/
theorem add (hf : HasVerticalStripGrowth f) (hg : HasVerticalStripGrowth g) :
    HasVerticalStripGrowth (fun s ↦ f s + g s) := by
  intro a b hab
  obtain ⟨C, hC, A, hA, T, hT, hfbound⟩ := hf a b hab
  obtain ⟨D, hD, B, hB, U, hU, hgbound⟩ := hg a b hab
  refine ⟨C + D, add_pos hC hD, max A B, le_max_of_le_left hA,
    max T U, le_max_of_le_left hT, fun s hs ht ↦ ?_⟩
  have hbase : 1 ≤ 1 + |s.im| := le_add_of_nonneg_right (abs_nonneg _)
  calc
    ‖f s + g s‖ ≤ ‖f s‖ + ‖g s‖ := norm_add_le _ _
    _ ≤ C * (1 + |s.im|) ^ A + D * (1 + |s.im|) ^ B :=
      by
        gcongr
        · exact hfbound s hs ((le_max_left _ _).trans ht)
        · exact hgbound s hs ((le_max_right _ _).trans ht)
    _ ≤ C * (1 + |s.im|) ^ max A B + D * (1 + |s.im|) ^ max A B :=
      by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = (C + D) * (1 + |s.im|) ^ max A B := (add_mul _ _ _).symm

/-- Vertical-strip growth is stable under multiplication. -/
theorem mul (hf : HasVerticalStripGrowth f) (hg : HasVerticalStripGrowth g) :
    HasVerticalStripGrowth (fun s ↦ f s * g s) := by
  intro a b hab
  obtain ⟨C, hC, A, hA, T, hT, hfbound⟩ := hf a b hab
  obtain ⟨D, hD, B, hB, U, hU, hgbound⟩ := hg a b hab
  refine ⟨C * D, mul_pos hC hD, A + B, add_nonneg hA hB,
    max T U, le_max_of_le_left hT, fun s hs ht ↦ ?_⟩
  calc
    ‖f s * g s‖ = ‖f s‖ * ‖g s‖ := norm_mul _ _
    _ ≤ (C * (1 + |s.im|) ^ A) * (D * (1 + |s.im|) ^ B) :=
      by
        gcongr
        · exact hfbound s hs ((le_max_left _ _).trans ht)
        · exact hgbound s hs ((le_max_right _ _).trans ht)
    _ = (C * D) * (1 + |s.im|) ^ (A + B) := by
      rw [Real.rpow_add (by positivity)]
      ring

/-- Vertical-strip growth is stable under negation. -/
theorem neg (hf : HasVerticalStripGrowth f) :
    HasVerticalStripGrowth (fun s ↦ -f s) :=
  hf.mono fun s ↦ (norm_neg (f s)).le

/-- Vertical-strip growth is stable under subtraction. -/
theorem sub (hf : HasVerticalStripGrowth f) (hg : HasVerticalStripGrowth g) :
    HasVerticalStripGrowth (fun s ↦ f s - g s) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end HasVerticalStripGrowth

/-- Constant functions have vertical-strip growth. -/
@[simp]
theorem hasVerticalStripGrowth_const {c : ℂ} : HasVerticalStripGrowth (fun _ ↦ c) := by
  intro a b hab
  exact ⟨‖c‖ + 1, by positivity, 0, le_rfl, 0, le_rfl, fun s _ _ ↦ by simp⟩

namespace HasVerticalStripGrowth

variable {f : ℂ → ℂ}

/-- Multiplication by a constant preserves vertical-strip growth. -/
theorem const_mul (hf : HasVerticalStripGrowth f) (c : ℂ) :
    HasVerticalStripGrowth (fun s ↦ c * f s) :=
  hasVerticalStripGrowth_const.mul hf

/-- Natural powers preserve vertical-strip growth. -/
theorem pow (hf : HasVerticalStripGrowth f) (n : ℕ) :
    HasVerticalStripGrowth (fun s ↦ f s ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (hasVerticalStripGrowth_const (c := 1))
  | succ n ih => simpa only [pow_succ] using ih.mul hf

end HasVerticalStripGrowth

/-- Pointwise equal functions have the same vertical-strip growth property. -/
theorem hasVerticalStripGrowth_congr {f g : ℂ → ℂ} (h : ∀ s, f s = g s) :
    HasVerticalStripGrowth f ↔ HasVerticalStripGrowth g := by
  rw [funext h]

/-- Real exponentials `exp (r * s)` have vertical-strip growth. -/
theorem hasVerticalStripGrowth_cexp_ofReal_mul {r : ℝ} :
    HasVerticalStripGrowth (fun s : ℂ ↦ Complex.exp (r * s)) := by
  intro a b hab
  refine ⟨Real.exp (|r| * max |a| |b|), Real.exp_pos _, 0, le_rfl,
    0, le_rfl, fun s hs _ ↦ ?_⟩
  have hre : |s.re| ≤ max |a| |b| := abs_le_max_abs_abs hs.1 hs.2
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Real.rpow_zero, mul_one]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by rw [abs_mul]; gcongr)

end TauCeti
