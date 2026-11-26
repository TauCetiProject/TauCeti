/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.NearestPointOnVerticalLine

/-!
# Analytic expansion discs for meromorphic functions

A meromorphic function in normal form on a right half-plane that has a pole, but none on or to
the right of a vertical line, admits one of two configurations of Taylor discs centred on that
line. Either a vertically shifted disc isolates a pole and the real-centred disc of equal radius
is analytic, or the real-centred disc isolates a real pole of maximal real part. Normal form
ensures that pole-free regions have no removable singularities.

This is the analytic form of the disc selection used in Levent Alpöge's windowed Landau theorem
(`Deduction.landau_window`). It uses the discrete-set dichotomy
`TauCeti.exists_ball_inter_eq_singleton_or_exists_real_ball_inter_eq_singleton`.
-/

public section

open Complex Filter Metric Set

/-- Let `f` be in meromorphic normal form on the half-plane `θ < re z`. Suppose it has a pole
in that half-plane and all such poles lie to the left of `re z = σ`. Then either:

* a disc centred at `σ + γ * I` isolates a pole `ρ` distinct from its centre, and `f` is analytic
  on the punctured disc and on the equal-radius disc about `σ`; or
* a disc centred at `σ` isolates a real pole `β > θ` of maximal real part, and `f` is analytic
  on that disc punctured at `β`.

The radius is at most `σ - θ` in both cases. The two punctured discs exclude the pole, not the
expansion centre. For an arbitrary meromorphic function, apply this to `toMeromorphicNFOn`;
`meromorphicOrderAt_toMeromorphicNFOn` identifies its poles with those of the original function
in the half-plane. -/
theorem MeromorphicNFOn.exists_analytic_discs_or_rightmost_real_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {θ σ : ℝ} (hf : MeromorphicNFOn f {z | θ < z.re})
    (hσ : ∀ z : ℂ, θ < z.re → meromorphicOrderAt f z < 0 → z.re < σ)
    (hθ : ∃ z : ℂ, θ < z.re ∧ meromorphicOrderAt f z < 0) :
    (∃ (γ : ℝ) (ρ : ℂ) (r : ℝ),
      0 < dist ((σ : ℂ) + γ * I) ρ ∧ dist ((σ : ℂ) + γ * I) ρ < r ∧ r ≤ σ - θ ∧
      meromorphicOrderAt f ρ < 0 ∧
      AnalyticOnNhd ℂ f (ball ((σ : ℂ) + γ * I) r \ {ρ}) ∧ AnalyticOnNhd ℂ f (ball (σ : ℂ) r)) ∨
    ∃ (β r : ℝ), θ < β ∧ 0 < σ - β ∧ σ - β < r ∧ r ≤ σ - θ ∧
      meromorphicOrderAt f (β : ℂ) < 0 ∧ (∀ z : ℂ, meromorphicOrderAt f z < 0 → z.re ≤ β) ∧
      AnalyticOnNhd ℂ f (ball (σ : ℂ) r \ {(β : ℂ)}) := by
  let Z : Set ℂ := {z | θ < z.re ∧ meromorphicOrderAt f z < 0}
  have hZ : Zᶜ ∈ codiscreteWithin {z | θ < z.re} :=
    mem_of_superset hf.meromorphicOn.analyticAt_mem_codiscreteWithin fun z hz hp ↦
      hz.meromorphicOrderAt_nonneg.not_gt hp.2
  have han {c : ℂ} {r : ℝ} (hc : c.re = σ) (hr : r ≤ σ - θ) {z : ℂ} (hz : z ∈ ball c r)
      (hn : z ∉ Z) : AnalyticAt ℂ f z := by
    have hθz : θ < z.re :=
      ball_subset_setOfPred_lt_re (by rw [hc]; linarith only [hr]) hz
    exact (hf hθz).meromorphicOrderAt_nonneg_iff_analyticAt.1 <|
      le_of_not_gt fun h ↦ hn ⟨hθz, h⟩
  have hρ : ∃ z ∈ Z, θ < z.re := by
    obtain ⟨z, hz, hpole⟩ := hθ
    exact ⟨z, ⟨hz, hpole⟩, hz⟩
  rcases TauCeti.exists_ball_inter_eq_singleton_or_exists_real_ball_inter_eq_singleton hZ
      (fun z hz ↦ hσ z hz.1 hz.2) hρ with
    ⟨γ, ρ, hρZ, r, hd, hdr, hr, hball, hempty⟩ | ⟨β, hβZ, hβ, hmax, r, hd, hr, hball⟩
  · have hshift : ((σ : ℂ) + γ * I).re = σ := by simp
    refine Or.inl ⟨γ, ρ, r, hd, hdr, hr, hρZ.2, ?_, ?_⟩
    · exact fun z hz ↦ han hshift hr hz.1 fun h ↦ hz.2 (hball ▸ ⟨hz.1, h⟩)
    · exact fun z hz ↦ han (ofReal_re σ) hr hz fun h ↦ notMem_empty z (hempty ▸ ⟨hz, h⟩)
  · have hβσ : β < σ := by simpa using hσ (β : ℂ) hβZ.1 hβZ.2
    refine Or.inr ⟨β, r, hβ, sub_pos.mpr hβσ, hd, hr, hβZ.2, ?_, ?_⟩
    · intro z hz
      by_cases hzθ : θ < z.re
      · exact hmax z ⟨hzθ, hz⟩
      · exact (le_of_not_gt hzθ).trans hβ.le
    · exact fun z hz ↦ han (ofReal_re σ) hr hz.1 fun h ↦ hz.2 (hball ▸ ⟨hz.1, h⟩)
