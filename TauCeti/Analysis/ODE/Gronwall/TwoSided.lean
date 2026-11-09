/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.ODE.Gronwall

/-!
# Grönwall bounds in both time directions

Mathlib's `gronwallBound` controls a curve forward from the left endpoint. Here the initial
point may be anywhere in a closed interval: an affine time change gives the exact same bound
with elapsed time `|t - t₀|`. The derivative may be taken within the closed interval, so no
extension beyond its endpoints is required. There are no completeness or sign assumptions.

## Main results

* `TauCeti.norm_le_gronwallBound_of_norm_derivWithin_le`: a norm bound from any reference time.
* `TauCeti.norm_sub_le_gronwallBound_of_linearODE`: comparison of two linear trajectories.
* `TauCeti.gronwallBound_zero_le_mul_exp`: an explicit zero-initial-value estimate.

Formalization references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Set Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A derivative norm bound on `[a,b]` controls the curve from any initial point
`t₀ ∈ [a,b]` in both time directions. No sign assumptions on the three constants
are needed for the exact Grönwall bound. -/
theorem norm_le_gronwallBound_of_norm_derivWithin_le
    {f f' : ℝ → E} {a b t₀ δ K ε : ℝ}
    (ht₀ : t₀ ∈ Icc a b)
    (hf' : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hinit : ‖f t₀‖ ≤ δ)
    (hbound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ gronwallBound δ K ε |t - t₀| := by
  intro t ht
  let r := |t - t₀|
  obtain ⟨σ, hσ, hend, hmap⟩ : ∃ σ : ℝ, |σ| = 1 ∧ t₀ + σ * r = t ∧
      MapsTo (fun s ↦ t₀ + σ * s) (Icc 0 r) (Icc a b) := by
    rcases le_total t₀ t with h | h
    · refine ⟨1, by norm_num, ?_, ?_⟩
      · dsimp [r]; rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
      · intro s hs
        dsimp [r] at hs
        rw [abs_of_nonneg (sub_nonneg.mpr h)] at hs
        constructor <;> dsimp <;> linarith [ht₀.1, ht.2, hs.1, hs.2]
    · refine ⟨-1, by norm_num, ?_, ?_⟩
      · dsimp [r]; rw [abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · intro s hs
        dsimp [r] at hs
        rw [abs_of_nonpos (sub_nonpos.mpr h)] at hs
        constructor <;> dsimp <;> linarith [ht.1, ht₀.2, hs.1, hs.2]
  let φ : ℝ → ℝ := fun s ↦ t₀ + σ * s
  have hφ : ∀ s, HasDerivAt φ σ s := fun s ↦ by
    simpa [φ] using ((hasDerivAt_id s).const_mul σ).const_add t₀
  have hd : ∀ s ∈ Icc 0 r,
      HasDerivWithinAt (f ∘ φ) (σ • f' (φ s)) (Icc 0 r) s :=
    fun s hs ↦ (hf' (φ s) (hmap hs)).scomp s (hφ s).hasDerivWithinAt hmap
  have hr : ∀ s ∈ Ico 0 r,
      HasDerivWithinAt (f ∘ φ) (σ • f' (φ s)) (Ici s) s := by
    intro s hs
    exact (hd s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
  have hb : ∀ s ∈ Ico 0 r, ‖σ • f' (φ s)‖ ≤ K * ‖(f ∘ φ) s‖ + ε := by
    intro s hs
    simpa only [norm_smul, Real.norm_eq_abs, hσ, one_mul, Function.comp_apply] using
      hbound (φ s) (hmap ⟨hs.1, hs.2.le⟩)
  have hi : ‖(f ∘ φ) 0‖ ≤ δ := by simpa [φ] using hinit
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun s hs ↦ (hd s hs).continuousWithinAt) hr hi hb r ⟨abs_nonneg _, le_rfl⟩
  simpa only [Function.comp_apply, φ, hend, sub_zero] using hg

/-- Two actual linear trajectories on `[a,b]` satisfy a two-sided Grönwall
comparison from any initial time `t₀` in that interval. The operator bound is on
`A₁`, and the forcing error is `(A₂ - A₁) Z₂`. No completeness or sign hypotheses
are needed for this exact bound. -/
theorem norm_sub_le_gronwallBound_of_linearODE
    {A₁ A₂ : ℝ → E →L[ℝ] E} {Z₁ Z₂ : ℝ → E} {a b t₀ K η : ℝ}
    (ht₀ : t₀ ∈ Icc a b)
    (hZ₁ : ∀ s ∈ Icc a b, HasDerivWithinAt Z₁ (A₁ s (Z₁ s)) (Icc a b) s)
    (hZ₂ : ∀ s ∈ Icc a b, HasDerivWithinAt Z₂ (A₂ s (Z₂ s)) (Icc a b) s)
    (hA₁ : ∀ s ∈ Icc a b, ‖A₁ s‖ ≤ K)
    (hdiff : ∀ s ∈ Icc a b, ‖(A₂ s - A₁ s) (Z₂ s)‖ ≤ η) :
    ∀ t ∈ Icc a b, ‖Z₁ t - Z₂ t‖ ≤ gronwallBound ‖Z₁ t₀ - Z₂ t₀‖ K η |t - t₀| := by
  apply norm_le_gronwallBound_of_norm_derivWithin_le ht₀
    (fun s hs ↦ (hZ₁ s hs).sub (hZ₂ s hs)) (le_refl _)
  intro s hs
  have heq : A₁ s (Z₁ s) - A₂ s (Z₂ s) =
      A₁ s (Z₁ s - Z₂ s) - (A₂ s - A₁ s) (Z₂ s) := by
    simp only [map_sub, sub_apply]
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add
    (((A₁ s).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hA₁ s hs) (norm_nonneg _))) (hdiff s hs))

/-- For nonnegative growth rate and error, the zero-initial-value Grönwall bound
is at most `ε * x * exp (K*x)`. This also includes growth rate zero. -/
lemma gronwallBound_zero_le_mul_exp {K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound 0 K ε x ≤ ε * x * exp (K * x) := by
  rcases eq_or_lt_of_le hK with h | h
  · subst K
    simp [gronwallBound_K0]
  · have he := mul_le_mul_of_nonneg_right (one_sub_le_exp_neg (K * x))
      (exp_pos (K * x)).le
    rw [← exp_add, neg_add_cancel, exp_zero] at he
    have he' : exp (K * x) - 1 ≤ (K * x) * exp (K * x) := by nlinarith
    rw [gronwallBound_of_K_ne_0 (ne_of_gt h)]
    simp only [zero_mul, zero_add]
    calc
      ε / K * (exp (K * x) - 1) ≤ ε / K * ((K * x) * exp (K * x)) :=
        mul_le_mul_of_nonneg_left he' (div_nonneg hε h.le)
      _ = ε * x * exp (K * x) := by field_simp

end TauCeti
