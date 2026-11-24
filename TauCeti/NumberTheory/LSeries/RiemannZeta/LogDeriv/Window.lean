/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.ZetaZeros
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Local

/-!
# The window form of the logarithmic derivative of the Riemann zeta function

There is an absolute constant `C` such that for every `s ≠ 1` with `-1 ≤ Re s ≤ 2` and
`ζ(s) ≠ 0`,
`‖ζ′/ζ(s) + 1/(s - 1) - ∑ m(ρ)/(s - ρ)‖ ≤ C log(|Im s| + 2)`,
the sum running over the zeros `ρ` of `ζ` with `0 < Re ρ < 1` and `|Im ρ - Im s| ≤ 1`, weighted
by their analytic order `m(ρ)`.

## Main results

* `TauCeti.exists_finsum_analyticOrderAt_riemannZeta_le`: the zeros of `ζ` in a closed disc of
  fixed radius centred on a vertical line, counted with order, number `O(log(|Im s₀| + 2))`.
* `TauCeti.riemannZeta_logDeriv_window`: the window form of the local expansion of `ζ′/ζ`.

## Implementation notes

The zero count is Jensen's bound `AnalyticOnNhd.sum_divisor_le_log_div_log` for the entire
function `(s - 1) ζ(s)` on a disc centred on the line `Re s = 2`, with the relative growth bound
`TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow_mul`. The window form applies the local
expansion `TauCeti.riemannZeta_local_logDeriv` with centre `s₀ = 2 + i Im s` and radii `3 < 4`.
Every zero of the window lies in the disc of radius `4`. Every other zero of `ζ` is at distance at
least `1` from `s`: zeros with `Re ρ ≤ 0` are the trivial zeros `-2, -4, …`
(`riemannZeta_eq_zero_iff_of_re_nonpos`), there are none with `Re ρ ≥ 1`, and the rest have
`|Im ρ - Im s| > 1`. So the zeros of the disc outside the window contribute at most their count.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 8.6, pp.90–91, and
  Lemma 11.2, p.113.
-/

public section

open Complex DirichletCharacter Metric Set

namespace TauCeti

/-- **Counting zeros of `ζ` in discs.** For real `σ₀` and `r` there is a constant `C` such that
for every centre `s₀` with `Re s₀ = σ₀`, the zeros of `ζ` in the closed disc of radius `r` about
`s₀`, counted with analytic order, number at most `C log(|Im s₀| + 2)`. -/
theorem exists_finsum_analyticOrderAt_riemannZeta_le (σ₀ r : ℝ) :
    ∃ C : ℝ, ∀ s₀ : ℂ, s₀.re = σ₀ →
      ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r ∧ riemannZeta z = 0},
          ((analyticOrderAt riemannZeta ρ.val).toNat : ℝ) ≤
        C * Real.log (|s₀.im| + 2) := by
  classical
  set R := |r| + |σ₀ - 2| + 1
  have hR : 0 < R := by positivity
  obtain ⟨D, hD⟩ := exists_norm_LFunctionTrivChar₁_one_le_rpow_mul one_lt_two (R + 1)
  refine ⟨D / Real.log ((R + 1) / R), fun s₀ hs₀ ↦ ?_⟩
  set c : ℂ := 2 + s₀.im * I
  have hc : c.re = 2 := by simp [c]
  have hcim : c.im = s₀.im := by simp [c]
  have ht : 0 < |s₀.im| + 2 := by positivity
  have hF := (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd isOpen_univ
  have hFc : LFunctionTrivChar₁ 1 c ≠ 0 := by
    have hc1 : c ≠ 1 := fun h ↦ by simp [h] at hc
    rw [LFunctionTrivChar₁_one_apply_of_ne_one hc1]
    exact mul_ne_zero (sub_ne_zero.mpr hc1) (riemannZeta_ne_zero_of_one_lt_re (by simp [hc]))
  have hJ := (hF.mono (subset_univ _)).sum_divisor_le_log_div_log hR (lt_add_one R) hFc
    fun w hw ↦ hD c w hc (by rw [mem_sphere, dist_eq_norm] at hw; exact hw.le)
  rw [Real.log_rpow (by rwa [hcim]), hcim] at hJ
  -- the zeros of `ζ` in the disc of radius `R` about `c`
  set Z := ((isCompact_closedBall c R).inter_riemannZetaZeros_finite).toFinset
  have hZ (z : ℂ) : z ∈ Z ↔ ‖z - c‖ ≤ R ∧ riemannZeta z = 0 := by
    simp [Z, dist_eq_norm, mem_riemannZetaZeros]
  have hsub (z : ℂ) (hz : ‖z - s₀‖ ≤ r) : ‖z - c‖ ≤ R := by
    have hsc : ‖s₀ - c‖ = |σ₀ - 2| := by
      have : s₀ - c = ((σ₀ - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c, hs₀]
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    calc ‖z - c‖ = ‖(z - s₀) + (s₀ - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖z - s₀‖ + ‖s₀ - c‖ := norm_add_le _ _
      _ ≤ R := by rw [hsc]; linarith [le_abs_self r]
  have hdiv : ∑ᶠ ρ, MeromorphicOn.divisor (LFunctionTrivChar₁ 1) (closedBall c R) ρ =
      ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℤ) := by
    refine (finsum_eq_sum_of_support_subset _ fun z hz ↦ ?_).trans
      (Finset.sum_congr rfl fun z hz ↦ ?_)
    · rw [Function.mem_support, divisor_LFunctionTrivChar₁_one_closedBall_apply] at hz
      exact (hZ z).mpr (by_contra fun h ↦ hz (ite_eq_right h))
    · rw [divisor_LFunctionTrivChar₁_one_closedBall_apply, ite_eq_left ((hZ z).mp hz)]
  rw [finsum_subtype_eq_finsum_cond (f := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ)),
    finsum_cond_eq_sum_of_cond_iff (t := Z.filter fun z ↦ ‖z - s₀‖ ≤ r ∧ riemannZeta z = 0) _
      fun {z} _ ↦ by simpa [Finset.mem_filter, hZ] using fun h h' ↦ ⟨hsub z h, h'⟩]
  calc _ ≤ ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity
    _ ≤ D * Real.log (|s₀.im| + 2) / Real.log ((R + 1) / R) := by exact_mod_cast hdiv ▸ hJ
    _ = _ := by ring

/-- A zero `ρ` of `ζ` outside the window `0 < Re ρ < 1`, `|Im ρ - Im s| ≤ 1` is at distance at
least `1` from any `s` with `-1 ≤ Re s`. -/
private theorem one_le_norm_sub_of_riemannZeta_eq_zero {s ρ : ℂ} (hs : -1 ≤ s.re)
    (hρ : riemannZeta ρ = 0) (hw : ¬(0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - s.im| ≤ 1)) :
    1 ≤ ‖s - ρ‖ := by
  rcases le_or_gt ρ.re 0 with h0 | h0
  · obtain ⟨n, rfl⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos h0).mp hρ
    have hre : (s - -2 * ((n : ℂ) + 1)).re = s.re + 2 * (n + 1) := by simp
    refine le_trans ?_ ((le_abs_self _).trans (abs_re_le_norm _))
    rw [hre]
    linarith [n.cast_nonneg (α := ℝ)]
  rcases lt_or_ge ρ.re 1 with h1 | h1
  · have : 1 < |ρ.im - s.im| := by
      by_contra h
      exact hw ⟨h0, h1, not_lt.mp h⟩
    rw [abs_sub_comm] at this
    exact this.le.trans (by simpa using abs_im_le_norm (s - ρ))
  · exact absurd hρ (riemannZeta_ne_zero_of_one_le_re h1)

/-- Over a finite set `Z`, the zeros of `ζ` outside the window about `s` contribute at most their
number, counted with order, to `∑ m(ρ)/(s - ρ)`, when `-1 ≤ Re s`. Points of `Z` that are not
zeros have order `0`. -/
private theorem norm_sum_filter_not_window_le {s : ℂ} (hs : -1 ≤ s.re) (Z : Finset ℂ)
    [DecidablePred fun z : ℂ ↦ 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1] :
    ‖∑ z ∈ Z with ¬(0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1),
        ((analyticOrderAt riemannZeta z).toNat : ℂ) / (s - z)‖ ≤
      ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun z hz ↦ ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity))
  rw [norm_div, Complex.norm_natCast]
  by_cases hζ : riemannZeta z = 0
  · exact div_le_self (by positivity)
      (one_le_norm_sub_of_riemannZeta_eq_zero hs hζ (Finset.mem_filter.mp hz).2)
  · simp [analyticOrderAt_eq_zero.mpr (Or.inr hζ)]

/-- A point `z` with `0 < Re z < 1` and `|Im z - Im s₀| ≤ 1` is within distance `4` of a centre
`s₀` on the line `Re s₀ = 2`. -/
private theorem norm_sub_le_four_of_mem_window {z s₀ : ℂ} (hs₀ : s₀.re = 2) (h0 : 0 < z.re)
    (h1 : z.re < 1) (him : |z.im - s₀.im| ≤ 1) : ‖z - s₀‖ ≤ 4 := by
  have hre : |(z - s₀).re| ≤ 2 := by
    rw [sub_re, hs₀, abs_le]
    constructor <;> linarith
  rw [← sub_im] at him
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply, ← sq, ← sq]
  nlinarith [sq_abs (z - s₀).re, sq_abs (z - s₀).im, abs_nonneg (z - s₀).re,
    abs_nonneg (z - s₀).im]

/-- **The window form of the local expansion of `ζ′/ζ`.** There is a constant `C` such that for
every `s ≠ 1` with `-1 ≤ Re s ≤ 2` and `ζ(s) ≠ 0`, `ζ′/ζ(s) + 1/(s - 1)` differs from
`∑ m(ρ)/(s - ρ)` over the zeros `ρ` of `ζ` with `0 < Re ρ < 1` and `|Im ρ - Im s| ≤ 1`, counted
with analytic order `m(ρ)`, by at most `C log(|Im s| + 2)`. -/
theorem riemannZeta_logDeriv_window :
    ∃ C : ℝ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        C * Real.log (|s.im| + 2) := by
  classical
  obtain ⟨C₁, hC₁⟩ := riemannZeta_local_logDeriv (σ₀ := 2) (r := 3) (r' := 4) one_lt_two
    (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂⟩ := exists_finsum_analyticOrderAt_riemannZeta_le 2 4
  refine ⟨C₁ + C₂, fun s hs₁ hs₂ hs1 hζ ↦ ?_⟩
  set s₀ : ℂ := 2 + s.im * I
  have hs₀ : s₀.re = 2 := by simp [s₀]
  have hs₀im : s₀.im = s.im := by simp [s₀]
  have hss₀ : ‖s - s₀‖ ≤ 3 := by
    have : s - s₀ = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [s₀]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  -- the zeros of `ζ` in the disc of radius `4` about `s₀`
  set Z := ((isCompact_closedBall s₀ 4).inter_riemannZetaZeros_finite).toFinset
  have hZ (z : ℂ) : z ∈ Z ↔ ‖z - s₀‖ ≤ 4 ∧ riemannZeta z = 0 := by
    simp [Z, dist_eq_norm, mem_riemannZetaZeros]
  set W : ℂ → Prop := fun z ↦ 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1
  have hWZ (z : ℂ) (hz : W z) (hζz : riemannZeta z = 0) : z ∈ Z :=
    (hZ z).mpr ⟨norm_sub_le_four_of_mem_window hs₀ hz.1 hz.2.1 (hs₀im ▸ hz.2.2), hζz⟩
  set f : ℂ → ℂ := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℂ) / (s - z)
  have hdisc : ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ 4 ∧ riemannZeta z = 0}, f ρ = ∑ z ∈ Z, f z := by
    rw [finsum_subtype_eq_finsum_cond (f := f)]
    exact finsum_cond_eq_sum_of_cond_iff _ fun {z} _ ↦ (hZ z).symm
  have hwin : ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
      f ρ = ∑ z ∈ Z with W z, f z := by
    rw [finsum_subtype_eq_finsum_cond (f := f)]
    refine finsum_cond_eq_sum_of_cond_iff _ fun {z} _ ↦ ?_
    simp only [Finset.mem_filter, W]
    exact ⟨fun h ↦ ⟨hWZ z ⟨h.1, h.2.1, h.2.2.1⟩ h.2.2.2, h.1, h.2.1, h.2.2.1⟩,
      fun h ↦ ⟨h.2.1, h.2.2.1, h.2.2.2, ((hZ z).mp h.1).2⟩⟩
  -- the zeros of the disc outside the window contribute at most their count
  have hrest : ‖∑ z ∈ Z with ¬W z, f z‖ ≤ C₂ * Real.log (|s.im| + 2) := by
    have hcount := hC₂ s₀ hs₀
    rw [hs₀im, finsum_subtype_eq_finsum_cond
      (f := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ)),
      finsum_cond_eq_sum_of_cond_iff _ fun {z} _ ↦ (hZ z).symm] at hcount
    exact (norm_sum_filter_not_window_le hs₁ Z).trans hcount
  have hsplit := Finset.sum_filter_add_sum_filter_not Z W f
  have hloc := hC₁ s₀ s hs₀ hss₀ hs1 hζ
  rw [hs₀im] at hloc
  rw [hwin]
  rw [hdisc, ← hsplit] at hloc
  calc _ = ‖(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ((∑ z ∈ Z with W z, f z) + ∑ z ∈ Z with ¬W z, f z)) + ∑ z ∈ Z with ¬W z, f z‖ := by
        rw [sub_add_eq_sub_sub, sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ C₁ * Real.log (|s.im| + 2) + C₂ * Real.log (|s.im| + 2) := add_le_add hloc hrest
    _ = _ := by ring

end TauCeti
