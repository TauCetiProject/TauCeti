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
import TauCeti.Analysis.SpecialFunctions.Log.TwoAdd
import TauCeti.Data.Real.Pigeonhole
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Local
import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic

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
* `TauCeti.riemannZetaZerosClosedBall`: the zeros of `ζ` in a closed disc, as a `Finset`, and
  `TauCeti.finsum_window_eq_sum_filter`, which turns a sum over the zeros of a window into a
  `Finset` sum over any finite set containing them, such as the disc of radius `4` about
  `2 + i t` (`TauCeti.finsum_window_eq_sum_riemannZetaZerosClosedBall`).
* `TauCeti.riemannZeta_logDeriv_window`: the window form of the local expansion of `ζ′/ζ`.
* `TauCeti.riemannZeta_safe_height`: every `[T, T + 1]` with `T ≥ 2` contains a height `T′` with
  `ζ(σ ± i T′) ≠ 0` and `‖ζ′/ζ(σ ± i T′)‖ ≤ C log² (T + 2)` for `-1 ≤ σ ≤ 2`.

## Implementation notes

The zero count is Jensen's bound
`AnalyticOnNhd.sum_divisor_le_log_div_log_of_closedBall_subset` for the entire function
`(s - 1) ζ(s)` on a disc centred on the line `Re s = 2`, with the relative growth bound
`TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow_mul`. The window form applies the local
expansion `TauCeti.riemannZeta_local_logDeriv` with centre `s₀ = 2 + i Im s` and radii `3 < 4`.
Every zero of the window lies in the disc of radius `4`. Every other zero of `ζ` is at distance at
least `1` from `s`: zeros with `Re ρ ≤ 0` are the trivial zeros `-2, -4, …`
(`riemannZeta_eq_zero_iff_of_re_nonpos`), there are none with `Re ρ ≥ 1`, and the rest have
`|Im ρ - Im s| > 1`. So the zeros of the disc outside the window contribute at most their count.

For the safe height, the zeros of the windows about the points `σ ± i T′` with `T ≤ T′ ≤ T + 1`
lie in the two discs of radius `4` about `2 ± i T`. They number `K = O(log (T + 2))` with order,
so their ordinates take at most `K` absolute values, and the pigeonhole lemma
`TauCeti.exists_mem_Icc_forall_le_abs_sub` gives `T′ ∈ [T, T + 1]` at distance at least
`1 / (2 (K + 1))` from all of them. At such a height `ζ` has no zero on the horizontal segments,
and the window sum is at most `2 K (K + 1) = O(log² (T + 2))`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 8.6, pp.90–91,
  Lemma 11.2, p.113, and Lemma 11.4, pp.114–115.
-/

public section

open Complex DirichletCharacter Metric Set

namespace TauCeti

/-- The zeros of `ζ` in the closed disc of radius `R` about `c`, as a finite set. -/
noncomputable def riemannZetaZerosClosedBall (c : ℂ) (R : ℝ) : Finset ℂ :=
  ((isCompact_closedBall c R).inter_riemannZetaZeros_finite).toFinset

/-- Membership in `riemannZetaZerosClosedBall c R`: `z` is a zero of `ζ` with `‖z - c‖ ≤ R`. -/
@[simp]
theorem mem_riemannZetaZerosClosedBall {c z : ℂ} {R : ℝ} :
    z ∈ riemannZetaZerosClosedBall c R ↔ ‖z - c‖ ≤ R ∧ riemannZeta z = 0 := by
  simp [riemannZetaZerosClosedBall, dist_eq_norm, mem_riemannZetaZeros]

/-- A sum over the zeros of `ζ` in a closed disc, as a `finsum` over a subtype, is the `Finset`
sum over `riemannZetaZerosClosedBall`. -/
private theorem finsum_subtype_riemannZeta_eq_sum {M : Type*} [AddCommMonoid M] (c : ℂ) (R : ℝ)
    (f : ℂ → M) :
    ∑ᶠ ρ : {z : ℂ // ‖z - c‖ ≤ R ∧ riemannZeta z = 0}, f ρ =
      ∑ z ∈ riemannZetaZerosClosedBall c R, f z := by
  rw [finsum_subtype_eq_finsum_cond (f := f)]
  exact finsum_cond_eq_sum_of_cond_iff _ fun {z} _ ↦ mem_riemannZetaZerosClosedBall.symm

/-- The distance from `s` to the point `2 + i Im s` of the line `Re = 2` is `|Re s - 2|`. -/
private theorem norm_sub_two_add_im_mul_I (s : ℂ) : ‖s - (2 + s.im * I)‖ = |s.re - 2| := by
  have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp
  rw [this, Complex.norm_real, Real.norm_eq_abs]

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
  set c : ℂ := 2 + s₀.im * I with hcdef
  have hc : c.re = 2 := by simp [c]
  have hcim : c.im = s₀.im := by simp [c]
  have ht : 0 < |s₀.im| + 2 := by positivity
  have hF := (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd isOpen_univ
  have hFc : LFunctionTrivChar₁ 1 c ≠ 0 :=
    LFunctionTrivChar₁_one_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by simp [hc]))
  have hsub : closedBall s₀ r ⊆ closedBall c R := closedBall_subset_closedBall' <| by
    rw [dist_eq_norm, hcdef, norm_sub_two_add_im_mul_I, hs₀]
    linarith [le_abs_self r]
  have hJ := (hF.mono (subset_univ _)).sum_divisor_le_log_div_log_of_closedBall_subset hR
    (lt_add_one R) hFc (fun w hw ↦ hD c w hc (by rw [mem_sphere, dist_eq_norm] at hw; exact hw.le))
    hsub
  rw [Real.log_rpow (by rwa [hcim]), hcim] at hJ
  have hdiv : ∑ᶠ ρ, MeromorphicOn.divisor (LFunctionTrivChar₁ 1) (closedBall s₀ r) ρ =
      ∑ z ∈ riemannZetaZerosClosedBall s₀ r, ((analyticOrderAt riemannZeta z).toNat : ℤ) := by
    refine (finsum_eq_sum_of_support_subset _ fun z hz ↦ ?_).trans
      (Finset.sum_congr rfl fun z hz ↦ ?_)
    · rw [Function.mem_support, divisor_LFunctionTrivChar₁_one_closedBall_apply] at hz
      exact mem_riemannZetaZerosClosedBall.mpr (by_contra fun h ↦ hz (ite_eq_right h))
    · rw [divisor_LFunctionTrivChar₁_one_closedBall_apply,
        ite_eq_left (mem_riemannZetaZerosClosedBall.mp hz)]
  rw [finsum_subtype_riemannZeta_eq_sum s₀ r fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ)]
  calc _ ≤ D * Real.log (|s₀.im| + 2) / Real.log ((R + 1) / R) := by exact_mod_cast hdiv ▸ hJ
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

/-- A zero `ρ` of `ζ` with `|Re ρ - 2| ≤ 2` and `|Im ρ - t| ≤ 2` lies in the closed disc of
radius `4` about `2 + i t`. -/
theorem mem_riemannZetaZerosClosedBall_two_add {ρ : ℂ} {t : ℝ} (hre : |ρ.re - 2| ≤ 2)
    (him : |ρ.im - t| ≤ 2) (hζ : riemannZeta ρ = 0) :
    ρ ∈ riemannZetaZerosClosedBall (2 + t * I) 4 := by
  refine mem_riemannZetaZerosClosedBall.mpr ⟨(Complex.norm_le_abs_re_add_abs_im _).trans ?_, hζ⟩
  have h1 : (ρ - (2 + t * I)).re = ρ.re - 2 := by simp
  have h2 : (ρ - (2 + t * I)).im = ρ.im - t := by simp
  rw [h1, h2]
  linarith

/-- If a finite set `Z` contains the zeros of the window `0 < Re z < 1`, `|Im z - t| ≤ 1` at
height `t`, a sum over these zeros, as a `finsum` over a subtype, is the `Finset` sum over the
window zeros in `Z`. For `Z` one can take `riemannZetaZerosClosedBall (2 + t * I) 4`, by
`mem_riemannZetaZerosClosedBall_two_add`. -/
theorem finsum_window_eq_sum_filter {M : Type*} [AddCommMonoid M] {t : ℝ} {Z : Finset ℂ}
    (hZ : ∀ z : ℂ, 0 < z.re → z.re < 1 → |z.im - t| ≤ 1 → riemannZeta z = 0 → z ∈ Z)
    (f : ℂ → M)
    [DecidablePred fun z : ℂ ↦ 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0] :
    ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0}, f ρ =
      ∑ z ∈ Z with 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0, f z := by
  rw [finsum_subtype_eq_finsum_cond (f := f)]
  refine finsum_cond_eq_sum_of_cond_iff _ fun {z} _ ↦ ?_
  rw [Finset.mem_filter]
  exact ⟨fun h ↦ ⟨hZ z h.1 h.2.1 h.2.2.1 h.2.2.2, h⟩, fun h ↦ h.2⟩

/-- A sum over the zeros of the window at height `t`, as a `finsum` over a subtype, is the
`Finset` sum over the window zeros in the disc of radius `4` about `2 + i t`. -/
theorem finsum_window_eq_sum_riemannZetaZerosClosedBall {M : Type*} [AddCommMonoid M] (t : ℝ)
    (f : ℂ → M)
    [DecidablePred fun z : ℂ ↦ 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0] :
    ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0}, f ρ =
      ∑ z ∈ riemannZetaZerosClosedBall (2 + t * I) 4 with
        0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0, f z :=
  finsum_window_eq_sum_filter (fun _ h0 h1 him hζ ↦ mem_riemannZetaZerosClosedBall_two_add
    (abs_le.mpr ⟨by linarith, by linarith⟩) (him.trans (by norm_num)) hζ) f

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
    (by norm_num)
  obtain ⟨C₂, hC₂⟩ := exists_finsum_analyticOrderAt_riemannZeta_le 2 4
  refine ⟨C₁ + C₂, fun s hs₁ hs₂ hs1 hζ ↦ ?_⟩
  set s₀ : ℂ := 2 + s.im * I with hs₀def
  have hs₀ : s₀.re = 2 := by simp [s₀]
  have hs₀im : s₀.im = s.im := by simp [s₀]
  have hss₀ : ‖s - s₀‖ ≤ 3 := by
    rw [hs₀def, norm_sub_two_add_im_mul_I, abs_le]
    constructor <;> linarith
  -- the zeros of `ζ` in the disc of radius `4` about `s₀`
  set Z := riemannZetaZerosClosedBall s₀ 4
  set W : ℂ → Prop := fun z ↦ 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1
  set f : ℂ → ℂ := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℂ) / (s - z)
  have hwin : ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
      f ρ = ∑ z ∈ Z with W z, f z := by
    rw [finsum_window_eq_sum_riemannZetaZerosClosedBall s.im f]
    refine Finset.sum_congr (Finset.filter_congr fun z hz ↦ ?_) fun _ _ ↦ rfl
    exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1⟩,
      fun h ↦ ⟨h.1, h.2.1, h.2.2, (mem_riemannZetaZerosClosedBall.mp hz).2⟩⟩
  -- the zeros of the disc outside the window contribute at most their count
  have hrest : ‖∑ z ∈ Z with ¬W z, f z‖ ≤ C₂ * Real.log (|s.im| + 2) := by
    have hcount := hC₂ s₀ hs₀
    rw [hs₀im, finsum_subtype_riemannZeta_eq_sum s₀ 4
      fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ)] at hcount
    exact (norm_sum_filter_not_window_le hs₁ Z).trans hcount
  have hsplit := Finset.sum_filter_add_sum_filter_not Z W f
  have hloc := hC₁ s₀ s hs₀ hss₀ hs1 hζ
  rw [hs₀im] at hloc
  rw [hwin]
  rw [finsum_subtype_riemannZeta_eq_sum s₀ 4 f, ← hsplit] at hloc
  calc _ = ‖(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ((∑ z ∈ Z with W z, f z) + ∑ z ∈ Z with ¬W z, f z)) + ∑ z ∈ Z with ¬W z, f z‖ := by
        rw [sub_add_eq_sub_sub, sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ C₁ * Real.log (|s.im| + 2) + C₂ * Real.log (|s.im| + 2) := add_le_add hloc hrest
    _ = _ := by ring

/-- A zero `ρ` of `ζ` in the window `0 < Re ρ < 1`, `|Im ρ - Im s| ≤ 1` about a point `s` with
`T ≤ |Im s| ≤ T + 1` lies in the closed disc of radius `4` about `2 + i T` or about `2 - i T`. -/
private theorem mem_union_riemannZetaZerosClosedBall_of_window {T : ℝ} {s ρ : ℂ}
    (hT : T ≤ |s.im|) (hT' : |s.im| ≤ T + 1) (hρ : 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - s.im| ≤ 1)
    (hζ : riemannZeta ρ = 0) :
    ρ ∈ riemannZetaZerosClosedBall (2 + T * I) 4 ∪
      riemannZetaZerosClosedBall (2 + ((-T : ℝ) : ℂ) * I) 4 := by
  have hre : |ρ.re - 2| ≤ 2 := abs_le.mpr ⟨by linarith [hρ.1], by linarith [hρ.2.1]⟩
  -- `||Im ρ| - T| ≤ ||Im ρ| - |Im s|| + 1 ≤ |Im ρ - Im s| + 1 ≤ 2`
  have him : |(|ρ.im| - T)| ≤ 2 := by
    have := (abs_abs_sub_abs_le_abs_sub ρ.im s.im).trans hρ.2.2
    rw [abs_le] at this ⊢
    constructor <;> linarith
  rw [Finset.mem_union]
  rcases le_or_gt 0 ρ.im with h | h
  · rw [abs_of_nonneg h] at him
    exact Or.inl (mem_riemannZetaZerosClosedBall_two_add hre him hζ)
  · have hneg : ρ.im - -T = -(|ρ.im| - T) := by
      rw [abs_of_neg h]
      ring
    exact Or.inr (mem_riemannZetaZerosClosedBall_two_add hre (by rwa [hneg, abs_neg]) hζ)

/-- If a finite set `Z` contains the zeros of the window about `s` and every point of `Z` is at
distance at least `δ > 0` from `s`, the window sum `∑ m(ρ)/(s - ρ)` has norm at most
`∑_{z ∈ Z} m(z) / δ`. -/
private theorem norm_finsum_window_le {s : ℂ} {Z : Finset ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hZ : ∀ z : ℂ, 0 < z.re → z.re < 1 → |z.im - s.im| ≤ 1 → riemannZeta z = 0 → z ∈ Z)
    (hsep : ∀ z ∈ Z, δ ≤ ‖s - z‖) :
    ‖∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
        ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
      (∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ)) / δ := by
  classical
  rw [finsum_window_eq_sum_filter hZ
    fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℂ) / (s - z), Finset.sum_div]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun z hz ↦ ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity))
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (by positivity) hδ (hsep z (Finset.mem_filter.mp hz).1)

/-- **The estimate at a separated point.** Let `C` be a constant of the window form
`TauCeti.riemannZeta_logDeriv_window`. If `-1 ≤ Re s ≤ 2`, `|Im s| ≥ 2`, a finite set `Z`
contains the zeros of the window about `s`, and every point of `Z` is at distance at least
`δ > 0` from `s`, then `ζ(s) ≠ 0` and
`‖ζ′/ζ(s)‖ ≤ C log(|Im s| + 2) + ∑_{z ∈ Z} m(z) / δ + 1`. -/
private theorem riemannZeta_ne_zero_and_norm_logDeriv_le {C : ℝ}
    (hC : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        C * Real.log (|s.im| + 2))
    {s : ℂ} {Z : Finset ℂ} {δ : ℝ} (hδ : 0 < δ) (hs₁ : -1 ≤ s.re) (hs₂ : s.re ≤ 2)
    (hsim : 2 ≤ |s.im|)
    (hZ : ∀ z : ℂ, 0 < z.re → z.re < 1 → |z.im - s.im| ≤ 1 → riemannZeta z = 0 → z ∈ Z)
    (hsep : ∀ z ∈ Z, δ ≤ ‖s - z‖) :
    riemannZeta s ≠ 0 ∧ ‖deriv riemannZeta s / riemannZeta s‖ ≤
      C * Real.log (|s.im| + 2) +
        (∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ)) / δ + 1 := by
  -- a zero at `s` would lie in `Z`, or outside the window at distance `≥ 1` from itself
  have hζ : riemannZeta s ≠ 0 := fun hζ ↦ by
    by_cases hw : 0 < s.re ∧ s.re < 1 ∧ |s.im - s.im| ≤ 1
    · have := hsep s (hZ s hw.1 hw.2.1 hw.2.2 hζ)
      rw [sub_self, norm_zero] at this
      linarith
    · have := one_le_norm_sub_of_riemannZeta_eq_zero hs₁ hζ hw
      rw [sub_self, norm_zero] at this
      linarith
  refine ⟨hζ, ?_⟩
  have hs1 : 2 ≤ ‖s - 1‖ := hsim.trans (by simpa using abs_im_le_norm (s - 1))
  have hpole : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]
    linarith
  have hs1' : s ≠ 1 := fun h ↦ by norm_num [h] at hs1
  set W := ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
    ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)
  have hsplit : deriv riemannZeta s / riemannZeta s =
      (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - W) + W - 1 / (s - 1) := by ring
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    (hC s hs₁ hs₂ hs1' hζ) (norm_finsum_window_le hδ hZ hsep))) hpole)

/-- If `C` bounds the zero count of `exists_finsum_analyticOrderAt_riemannZeta_le` for centres on
the line `Re s₀ = 2` and radius `4`, then the zeros of `ζ` in the discs of radius `4` about
`2 ± i T`, counted with order, number at most `2 |C| log (|T| + 2)`. -/
private theorem sum_toNat_analyticOrderAt_union_le {C : ℝ}
    (hC : ∀ s₀ : ℂ, s₀.re = 2 →
      ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ 4 ∧ riemannZeta z = 0},
          ((analyticOrderAt riemannZeta ρ.val).toNat : ℝ) ≤ C * Real.log (|s₀.im| + 2))
    (T : ℝ) :
    ∑ z ∈ riemannZetaZerosClosedBall (2 + T * I) 4 ∪
        riemannZetaZerosClosedBall (2 + ((-T : ℝ) : ℂ) * I) 4,
        ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ 2 * |C| * Real.log (|T| + 2) := by
  classical
  have hdisc (t : ℝ) : ∑ z ∈ riemannZetaZerosClosedBall (2 + t * I) 4,
      ((analyticOrderAt riemannZeta z).toNat : ℝ) ≤ |C| * Real.log (|t| + 2) := by
    have him : (2 + t * I).im = t := by simp
    have := hC (2 + t * I) (by simp)
    rw [finsum_subtype_riemannZeta_eq_sum _ 4
      fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ), him] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (Real.log_nonneg (by linarith [abs_nonneg t])))
  have h := Finset.sum_union_inter (s₁ := riemannZetaZerosClosedBall (2 + T * I) 4)
    (s₂ := riemannZetaZerosClosedBall (2 + ((-T : ℝ) : ℂ) * I) 4)
    (f := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ))
  have h0 : 0 ≤ ∑ z ∈ riemannZetaZerosClosedBall (2 + T * I) 4 ∩
      riemannZetaZerosClosedBall (2 + ((-T : ℝ) : ℂ) * I) 4,
      ((analyticOrderAt riemannZeta z).toNat : ℝ) := by positivity
  have h1 := hdisc T
  have h2 := hdisc (-T)
  rw [abs_neg] at h2
  linarith

/-- Every point of a finite set `Z` of zeros of `ζ` has order at least `1`, so the set of the
absolute values of their ordinates has at most `∑_{z ∈ Z} m(z)` elements. -/
private theorem card_image_abs_im_le_sum {Z : Finset ℂ} (hZ : ∀ z ∈ Z, riemannZeta z = 0) :
    ((Z.image fun z ↦ |z.im|).card : ℝ) ≤ ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
  refine (Nat.cast_le.2 Finset.card_image_le).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact Finset.sum_le_sum fun z hz ↦ by
    exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta (hZ z hz)

/-- The final arithmetic: if `1 ≤ L`, `0 ≤ l ≤ 2 L` and `0 ≤ K ≤ 2 |C'| L`, then
`C l + 2 K (K + 1) + 1 ≤ (2 |C| + 8 C'² + 4 |C'| + 1) L²`. -/
private theorem mul_add_two_mul_mul_add_one_le {C C' K L l : ℝ} (hL : 1 ≤ L) (hl : 0 ≤ l)
    (hlL : l ≤ 2 * L) (hK0 : 0 ≤ K) (hK : K ≤ 2 * |C'| * L) :
    C * l + 2 * K * (K + 1) + 1 ≤ (2 * |C| + 8 * C' ^ 2 + 4 * |C'| + 1) * L ^ 2 := by
  have hC : C * l ≤ |C| * (2 * L) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hl).trans
      (mul_le_mul_of_nonneg_left hlL (abs_nonneg C))
  have hL2 : L ≤ L ^ 2 := by nlinarith
  nlinarith [abs_nonneg C', abs_nonneg C, sq_abs C',
    mul_le_mul hK hK hK0 (by nlinarith [abs_nonneg C']),
    mul_le_mul_of_nonneg_left hL2 (abs_nonneg C), mul_le_mul_of_nonneg_left hL2 (abs_nonneg C')]

/-- **A safe height for `ζ′/ζ`.** There is a constant `C` such that every `T ≥ 2` has some
`T′ ∈ [T, T + 1]` with `ζ(σ ± i T′) ≠ 0` and `‖ζ′/ζ(σ ± i T′)‖ ≤ C log² (T + 2)` for every
`σ ∈ [-1, 2]`. -/
theorem riemannZeta_safe_height :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∃ T' ∈ Set.Icc T (T + 1), ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ∀ s ∈ ({(σ : ℂ) + (T' : ℂ) * I, (σ : ℂ) - (T' : ℂ) * I} : Set ℂ),
        riemannZeta s ≠ 0 ∧
          ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log (T + 2) ^ 2 := by
  classical
  obtain ⟨Cw, hCw⟩ := riemannZeta_logDeriv_window
  obtain ⟨Cc, hCc⟩ := exists_finsum_analyticOrderAt_riemannZeta_le 2 4
  refine ⟨2 * |Cw| + 8 * Cc ^ 2 + 4 * |Cc| + 1, fun T hT ↦ ?_⟩
  -- the zeros of `ζ` in the discs of radius `4` about `2 ± i T`; their ordinates are avoided
  set Z := riemannZetaZerosClosedBall (2 + T * I) 4 ∪
    riemannZetaZerosClosedBall (2 + ((-T : ℝ) : ℂ) * I) 4
  set K := ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hcard := card_image_abs_im_le_sum (Z := Z) fun z hz ↦ by
    rcases Finset.mem_union.1 hz with hz | hz <;> exact (mem_riemannZetaZerosClosedBall.1 hz).2
  obtain ⟨T', hT', hsepT'⟩ := exists_mem_Icc_forall_le_abs_sub (Z.image fun z ↦ |z.im|)
    (by linarith : T ≤ T + 1)
  have hδ : 1 / (2 * (K + 1)) ≤ (T + 1 - T) / (2 * ((Z.image fun z ↦ |z.im|).card + 1)) := by
    rw [add_sub_cancel_left]
    gcongr
  refine ⟨T', hT', fun σ hσ₁ hσ₂ s hs ↦ ?_⟩
  have hsre : s.re = σ := by rcases hs with rfl | rfl <;> simp
  have hsim : |s.im| = T' := by
    rcases hs with rfl | rfl <;> simp [abs_of_nonneg (by linarith [hT'.1] : (0 : ℝ) ≤ T')]
  have hsep (z : ℂ) (hz : z ∈ Z) : 1 / (2 * (K + 1)) ≤ ‖s - z‖ := by
    refine (hδ.trans (hsepT' _ (Finset.mem_image_of_mem _ hz))).trans ?_
    rw [← hsim]
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by simpa using abs_im_le_norm (s - z))
  obtain ⟨hζ, hbound⟩ := riemannZeta_ne_zero_and_norm_logDeriv_le hCw (Z := Z)
    (one_div_pos.2 (by linarith)) (hsre ▸ hσ₁) (hsre ▸ hσ₂) (by linarith [hT'.1])
    (fun z h1 h2 h3 h4 ↦ mem_union_riemannZetaZerosClosedBall_of_window (hsim ▸ hT'.1)
      (hsim ▸ hT'.2) ⟨h1, h2, h3⟩ h4) hsep
  refine ⟨hζ, hbound.trans ?_⟩
  -- `log (|Im s| + 2) ≤ 2 log (T + 2)`, and `K / δ = 2 K (K + 1)`
  have hlog : Real.log (|s.im| + 2) ≤ 2 * Real.log (T + 2) :=
    Real.log_add_two_le_two_mul_log_add_two (by linarith) (abs_nonneg _)
      (by linarith [hT'.2])
  have hKδ : K / (1 / (2 * (K + 1))) = 2 * K * (K + 1) := by
    rw [div_div_eq_mul_div, div_one]
    ring
  rw [hKδ]
  exact mul_add_two_mul_mul_add_one_le
    ((Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_d9]))
    (Real.log_nonneg (by linarith [abs_nonneg s.im])) hlog hK0
    (abs_of_nonneg (by linarith : (0 : ℝ) ≤ T) ▸ sum_toNat_analyticOrderAt_union_le hCc T)

end TauCeti
