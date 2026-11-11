/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Contour.Residue.Cycle
public import TauCeti.Analysis.Contour.Winding.Number.Rectangle
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Shifting a vertical line of integration past simple poles

Let `F` be holomorphic on a neighbourhood of the closed strip `d ≤ Re t ≤ c` except at a finite
set `P` of poles inside the open strip, integrable on both boundary lines, and such that
the horizontal connectors `∫_d^c F(x + iT) dx` tend to `0` as `T → ±∞`. Then

`∫_ℝ F(c + iy) dy - ∫_ℝ F(d + iy) dy = 2π ∑_{p ∈ P} Res(F, p)`.

This is the line shift behind DLMF 2.5.6–2.5.7 and behind the evaluation of Mellin–Barnes
integrals by residues. The proof applies Tau Ceti's residue theorem for null-homologous curves to
the boundary of the rectangle `[d, c] × [-T, T]`, which winds once around every pole, and lets
`T → ∞`. The line integrals use `dy`, so the factor `i` of `dt = i dy` cancels against the `2πi`
of the residue theorem.

## Main results

* `TauCeti.Contour.residue_eq_of_eventuallyEq_div_sub`: if `F(t) = φ(t)/(t - p)` near `p` with
  `φ` analytic at `p`, the residue of `F` at `p` is `φ(p)`.
* `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue`: the line shift past simple
  poles, and `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue_of_meromorphicAt`
  past meromorphic singularities of any order.
* `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_range_residue`: its iteration across a
  decreasing sequence of lines with one simple pole between consecutive lines, and
  `TauCeti.Contour.tendsto_sum_range_residue`, `TauCeti.Contour.hasSum_residue`: the resulting
  residue series.
-/

@[expose] public section

open Complex Set Filter MeasureTheory
open scoped Topology Real

namespace TauCeti.Contour

/-- At a simple pole written as `F(t) = φ(t)/(t - p)` with `φ` analytic at `p`, the residue of
`F` is `φ(p)`. Removable singularities are included, with `φ(p) = 0`. -/
theorem residue_eq_of_eventuallyEq_div_sub {F φ : ℂ → ℂ} {p : ℂ} (hφ : AnalyticAt ℂ φ p)
    (hF : ∀ᶠ t in 𝓝[≠] p, F t = φ t / (t - p)) : residue F p = φ p := by
  rw [residue_congr_nhdsNE hF]
  simpa using residue_div_sub_pow_of_analyticAt hφ 0

/-- A function of the form `φ(t)/(t - p)` near `p`, with `φ` analytic at `p`, is meromorphic
at `p`. -/
theorem meromorphicAt_of_eventuallyEq_div_sub {F φ : ℂ → ℂ} {p : ℂ} (hφ : AnalyticAt ℂ φ p)
    (hF : ∀ᶠ t in 𝓝[≠] p, F t = φ t / (t - p)) : MeromorphicAt F p :=
  (hφ.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt).congr
    (hF.mono fun _ ht => ht.symm)

/-- The residue theorem on the rectangle `[d, c] × [-T, T]`, written edge by edge. -/
private theorem rectangle_edges_eq {F : ℂ → ℂ} {c d T : ℝ} (hdc : d < c) (hT : 0 < T)
    {U : Set ℂ} (hU : IsOpen U) (hstrip : {t : ℂ | d ≤ t.re ∧ t.re ≤ c} ⊆ U)
    (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c) (hPT : ∀ p ∈ P, |p.im| < T)
    (hF : DifferentiableOn ℂ F (U \ (P : Set ℂ))) (hmero : ∀ p ∈ P, MeromorphicAt F p) :
    (∫ x : ℝ in d..c, F (x + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in d..c, F (x + T * I)) +
        I • (∫ y : ℝ in (-T)..T, F (c + y * I)) - I • (∫ y : ℝ in (-T)..T, F (d + y * I)) =
      2 * (π : ℂ) * I * ∑ p ∈ P, residue F p := by
  set z : ℂ := ⟨d, -T⟩
  set w : ℂ := ⟨c, T⟩
  have hre : z.re ≤ w.re := hdc.le
  have him : z.im ≤ w.im := by change -T ≤ T; linarith
  have hrect : Rectangle z w ⊆ U := fun t ht => by
    rw [Rectangle, mem_reProdIm, uIcc_of_le hre, uIcc_of_le him] at ht
    exact hstrip ⟨ht.1.1, ht.1.2⟩
  have hPint : ∀ p ∈ P, p ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im := fun p hp =>
    ⟨hP p hp, abs_lt.mp (hPT p hp)⟩
  have hfront : ∀ t ∈ frontier (Rectangle z w), t ∉ (P : Set ℂ) := fun t ht htP => by
    have hi := hPint t htP
    rw [← interior_rectangle hre him] at hi
    exact disjoint_left.1 disjoint_interior_frontier hi ht
  have hmem : ∀ t ∈ uIcc (0 : ℝ) 4, rectBoundary z w t ∈ frontier (Rectangle z w) := fun t ht =>
    image_rectBoundary z w ▸ mem_image_of_mem _ (by rwa [uIcc_of_le (by norm_num)] at ht)
  have hoff : ∀ t ∈ uIcc (0 : ℝ) 4, rectBoundary z w t ∉ (P : Set ℂ) := fun t ht =>
    hfront _ (hmem t ht)
  have hres := classicalResidueTheorem_nullHomologous hU hF (fun s hs _ => hmero s hs)
    (isPiecewiseC1On_rectBoundary z w)
    (fun t ht => hrect ((isClosed_rectangle z w).frontier_subset (hmem t ht)))
    (by rw [rectBoundary_zero, rectBoundary_four]) hoff (isNullHomologous_rectBoundary hrect)
  rw [Finset.sum_congr rfl fun p hp => by
    rw [windingNumber_rectBoundary_eq_one (hPint p hp), one_mul]] at hres
  have hcont : ContinuousOn F (frontier (Rectangle z w)) :=
    hF.continuousOn.mono fun t ht =>
      ⟨hrect ((isClosed_rectangle z w).frontier_subset ht), hfront t ht⟩
  rw [integral_rectBoundary hcont] at hres
  exact hres

/-- **Shifting the line of integration past meromorphic singularities.** Let `F` be holomorphic
on an open neighbourhood `U` of the closed strip `d ≤ Re t ≤ c` except at a finite set `P` of
points of the open strip, at each of which `F` is meromorphic, integrable on the lines
`Re t = c` and `Re t = d`, and with horizontal connectors `∫_d^c F(x + iT) dx` tending to `0` as
`T → ±∞`. Then `∫_ℝ F(c + iy) dy - ∫_ℝ F(d + iy) dy = 2π ∑_{p ∈ P} Res(F, p)`. -/
theorem integral_vertical_sub_eq_two_pi_mul_sum_residue_of_meromorphicAt (F : ℂ → ℂ) {c d : ℝ}
    (hdc : d < c) {U : Set ℂ} (hU : IsOpen U) (hstrip : {t : ℂ | d ≤ t.re ∧ t.re ≤ c} ⊆ U)
    (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hF : DifferentiableOn ℂ F (U \ (P : Set ℂ))) (hmero : ∀ p ∈ P, MeromorphicAt F p)
    (hc : Integrable fun y : ℝ => F (c + y * I)) (hd : Integrable fun y : ℝ => F (d + y * I))
    (htop : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atBot (𝓝 0)) :
    (∫ y : ℝ, F (c + y * I)) - ∫ y : ℝ, F (d + y * I) =
      2 * π * ∑ p ∈ P, residue F p := by
  have hlim : Tendsto (fun T : ℝ =>
      (∫ x : ℝ in d..c, F (x + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in d..c, F (x + T * I)) +
        I • (∫ y : ℝ in (-T)..T, F (c + y * I)) - I • (∫ y : ℝ in (-T)..T, F (d + y * I)))
      atTop (𝓝 (0 - 0 + I • (∫ y : ℝ, F (c + y * I)) - I • ∫ y : ℝ, F (d + y * I))) :=
    (((hbot.comp tendsto_neg_atTop_atBot).sub htop).add
      ((intervalIntegral_tendsto_integral hc tendsto_neg_atTop_atBot tendsto_id).const_smul
        I)).sub
      ((intervalIntegral_tendsto_integral hd tendsto_neg_atTop_atBot tendsto_id).const_smul I)
  have hev : ∀ᶠ T : ℝ in atTop, 0 < T ∧ ∀ p ∈ P, |p.im| < T :=
    (eventually_gt_atTop 0).and ((Finset.eventually_all P).mpr fun p _ => eventually_gt_atTop _)
  have hconst : Tendsto (fun T : ℝ =>
      (∫ x : ℝ in d..c, F (x + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in d..c, F (x + T * I)) +
        I • (∫ y : ℝ in (-T)..T, F (c + y * I)) - I • (∫ y : ℝ in (-T)..T, F (d + y * I)))
      atTop (𝓝 (2 * (π : ℂ) * I * ∑ p ∈ P, residue F p)) :=
    tendsto_const_nhds.congr' (hev.mono fun T hT =>
      (rectangle_edges_eq hdc hT.1 hU hstrip P hP hT.2 hF hmero).symm)
  have h := tendsto_nhds_unique hlim hconst
  simp only [sub_zero, zero_add, smul_eq_mul, ← mul_sub] at h
  apply mul_left_cancel₀ I_ne_zero
  rw [h]
  ring

/-- **Shifting the line of integration past simple poles.** Let `F` be holomorphic on an open
neighbourhood `U` of the closed strip `d ≤ Re t ≤ c` except at a finite set `P` of simple poles in
the open strip, integrable on the lines `Re t = c` and `Re t = d`, and with horizontal connectors
`∫_d^c F(x + iT) dx` tending to `0` as `T → ±∞`. Then
`∫_ℝ F(c + iy) dy - ∫_ℝ F(d + iy) dy = 2π ∑_{p ∈ P} Res(F, p)`. -/
theorem integral_vertical_sub_eq_two_pi_mul_sum_residue (F : ℂ → ℂ) {c d : ℝ} (hdc : d < c)
    {U : Set ℂ} (hU : IsOpen U) (hstrip : {t : ℂ | d ≤ t.re ∧ t.re ≤ c} ⊆ U)
    (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hF : DifferentiableOn ℂ F (U \ (P : Set ℂ)))
    (hpole : ∀ p ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ t in 𝓝[≠] p, F t = g t / (t - p))
    (hc : Integrable fun y : ℝ => F (c + y * I)) (hd : Integrable fun y : ℝ => F (d + y * I))
    (htop : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atBot (𝓝 0)) :
    (∫ y : ℝ, F (c + y * I)) - ∫ y : ℝ, F (d + y * I) =
      2 * π * ∑ p ∈ P, residue F p :=
  integral_vertical_sub_eq_two_pi_mul_sum_residue_of_meromorphicAt F hdc hU hstrip P hP hF
    (fun p hp => by
      obtain ⟨g, hg, hFg⟩ := hpole p hp
      exact meromorphicAt_of_eventuallyEq_div_sub hg hFg) hc hd htop hbot

/-- **Iterated line shifts.** Let `c₀ > c₁ > ⋯` be lines with exactly one simple pole `p n` of
`F` in each strip `c (n + 1) < Re t < c n`, each strip satisfying the hypotheses of
`integral_vertical_sub_eq_two_pi_mul_sum_residue`. Then
`∫_ℝ F(c₀ + iy) dy - ∫_ℝ F(c_N + iy) dy = 2π ∑_{n < N} Res(F, p n)`. -/
theorem integral_vertical_sub_eq_two_pi_mul_sum_range_residue (F : ℂ → ℂ) {c : ℕ → ℝ}
    {p : ℕ → ℂ} (hc : ∀ n, c (n + 1) < c n) {U : ℕ → Set ℂ} (hU : ∀ n, IsOpen (U n))
    (hstrip : ∀ n, {t : ℂ | c (n + 1) ≤ t.re ∧ t.re ≤ c n} ⊆ U n)
    (hp : ∀ n, c (n + 1) < (p n).re ∧ (p n).re < c n)
    (hF : ∀ n, DifferentiableOn ℂ F (U n \ {p n}))
    (hpole : ∀ n, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (p n) ∧
      ∀ᶠ t in 𝓝[≠] p n, F t = g t / (t - p n))
    (hint : ∀ n, Integrable fun y : ℝ => F (c n + y * I))
    (htop : ∀ n, Tendsto (fun T : ℝ => ∫ x in c (n + 1)..c n, F (x + T * I)) atTop (𝓝 0))
    (hbot : ∀ n, Tendsto (fun T : ℝ => ∫ x in c (n + 1)..c n, F (x + T * I)) atBot (𝓝 0))
    (N : ℕ) :
    (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      2 * π * ∑ n ∈ Finset.range N, residue F (p n) := by
  have hstep : ∀ n, (∫ y : ℝ, F (c n + y * I)) - ∫ y : ℝ, F (c (n + 1) + y * I) =
      2 * π * residue F (p n) := fun n => by
    have h := integral_vertical_sub_eq_two_pi_mul_sum_residue F (hc n) (hU n) (hstrip n) {p n}
      (by simpa using hp n) (by simpa using hF n) (by simpa using hpole n) (hint n)
      (hint (n + 1)) (htop n) (hbot n)
    simpa using h
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ← ih, ← hstep N]
    ring

/-- If the partial residue sums of iterated line shifts satisfy the identity of
`integral_vertical_sub_eq_two_pi_mul_sum_range_residue` and the integrals on the lines `c N`
tend to `0`, the partial residue sums tend to `(2π)⁻¹ ∫_ℝ F(c₀ + iy) dy`. -/
theorem tendsto_sum_range_residue {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ}
    (hsum : ∀ N, (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      2 * π * ∑ n ∈ Finset.range N, residue F (p n))
    (hlim : Tendsto (fun N => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, residue F (p n)) atTop
      (𝓝 ((2 * π : ℂ)⁻¹ * ∫ y : ℝ, F (c 0 + y * I))) := by
  have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have h := ((tendsto_const_nhds (x := ∫ y : ℝ, F (c 0 + y * I))).sub hlim).const_mul
    (2 * π : ℂ)⁻¹
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  rw [hsum N, ← mul_assoc, inv_mul_cancel₀ h2π, one_mul]

/-- When the residue series of iterated line shifts is summable, its sum is
`(2π)⁻¹ ∫_ℝ F(c₀ + iy) dy`. -/
theorem hasSum_residue {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ}
    (hsum : ∀ N, (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      2 * π * ∑ n ∈ Finset.range N, residue F (p n))
    (hlim : Tendsto (fun N => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0))
    (hs : Summable fun n => residue F (p n)) :
    HasSum (fun n => residue F (p n)) ((2 * π : ℂ)⁻¹ * ∫ y : ℝ, F (c 0 + y * I)) :=
  (hs.hasSum_iff_tendsto_nat).mpr (tendsto_sum_range_residue hsum hlim)

end TauCeti.Contour
