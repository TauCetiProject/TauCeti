/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Winding.Number.Rectangle
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Shifting a vertical line of integration past poles

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

* `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue`: the line shift past
  meromorphic singularities of any order, and
  `TauCeti.Contour.tendsto_intervalIntegral_vertical_sub`: its symmetric-limit form, which needs
  no integrability on the two lines.
* `TauCeti.Contour.tendsto_intervalIntegral_horizontal`: the horizontal connectors vanish when the
  integrand decays uniformly on the strip.
* `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_range_residue`: its iteration across
  finitely many lines with one singularity between consecutive lines, and
  `TauCeti.Contour.tendsto_sum_range_residue`, `TauCeti.Contour.hasSum_residue`: the resulting
  residue series.

The statements follow the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMFMathlib/Analysis/Complex/VerticalResidues.lean` and
`DLMF/AsymptoticApproximations/Mellin/Transforms.lean`. The line shift is proved here through Tau
Ceti's rectangle residue theorem instead of lean-DLMF's own contour machinery.
-/

public section

open Complex Set Filter MeasureTheory
open scoped Topology Real

namespace TauCeti.Contour

/-- The residue theorem on the rectangle `[d, c] × [-T, T]`, written edge by edge. -/
private theorem rectangle_edges_eq {F : ℂ → ℂ} {c d T : ℝ} (hdc : d ≤ c) (hT : 0 < T)
    {U : Set ℂ} (hU : IsOpen U) (hstrip : {t : ℂ | d ≤ t.re ∧ t.re ≤ c} ⊆ U)
    (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c) (hPT : ∀ p ∈ P, |p.im| < T)
    (hF : DifferentiableOn ℂ F (U \ (P : Set ℂ))) (hmero : ∀ p ∈ P, MeromorphicAt F p) :
    (∫ x : ℝ in d..c, F (x + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in d..c, F (x + T * I)) +
        I • (∫ y : ℝ in (-T)..T, F (c + y * I)) - I • (∫ y : ℝ in (-T)..T, F (d + y * I)) =
      2 * (π : ℂ) * I * ∑ p ∈ P, residue F p := by
  set z : ℂ := ⟨d, -T⟩
  set w : ℂ := ⟨c, T⟩
  have hre : z.re ≤ w.re := hdc
  have him : z.im ≤ w.im := by simp only [z, w]; linarith
  have hrect : Rectangle z w ⊆ U := fun t ht => hstrip ((mem_rectangle_iff hre him).1 ht).1
  have hPint : ∀ p ∈ P, p ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im := fun p hp =>
    ⟨hP p hp, abs_lt.mp (hPT p hp)⟩
  have hfront : ∀ t ∈ frontier (Rectangle z w), t ∉ (P : Set ℂ) := fun t ht htP => by
    have hi := hPint t htP
    rw [← interior_rectangle hre him] at hi
    exact disjoint_left.1 disjoint_interior_frontier hi ht
  have hoff : ∀ t ∈ uIcc (0 : ℝ) 4, rectBoundary z w t ∉ (P : Set ℂ) := fun t _ =>
    hfront _ (rectBoundary_mem_frontier t)
  have hres := classicalResidueTheorem_nullHomologous hU hF (fun s hs _ => hmero s hs)
    (isPiecewiseC1On_rectBoundary z w) (fun t _ => hrect (rectBoundary_mem_rectangle t))
    (by rw [rectBoundary_zero, rectBoundary_four]) hoff (isNullHomologous_rectBoundary hrect)
  rw [Finset.sum_congr rfl fun p hp => by
    rw [windingNumber_rectBoundary_eq_one (hPint p hp), one_mul]] at hres
  have hcont : ContinuousOn F (frontier (Rectangle z w)) :=
    hF.continuousOn.mono fun t ht =>
      ⟨hrect ((isClosed_rectangle z w).frontier_subset ht), hfront t ht⟩
  rw [integral_rectBoundary hcont] at hres
  exact hres

/-- If `H(σ + iT) → 0` as `T` tends along `l`, uniformly for `σ` between `d` and `c`, then the
horizontal connector `∫_d^c H(σ + iT) dσ` tends to `0` along `l`. -/
theorem tendsto_intervalIntegral_horizontal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : ℂ → E} {c d : ℝ} {l : Filter ℝ}
    (h : Tendsto (fun q : ℝ × ℝ => H (q.2 + q.1 * I)) (l ×ˢ 𝓟 (uIcc d c)) (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ σ in d..c, H (σ + T * I)) l (𝓝 0) :=
  TendstoUniformlyOn.tendsto_intervalIntegral_nhds_zero (tendsto_prod_principal_iff.mp h)

/-- **The symmetric line shift.** Let `F` be holomorphic on an open neighbourhood `U` of the closed
strip `d ≤ Re t ≤ c` except at a finite set `P` of points of the open strip, at each of which `F`
is meromorphic, and with horizontal connectors `∫_d^c F(x + iT) dx` tending to `0` as
`T → ±∞`. Then `∫_{-T}^{T} F(c + iy) dy - ∫_{-T}^{T} F(d + iy) dy → 2π ∑_{p ∈ P} Res(F, p)` as
`T → ∞`; no integrability on the two lines is needed. -/
theorem tendsto_intervalIntegral_vertical_sub (F : ℂ → ℂ) {c d : ℝ} (hdc : d ≤ c) {U : Set ℂ}
    (hU : IsOpen U) (hstrip : {t : ℂ | d ≤ t.re ∧ t.re ≤ c} ⊆ U)
    (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hF : DifferentiableOn ℂ F (U \ (P : Set ℂ))) (hmero : ∀ p ∈ P, MeromorphicAt F p)
    (htop : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atBot (𝓝 0)) :
    Tendsto (fun T : ℝ =>
        (∫ y : ℝ in (-T)..T, F (c + y * I)) - ∫ y : ℝ in (-T)..T, F (d + y * I))
      atTop (𝓝 (2 * π * ∑ p ∈ P, residue F p)) := by
  have hev : ∀ᶠ T : ℝ in atTop, 0 < T ∧ ∀ p ∈ P, |p.im| < T :=
    (eventually_gt_atTop 0).and ((Finset.eventually_all P).mpr fun p _ => eventually_gt_atTop _)
  -- Solve the rectangle identity for the difference of the vertical edges.
  have hlim : Tendsto (fun T : ℝ => 2 * π * ∑ p ∈ P, residue F p - I⁻¹ *
      ((∫ x : ℝ in d..c, F (x + ((-T : ℝ) : ℂ) * I)) - ∫ x : ℝ in d..c, F (x + T * I)))
      atTop (𝓝 (2 * π * ∑ p ∈ P, residue F p - I⁻¹ * (0 - 0))) :=
    tendsto_const_nhds.sub (((hbot.comp tendsto_neg_atTop_atBot).sub htop).const_mul _)
  rw [sub_zero, mul_zero, sub_zero] at hlim
  refine hlim.congr' (hev.mono fun T hT => ?_)
  have h := rectangle_edges_eq hdc hT.1 hU hstrip P hP hT.2 hF hmero
  simp only [smul_eq_mul] at h
  linear_combination (-I⁻¹) * h + ((∫ y : ℝ in (-T)..T, F (c + y * I)) -
    (∫ y : ℝ in (-T)..T, F (d + y * I)) - 2 * π * ∑ p ∈ P, residue F p) *
      inv_mul_cancel₀ I_ne_zero

/-- **Shifting the line of integration past meromorphic singularities.** Let `F` be holomorphic
on an open neighbourhood `U` of the closed strip `d ≤ Re t ≤ c` except at a finite set `P` of
points of the open strip, at each of which `F` is meromorphic, integrable on the lines
`Re t = c` and `Re t = d`, and with horizontal connectors `∫_d^c F(x + iT) dx` tending to `0` as
`T → ±∞`. Then `∫_ℝ F(c + iy) dy - ∫_ℝ F(d + iy) dy = 2π ∑_{p ∈ P} Res(F, p)`. The poles may have
any order; a simple pole `F(t) = g(t)/(t - p)` with `g` analytic at `p` is meromorphic by
`MeromorphicAt.meromorphicAt_congr`. -/
theorem integral_vertical_sub_eq_two_pi_mul_sum_residue (F : ℂ → ℂ) {c d : ℝ} (hdc : d ≤ c)
    {U : Set ℂ} (hU : IsOpen U) (hstrip : {t : ℂ | d ≤ t.re ∧ t.re ≤ c} ⊆ U)
    (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hF : DifferentiableOn ℂ F (U \ (P : Set ℂ))) (hmero : ∀ p ∈ P, MeromorphicAt F p)
    (hc : Integrable fun y : ℝ => F (c + y * I)) (hd : Integrable fun y : ℝ => F (d + y * I))
    (htop : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atBot (𝓝 0)) :
    (∫ y : ℝ, F (c + y * I)) - ∫ y : ℝ, F (d + y * I) =
      2 * π * ∑ p ∈ P, residue F p :=
  tendsto_nhds_unique
    ((intervalIntegral_tendsto_integral hc tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral hd tendsto_neg_atTop_atBot tendsto_id))
    (tendsto_intervalIntegral_vertical_sub F hdc hU hstrip P hP hF hmero htop hbot)

/-- **Iterated line shifts.** Let `c₀, c₁, …, c_N` be lines with exactly one singularity `p n` of
`F`, at which `F` is meromorphic, in each strip `c (n + 1) < Re t < c n` for `n < N`, each strip
satisfying the hypotheses of `integral_vertical_sub_eq_two_pi_mul_sum_residue`.
The poles may have any order. Then
`∫_ℝ F(c₀ + iy) dy - ∫_ℝ F(c_N + iy) dy = 2π ∑_{n < N} Res(F, p n)`. -/
theorem integral_vertical_sub_eq_two_pi_mul_sum_range_residue (F : ℂ → ℂ) {c : ℕ → ℝ}
    {p : ℕ → ℂ} (N : ℕ) {U : ℕ → Set ℂ} (hU : ∀ n < N, IsOpen (U n))
    (hstrip : ∀ n < N, {t : ℂ | c (n + 1) ≤ t.re ∧ t.re ≤ c n} ⊆ U n)
    (hp : ∀ n < N, c (n + 1) < (p n).re ∧ (p n).re < c n)
    (hF : ∀ n < N, DifferentiableOn ℂ F (U n \ {p n}))
    (hmero : ∀ n < N, MeromorphicAt F (p n))
    (hint : ∀ n ≤ N, Integrable fun y : ℝ => F (c n + y * I))
    (htop : ∀ n < N,
      Tendsto (fun T : ℝ => ∫ x in c (n + 1)..c n, F (x + T * I)) atTop (𝓝 0))
    (hbot : ∀ n < N,
      Tendsto (fun T : ℝ => ∫ x in c (n + 1)..c n, F (x + T * I)) atBot (𝓝 0)) :
    (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      2 * π * ∑ n ∈ Finset.range N, residue F (p n) := by
  have hstep : ∀ n ∈ Finset.range N, (∫ y : ℝ, F (c n + y * I)) -
      ∫ y : ℝ, F (c (n + 1) + y * I) = 2 * π * residue F (p n) := fun n hn => by
    have hn := Finset.mem_range.mp hn
    have h := integral_vertical_sub_eq_two_pi_mul_sum_residue F
      ((hp n hn).1.trans (hp n hn).2).le (hU n hn) (hstrip n hn) {p n} (by simpa using hp n hn)
      (by simpa using hF n hn) (by simpa using hmero n hn) (hint n hn.le) (hint (n + 1) hn)
      (htop n hn) (hbot n hn)
    simpa using h
  rw [← Finset.sum_range_sub' (fun n => ∫ y : ℝ, F (c n + y * I)) N, Finset.mul_sum]
  exact Finset.sum_congr rfl hstep

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

/-- Under the hypotheses of `tendsto_sum_range_residue` (the identity of
`integral_vertical_sub_eq_two_pi_mul_sum_range_residue` for every `N`, and
`∫_ℝ F(c_N + iy) dy → 0`), if the residue series is summable then its sum is
`(2π)⁻¹ ∫_ℝ F(c₀ + iy) dy`. -/
theorem hasSum_residue {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ}
    (hsum : ∀ N, (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      2 * π * ∑ n ∈ Finset.range N, residue F (p n))
    (hlim : Tendsto (fun N => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0))
    (hs : Summable fun n => residue F (p n)) :
    HasSum (fun n => residue F (p n)) ((2 * π : ℂ)⁻¹ * ∫ y : ℝ, F (c 0 + y * I)) :=
  (hs.hasSum_iff_tendsto_nat).mpr (tendsto_sum_range_residue hsum hlim)

end TauCeti.Contour
