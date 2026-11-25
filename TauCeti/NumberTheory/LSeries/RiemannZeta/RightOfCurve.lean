/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.LSeries.ZetaZeros
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFreeRegion.RiemannZeta
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Window
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogUpperBound

/-!
# Bounds for `ζ′` and `ζ′/ζ` right of the classical curve

Write `L = log (|Im s| + 2)`. There are `0 < β < 1` and `C` such that every `s ≠ 1` with
`1 - β / L ≤ Re s` has `ζ(s) ≠ 0`, `‖ζ′(s) + 1/(s - 1)²‖ ≤ C L²` and
`‖ζ′/ζ(s) + 1/(s - 1)‖ ≤ C L`. The region is the whole half-plane right of the curve.

## Main results

* `TauCeti.exists_norm_deriv_riemannZeta₀_le_mul_log_sq`: for every real `A`, the derivative of
  the entire function `riemannZeta₀ = ζ - 1/(s - 1)` is `O(L²)` on `1 - A / L ≤ Re s`.
* `TauCeti.riemannZeta_deriv_logDeriv_bound`: nonvanishing and the two pole-subtracted bounds on
  the region `1 - β / L ≤ Re s`.

## Implementation notes

The bound for `ζ′` is Cauchy's estimate for `riemannZeta₀` on the circle of radius `1 / L` about
`s`, together with the logarithmic bound `TauCeti.exists_norm_riemannZeta₀_le_mul_log`, which holds
right of every curve `Re s = 1 - A / L`. No zero-free region enters.

For `ζ′/ζ` put `η = 1 / (2L)` and `s₁ = 1 + η + i Im s`. Comparing Dirichlet series with the real
point `1 + η` and the pole bound at `1` bound `ζ′/ζ` by `2L + O(1)` on `Re s ≥ 1 + η`, and
`1/(s - 1)` by `2L` there. Otherwise subtract the window expansions
`TauCeti.riemannZeta_logDeriv_window` at `s` and `s₁`, which share their window of zeros. By the
zero-free region `TauCeti.LFunctions.riemannZeta_zeroFreeRegion` every window zero `ρ` has
`Re ρ ≤ 1 - 2β / L`, so `‖1/(s - ρ) - 1/(s₁ - ρ)‖ ≤ (2 + 1/(2β)) Re 1/(s₁ - ρ)`, and the sum of
the `Re 1/(s₁ - ρ) ≥ 0` is at most the window sum at `s₁`, which is `O(L)`. The choice
`η = 1/(2L)` keeps `Re s₁ ≤ 2` at every height, so no compactness argument is needed at bounded
height.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Theorem 6.7.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§3.9–3.11.
* `ZetaDerivUpperBnd`, `LogDerivZetaBnd` and `LogDerivZetaBndUnif99` in A. Kontorovich, T. Tao
  et al., *PrimeNumberTheoremAnd*, file `PrimeNumberTheoremAnd/ZetaBounds.lean`, for bounded
  real parts and `|Im s|` large.
-/

public section

open Complex Metric

namespace TauCeti

/-- A shift by at most `2` in height at most doubles `log (· + 2)`: for `0 ≤ x` and
`0 ≤ y ≤ x + 2`, `log (y + 2) ≤ 2 log (x + 2)`, since `x + 4 ≤ (x + 2)²`. -/
private lemma log_add_two_le_two_mul_log_add_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hyx : y ≤ x + 2) : Real.log (y + 2) ≤ 2 * Real.log (x + 2) := by
  calc Real.log (y + 2) ≤ Real.log ((x + 2) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
    _ = 2 * Real.log (x + 2) := by rw [Real.log_pow]; norm_num

/-- The case of `log_add_two_le_two_mul_log_add_two` used for the zero-free region:
`log (|y| + 3) ≤ 2 log (|x| + 2)` when `|y| ≤ |x| + 1`. -/
private lemma log_abs_add_three_le {x y : ℝ} (h : |y| ≤ |x| + 1) :
    Real.log (|y| + 3) ≤ 2 * Real.log (|x| + 2) := by
  have := log_add_two_le_two_mul_log_add_two (abs_nonneg x) (by positivity : 0 ≤ |y| + 1)
    (by linarith)
  rwa [add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] at this

/-- `log 2 ≤ log (|t| + 2)`. -/
private lemma log_two_le_log_abs_add_two (t : ℝ) : Real.log 2 ≤ Real.log (|t| + 2) :=
  Real.log_le_log two_pos (by linarith [abs_nonneg t])

/-- **Cauchy's estimate for `riemannZeta₀` right of the curves.** For every real `A` there is `C`
such that the derivative of the entire function `riemannZeta₀ s = ζ(s) - 1/(s - 1)` satisfies
`‖deriv riemannZeta₀ s‖ ≤ C log² (|Im s| + 2)` whenever `1 - A / log (|Im s| + 2) ≤ Re s`. -/
theorem exists_norm_deriv_riemannZeta₀_le_mul_log_sq (A : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, 1 - A / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta₀ s‖ ≤ C * Real.log (|s.im| + 2) ^ 2 := by
  set B := max A 0
  obtain ⟨C, hC⟩ := exists_norm_riemannZeta₀_le_mul_log (2 * (B + 1))
  refine ⟨2 * max C 0, fun s hs ↦ ?_⟩
  set L := Real.log (|s.im| + 2)
  have hL2 := log_two_le_log_abs_add_two s.im
  have hL : 0 < L := (Real.log_pos one_lt_two).trans_le hL2
  have hLinv : L⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hL two_pos]
    linarith [Real.log_two_gt_d9]
  have hsB : 1 - B / L ≤ s.re :=
    le_trans (sub_le_sub_left (div_le_div_of_nonneg_right (le_max_left _ _) hL.le) 1) hs
  have hsph : ∀ z ∈ sphere s L⁻¹, ‖riemannZeta₀ z‖ ≤ 2 * max C 0 * L := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have him : |z.im - s.im| ≤ 2 := by
      have := abs_im_le_norm (z - s)
      rw [sub_im] at this
      linarith
    have hre : s.re - L⁻¹ ≤ z.re := by
      have := neg_abs_le (z - s).re
      have := abs_re_le_norm (z - s)
      rw [sub_re] at *
      linarith
    have hLz : Real.log (|z.im| + 2) ≤ 2 * L :=
      log_add_two_le_two_mul_log_add_two (abs_nonneg _) (abs_nonneg _)
        (by linarith [abs_sub_abs_le_abs_sub z.im s.im])
    have hLz0 : 0 < Real.log (|z.im| + 2) :=
      (Real.log_pos one_lt_two).trans_le (log_two_le_log_abs_add_two z.im)
    have hzA : 1 - 2 * (B + 1) / Real.log (|z.im| + 2) ≤ z.re := by
      have h1 : (B + 1) / L ≤ 2 * (B + 1) / Real.log (|z.im| + 2) := by
        rw [div_le_div_iff₀ hL hLz0]
        nlinarith [le_max_right A 0]
      have h2 : B / L + L⁻¹ = (B + 1) / L := by field_simp
      linarith
    calc ‖riemannZeta₀ z‖ ≤ C * Real.log (|z.im| + 2) := hC z hzA
      _ ≤ max C 0 * Real.log (|z.im| + 2) := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (2 * L) := by gcongr
      _ = 2 * max C 0 * L := by ring
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (inv_pos.mpr hL)
    differentiable_riemannZeta₀.diffContOnCl hsph
  rwa [div_inv_eq_mul, mul_assoc, ← sq] at this

/-- Right of `Re s = 1 + η` with `0 < η ≤ 1`, the Dirichlet-series comparison
`‖ζ′/ζ(w)‖ ≤ -ζ′/ζ(1 + η)` (the conductor-one case of
`DirichletCharacter.norm_logDeriv_LFunction_le_of_le_re`) and a pole bound
`-ζ′/ζ(1 + η) ≤ 1/η + C` give `‖ζ′/ζ(w) + 1/(w - 1)‖ ≤ 2/η + C`. -/
private lemma norm_logDeriv_add_one_div_le_of_le_re {CN : ℝ}
    (hNear : ∀ {η : ℝ}, 0 < η → η ≤ 1 → -(logDeriv riemannZeta (1 + η)).re ≤ η⁻¹ + CN)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {w : ℂ} (hw : 1 + η ≤ w.re) :
    ‖deriv riemannZeta w / riemannZeta w + 1 / (w - 1)‖ ≤ 2 * η⁻¹ + CN := by
  have h1 : ‖deriv riemannZeta w / riemannZeta w‖ ≤ η⁻¹ + CN := by
    rw [← logDeriv_apply]
    have hcmp : ‖logDeriv riemannZeta w‖ ≤ -(logDeriv riemannZeta ((1 + η : ℝ) : ℂ)).re := by
      simpa [DirichletCharacter.LFunction_modOne_eq] using
        (1 : DirichletCharacter ℂ 1).norm_logDeriv_LFunction_le_of_le_re (by linarith) hw
    refine hcmp.trans ?_
    have := hNear hη hη1
    push_cast
    linarith
  have h2 : ‖1 / (w - 1)‖ ≤ η⁻¹ := by
    rw [norm_div, norm_one, one_div]
    refine inv_anti₀ hη ?_
    have := re_le_norm (w - 1)
    rw [sub_re, one_re] at this
    linarith
  linarith [norm_add_le (deriv riemannZeta w / riemannZeta w) (1 / (w - 1))]

/-- The comparison of one window zero `ρ` at `s` and at `s₁ = 1 + η + i Im s`: if
`1 - a ≤ Re s < 1 + η` and `Re ρ ≤ 1 - 2a` with `0 < a`, `0 < η`, then
`‖1/(s - ρ) - 1/(s₁ - ρ)‖ ≤ (2 + η / a) Re 1/(s₁ - ρ)`. -/
private lemma norm_one_div_sub_sub_one_div_sub_le {s s₁ ρ : ℂ} {a η : ℝ} (ha : 0 < a)
    (hη : 0 < η) (hs₁re : s₁.re = 1 + η) (hs₁im : s₁.im = s.im) (hs : 1 - a ≤ s.re)
    (hs' : s.re < 1 + η) (hρ : ρ.re ≤ 1 - 2 * a) :
    ‖1 / (s - ρ) - 1 / (s₁ - ρ)‖ ≤ (2 + η / a) * (1 / (s₁ - ρ)).re := by
  set u := s - ρ
  set v := s₁ - ρ
  have hure : a ≤ u.re := by simp only [u, sub_re]; linarith
  have hvre : η + 2 * a ≤ v.re := by simp only [v, sub_re]; linarith
  have hu : a ≤ ‖u‖ := hure.trans (re_le_norm u)
  have hu0 : u ≠ 0 := norm_pos_iff.mp (ha.trans_le hu)
  have hv0 : v ≠ 0 := fun h ↦ by simp [h] at hvre; linarith
  have hvu : v - u = ((1 + η - s.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [u, v, hs₁re, hs₁im]
  have hd : ‖v - u‖ = 1 + η - s.re := by
    rw [hvu, norm_real, Real.norm_of_nonneg (by linarith)]
  have hvle : ‖v‖ ≤ ‖u‖ + (1 + η - s.re) := by
    have := norm_add_le u (v - u)
    rwa [add_sub_cancel, hd] at this
  have hkey : (1 + η - s.re) * ‖v‖ ≤ (2 + η / a) * v.re * ‖u‖ := by
    have h1 : 1 + η - s.re ≤ v.re := by linarith
    have h2 : ‖v‖ ≤ (2 + η / a) * ‖u‖ := by
      have : η + a ≤ (1 + η / a) * ‖u‖ := by
        have : (1 + η / a) * a = η + a := by field_simp; ring
        nlinarith [div_pos hη ha]
      nlinarith
    calc (1 + η - s.re) * ‖v‖ ≤ v.re * ((2 + η / a) * ‖u‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
      _ = _ := by ring
  have hre : (1 / v).re = v.re / ‖v‖ ^ 2 := by
    rw [one_div, inv_re, normSq_eq_norm_sq]
  rw [hre, one_div, one_div, inv_sub_inv hu0 hv0, norm_div, norm_mul, hd, mul_div_assoc']
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (1 + η - s.re) * ‖v‖ ^ 2 = ((1 + η - s.re) * ‖v‖) * ‖v‖ := by ring
    _ ≤ ((2 + η / a) * v.re * ‖u‖) * ‖v‖ := by gcongr
    _ = _ := by ring

/-- The comparison of the window sums at `s` and at `s₁ = 1 + η + i Im s`, with nonnegative
weights, when every point of `W` lies on `Re z ≤ 1 - 2a`. -/
private lemma norm_sum_div_sub_sub_sum_div_sub_le {s s₁ : ℂ} {a η : ℝ} (ha : 0 < a) (hη : 0 < η)
    (hs₁re : s₁.re = 1 + η) (hs₁im : s₁.im = s.im) (hs : 1 - a ≤ s.re) (hs' : s.re < 1 + η)
    {W : Finset ℂ} (hW : ∀ z ∈ W, z.re ≤ 1 - 2 * a) {m : ℂ → ℝ} (hm : ∀ z, 0 ≤ m z) :
    ‖∑ z ∈ W, (m z : ℂ) / (s - z) - ∑ z ∈ W, (m z : ℂ) / (s₁ - z)‖ ≤
      (2 + η / a) * ‖∑ z ∈ W, (m z : ℂ) / (s₁ - z)‖ := by
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ z ∈ W, ‖(m z : ℂ) / (s - z) - (m z : ℂ) / (s₁ - z)‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ W, (2 + η / a) * ((m z : ℂ) / (s₁ - z)).re := by
      refine Finset.sum_le_sum fun z hz ↦ ?_
      have hpt := norm_one_div_sub_sub_one_div_sub_le ha hη hs₁re hs₁im hs hs' (hW z hz)
      rw [div_eq_mul_one_div (m z : ℂ), div_eq_mul_one_div (m z : ℂ), ← mul_sub, norm_mul,
        norm_real, Real.norm_of_nonneg (hm z), re_ofReal_mul]
      calc _ ≤ m z * ((2 + η / a) * (1 / (s₁ - z)).re) := mul_le_mul_of_nonneg_left hpt (hm z)
        _ = _ := by ring
    _ = (2 + η / a) * (∑ z ∈ W, (m z : ℂ) / (s₁ - z)).re := by rw [← Finset.mul_sum, re_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (re_le_norm _) (by positivity)

/-- The zeros of the window of `ζ` at height `t` form a finite set `W`, and the window sum at every
point `w` of height `t` is a `Finset` sum over `W`. -/
private lemma exists_finset_window (t : ℝ) :
    ∃ W : Finset ℂ, (∀ z ∈ W, 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0) ∧
      ∀ w : ℂ, w.im = t →
        ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - w.im| ≤ 1 ∧ riemannZeta z = 0},
          ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (w - ρ.val) =
            ∑ z ∈ W, (((analyticOrderAt riemannZeta z).toNat : ℝ) : ℂ) / (w - z) := by
  have hfin : {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0}.Finite := by
    refine ((isCompact_closedBall ((2 : ℂ) + t * I) 4).inter_riemannZetaZeros_finite).subset
      fun z hz ↦ ⟨?_, mem_riemannZetaZeros.mpr hz.2.2.2⟩
    obtain ⟨hz0, hz1, hzt, -⟩ := hz
    rw [mem_closedBall, dist_eq_norm]
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    have h1 : (z - (2 + t * I)).re = z.re - 2 := by simp
    have h2 : (z - (2 + t * I)).im = z.im - t := by simp
    rw [h1, h2, abs_of_neg (by linarith)]
    linarith
  refine ⟨hfin.toFinset, fun z hz ↦ by simpa using hz, fun w hw ↦ ?_⟩
  rw [finsum_subtype_eq_finsum_cond
    (f := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℂ) / (w - z))]
  simp only [ofReal_natCast]
  exact finsum_cond_eq_sum_of_cond_iff _ fun {z} _ ↦ by rw [Set.Finite.mem_toFinset, hw]; rfl

/-- With a zero-free width `c` in the normalization `log (|Im s| + 3)`, every zero `z` of `ζ` with
`Re z < 1` and `|Im z - t| ≤ 1` has `Re z ≤ 1 - c / (2 log (|t| + 2))`. -/
private lemma re_le_of_riemannZeta_eq_zero {c : ℝ} (hc : 0 < c)
    (hzf : ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0)
    {t : ℝ} {z : ℂ} (hz1 : z.re < 1) (hzim : |z.im - t| ≤ 1) (hzζ : riemannZeta z = 0) :
    z.re ≤ 1 - c / (2 * Real.log (|t| + 2)) := by
  have hz1' : z ≠ 1 := fun h ↦ by rw [h, one_re] at hz1; exact lt_irrefl _ hz1
  have hlt := lt_of_not_ge fun h ↦ hzf z hz1' h hzζ
  have hLz := log_abs_add_three_le (x := t) (y := z.im)
    (by linarith [abs_sub_abs_le_abs_sub z.im t, (abs_le.mp hzim).2])
  have hlz : 0 < Real.log (|z.im| + 3) := Real.log_pos (by linarith [abs_nonneg z.im])
  have := div_le_div_of_nonneg_left hc.le hlz hLz
  linarith

/-- **The window comparison.** Let `Cw` be a constant of the window form
`TauCeti.riemannZeta_logDeriv_window`, `CN` one of the pole bound at `1` and `c` a zero-free
width. Write `L = log (|Im s| + 2)`. For `0 < β ≤ min (c / 4) (1 / 2)`, every `s ≠ 1` with
`ζ(s) ≠ 0` and `1 - β / L ≤ Re s < 1 + 1/(2L)` has
`‖ζ′/ζ(s) + 1/(s - 1)‖ ≤ |Cw| L + (3 + 1/(2β)) ((4 + |Cw|) L + CN)`. -/
private lemma norm_logDeriv_add_one_div_le_of_re_lt {Cw CN c β : ℝ}
    (hCw : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        Cw * Real.log (|s.im| + 2))
    (hNear : ∀ {η : ℝ}, 0 < η → η ≤ 1 → -(logDeriv riemannZeta (1 + η)).re ≤ η⁻¹ + CN)
    (hc : 0 < c)
    (hzf : ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0)
    (hβ : 0 < β) (hβc : β ≤ c / 4) (hβ2 : β ≤ 1 / 2) {s : ℂ} (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hs : 1 - β / Real.log (|s.im| + 2) ≤ s.re)
    (hsη : s.re < 1 + (2 * Real.log (|s.im| + 2))⁻¹) :
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤
      |Cw| * Real.log (|s.im| + 2) +
        (3 + 1 / (2 * β)) * ((4 + |Cw|) * Real.log (|s.im| + 2) + CN) := by
  set t := s.im
  set L := Real.log (|t| + 2)
  have hL : 1 / 2 ≤ L := by linarith [log_two_le_log_abs_add_two t, Real.log_two_gt_d9]
  set η := (2 * L)⁻¹
  have hη : 0 < η := by positivity
  have hη1 : η ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
  have hβL : β / L ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  set s₁ : ℂ := ((1 + η : ℝ) : ℂ) + t * I
  have hs₁re : s₁.re = 1 + η := by simp [s₁]
  have hs₁im : s₁.im = t := by simp [s₁]
  have hs₁1 : s₁ ≠ 1 := fun h ↦ by rw [h, one_re] at hs₁re; linarith
  have hζ₁ : riemannZeta s₁ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
  -- both window sums run over the same finite set of zeros
  obtain ⟨W, hW, hsum⟩ := exists_finset_window t
  set m : ℂ → ℝ := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ)
  have hw := hCw s (by linarith) (by linarith) hs1 hζ
  have hw₁ := hCw s₁ (by linarith) (by linarith) hs₁1 hζ₁
  rw [hsum s rfl] at hw
  rw [hsum s₁ hs₁im, hs₁im] at hw₁
  set H := deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
  set H₁ := deriv riemannZeta s₁ / riemannZeta s₁ + 1 / (s₁ - 1)
  set S₀ := ∑ z ∈ W, (m z : ℂ) / (s - z)
  set S₁ := ∑ z ∈ W, (m z : ℂ) / (s₁ - z)
  have hCwL : Cw * L ≤ |Cw| * L := mul_le_mul_of_nonneg_right (le_abs_self Cw) (by linarith)
  have hH₁ : ‖H₁‖ ≤ 4 * L + CN := by
    have := norm_logDeriv_add_one_div_le_of_le_re hNear hη hη1 hs₁re.ge
    rw [inv_inv] at this
    linarith
  have hS₁ : ‖S₁‖ ≤ (4 + |Cw|) * L + CN := by linarith [norm_le_norm_add_norm_sub H₁ S₁]
  -- every window zero lies on `Re z ≤ 1 - 2β/L`
  have hzero : ∀ z ∈ W, z.re ≤ 1 - 2 * (β / L) := by
    intro z hz
    obtain ⟨-, hz1, hzim, hzζ⟩ := hW z hz
    have := re_le_of_riemannZeta_eq_zero hc hzf hz1 hzim hzζ
    have : 2 * (β / L) ≤ c / (2 * L) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  have hS := norm_sum_div_sub_sub_sum_div_sub_le (div_pos hβ (by linarith)) hη hs₁re hs₁im
    (by linarith) hsη hzero (m := m) (fun z ↦ Nat.cast_nonneg _)
  rw [show η / (β / L) = 1 / (2 * β) by simp only [η]; field_simp] at hS
  calc ‖H‖ ≤ ‖H - S₀‖ + ‖S₀ - S₁‖ + ‖S₁‖ := by
        simpa using norm_add₃_le (a := H - S₀) (b := S₀ - S₁) (c := S₁)
    _ ≤ |Cw| * L + (2 + 1 / (2 * β)) * ((4 + |Cw|) * L + CN) + ((4 + |Cw|) * L + CN) := by
        gcongr
        · exact hw.trans hCwL
        · exact hS.trans (mul_le_mul_of_nonneg_left hS₁ (by positivity))
    _ = _ := by ring

/-- **Pole-subtracted bounds for `ζ′` and `ζ′/ζ` right of the classical curve.** There are
`0 < β < 1` and `C` such that every `s ≠ 1` with `1 - β / log (|Im s| + 2) ≤ Re s` has
`ζ(s) ≠ 0`, `‖ζ′(s) + 1/(s - 1)²‖ ≤ C log² (|Im s| + 2)` and
`‖ζ′/ζ(s) + 1/(s - 1)‖ ≤ C log (|Im s| + 2)`. -/
theorem riemannZeta_deriv_logDeriv_bound :
    ∃ β C : ℝ, 0 < β ∧ β < 1 ∧ ∀ s : ℂ, s ≠ 1 →
      1 - β / Real.log (|s.im| + 2) ≤ s.re →
        riemannZeta s ≠ 0 ∧
          ‖deriv riemannZeta s + 1 / (s - 1) ^ 2‖ ≤ C * Real.log (|s.im| + 2) ^ 2 ∧
          ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤
            C * Real.log (|s.im| + 2) := by
  obtain ⟨c, hc, hzf⟩ := LFunctions.riemannZeta_zeroFreeRegion
  obtain ⟨Cw, hCw⟩ := riemannZeta_logDeriv_window
  obtain ⟨CN, hCN, hNear⟩ := exists_neg_re_logDeriv_riemannZeta_one_add_le
  set β := min (c / 4) (1 / 2)
  have hβ : 0 < β := lt_min (by positivity) one_half_pos
  obtain ⟨Cd, hCd⟩ := exists_norm_deriv_riemannZeta₀_le_mul_log_sq β
  set K := 3 + 1 / (2 * β)
  set CH := |Cw| + K * (4 + |Cw| + CN / Real.log 2)
  refine ⟨β, max Cd CH, hβ, (min_le_right _ _).trans_lt (by norm_num), fun s hs1 hs ↦ ?_⟩
  set L := Real.log (|s.im| + 2)
  have hL2 := log_two_le_log_abs_add_two s.im
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : 0 < L := hlog2.trans_le hL2
  have hζ : riemannZeta s ≠ 0 := by
    have hlog3 : 0 < Real.log (|s.im| + 3) := Real.log_pos (by linarith [abs_nonneg s.im])
    have hL3 := log_abs_add_three_le (x := s.im) (y := s.im) (by linarith)
    have : β / L ≤ c / Real.log (|s.im| + 3) := by
      rw [div_le_div_iff₀ hL hlog3]
      nlinarith [min_le_left (c / 4) (1 / 2)]
    exact hzf s hs1 (by linarith)
  refine ⟨hζ, ?_, ?_⟩
  · rw [deriv_riemannZeta_eq_neg_inv_sub_sq_add hs1, one_div, ← inv_pow, neg_add_cancel_comm]
    exact (hCd s hs).trans (by gcongr; exact le_max_left _ _)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right Cd CH) hL.le)
  have hCNL : CN ≤ CN / Real.log 2 * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hL2 hCN
  have hCHL : |Cw| * L + K * ((4 + |Cw|) * L + CN) ≤ CH * L := by
    have : 0 ≤ K := by positivity
    have := mul_le_mul_of_nonneg_left hCNL this
    linarith [show CH * L = |Cw| * L + K * ((4 + |Cw|) * L + CN / Real.log 2 * L) by ring]
  refine le_trans ?_ hCHL
  rcases le_or_gt (1 + (2 * L)⁻¹) s.re with hsη | hsη
  · have hη1 : (2 * L)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; linarith [Real.log_two_gt_d9]
    have h := norm_logDeriv_add_one_div_le_of_le_re hNear (by positivity) hη1 hsη
    rw [inv_inv] at h
    have hK : 1 ≤ K := by linarith [show 0 ≤ 1 / (2 * β) by positivity]
    have hX : 0 ≤ (4 + |Cw|) * L + CN := by positivity
    nlinarith [abs_nonneg Cw]
  · exact norm_logDeriv_add_one_div_le_of_re_lt hCw hNear hc hzf hβ (min_le_left _ _)
      (min_le_right _ _) hs1 hζ hs hsη

end TauCeti
