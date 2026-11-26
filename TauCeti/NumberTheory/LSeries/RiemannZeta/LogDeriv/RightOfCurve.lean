/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import TauCeti.Algebra.Order.GroupWithZero.Basic
import TauCeti.Analysis.SpecialFunctions.Log.TwoAdd
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
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

* `TauCeti.riemannZeta_deriv_logDeriv_bound`: nonvanishing and the two pole-subtracted bounds on
  the region `1 - β / L ≤ Re s`.
* `TauCeti.exists_neg_logDeriv_riemannZeta_eq_add_and_norm_le`: `-ζ′/ζ = G + 1/(s - 1)` with `G`
  holomorphic on an open set containing `1 - c / log (|Im s| + 3) ≤ Re s` and
  `‖G(s)‖ ≤ C log (|Im s| + 3)` there.

## Implementation notes

The bound for `ζ′` is the Cauchy estimate `TauCeti.exists_norm_deriv_riemannZeta₀_le_mul_log_sq`
for the entire function `riemannZeta₀ = ζ - 1/(s - 1)`, which holds right of every curve
`Re s = 1 - A / L`. No zero-free region enters.

For `ζ′/ζ` put `η = 1 / (2L)` and `s₁ = 1 + η + i Im s`. Comparing Dirichlet series with the real
point `1 + η` and the pole bound at `1` bound `ζ′/ζ` by `2L + O(1)` on `Re s ≥ 1 + η`, and
`1/(s - 1)` by `2L` there. Otherwise subtract the window expansions
`TauCeti.riemannZeta_logDeriv_window` at `s` and `s₁`, which share their window of zeros. By the
zero-free region `TauCeti.LFunctions.riemannZeta_zeroFreeRegion` every window zero `ρ` has
`Re ρ ≤ 1 - 2β / L`, so `‖1/(s - ρ) - 1/(s₁ - ρ)‖ ≤ (2 + 1/(2β)) Re 1/(s₁ - ρ)`, and the sum of
the `Re 1/(s₁ - ρ) ≥ 0` is at most the window sum at `s₁`, which is `O(L)`. The window sums at
`s` and `s₁` are `Finset` sums over the zeros of `ζ` in the disc of radius `4` about `2 + i Im s`
(`TauCeti.finsum_window_eq_sum_riemannZetaZerosClosedBall`). The choice `η = 1/(2L)` keeps
`Re s₁ ≤ 2` at every height, so no compactness argument is needed at bounded height.

For `TauCeti.exists_neg_logDeriv_riemannZeta_eq_add_and_norm_le`, the region
`1 - β / log (|Im s| + 3) ≤ Re s` lies in the open set strictly right of the curve, and on it
`-ζ′/ζ - 1/(s - 1)` is the negative logarithmic derivative of the entire function `(s - 1) ζ(s)`
(`DirichletCharacter.LFunctionTrivChar₁` at level one), which is holomorphic across `s = 1`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Theorem 6.7.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§3.9–3.11.
* `ZetaDerivUpperBnd`, `LogDerivZetaBnd` and `LogDerivZetaBndUnif99` in A. Kontorovich, T. Tao
  et al., *PrimeNumberTheoremAnd*, file `PrimeNumberTheoremAnd/ZetaBounds.lean`, for bounded
  real parts and `|Im s|` large.
-/

public section

open Complex

namespace TauCeti

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

/-- The comparison of the window sums at `s` and at `s₁ = 1 + η + i Im s`, with weights in `ℕ`,
when every point of `W` lies on `Re z ≤ 1 - 2a`. -/
private lemma norm_sum_div_sub_sub_sum_div_sub_le {s s₁ : ℂ} {a η : ℝ} (ha : 0 < a) (hη : 0 < η)
    (hs₁re : s₁.re = 1 + η) (hs₁im : s₁.im = s.im) (hs : 1 - a ≤ s.re) (hs' : s.re < 1 + η)
    {W : Finset ℂ} (hW : ∀ z ∈ W, z.re ≤ 1 - 2 * a) (m : ℂ → ℕ) :
    ‖∑ z ∈ W, (m z : ℂ) / (s - z) - ∑ z ∈ W, (m z : ℂ) / (s₁ - z)‖ ≤
      (2 + η / a) * ‖∑ z ∈ W, (m z : ℂ) / (s₁ - z)‖ := by
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ z ∈ W, ‖(m z : ℂ) / (s - z) - (m z : ℂ) / (s₁ - z)‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ W, (2 + η / a) * ((m z : ℂ) / (s₁ - z)).re := by
      refine Finset.sum_le_sum fun z hz ↦ ?_
      have hpt := norm_one_div_sub_sub_one_div_sub_le ha hη hs₁re hs₁im hs hs' (hW z hz)
      rw [div_eq_mul_one_div (m z : ℂ), div_eq_mul_one_div (m z : ℂ), ← mul_sub, norm_mul,
        norm_natCast, ← ofReal_natCast, re_ofReal_mul]
      calc _ ≤ (m z : ℝ) * ((2 + η / a) * (1 / (s₁ - z)).re) :=
            mul_le_mul_of_nonneg_left hpt (Nat.cast_nonneg _)
        _ = _ := by ring
    _ = (2 + η / a) * (∑ z ∈ W, (m z : ℂ) / (s₁ - z)).re := by rw [← Finset.mul_sum, re_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (re_le_norm _) (by positivity)

/-- With a zero-free width `c` in the normalization `log (|Im s| + 3)` and `β ≤ c / 4`, `ζ` has
no zero on `1 - β / log (|Im s| + 2) ≤ Re s`. -/
private lemma riemannZeta_ne_zero_of_one_sub_div_le {c β : ℝ}
    (hzf : ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0)
    (hβc : β ≤ c / 4) {s : ℂ} (hs : 1 - β / Real.log (|s.im| + 2) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero
  set L := Real.log (|s.im| + 2)
  have hL : 0 < L := (Real.log_pos one_lt_two).trans_le (Real.log_two_le_log_add_two (abs_nonneg _))
  rcases le_or_gt β 0 with hβ | hβ
  · exact riemannZeta_ne_zero_of_one_le_re (by linarith [div_nonpos_of_nonpos_of_nonneg hβ hL.le])
  have hlog3 : 0 < Real.log (|s.im| + 3) := Real.log_pos (by linarith [abs_nonneg s.im])
  have hL3 : Real.log (|s.im| + 3) ≤ 2 * L := by
    have := Real.log_add_two_le_two_mul_log_add_two (abs_nonneg s.im)
      (by positivity : 0 ≤ |s.im| + 1) (by linarith)
    rwa [add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] at this
  have : β / L ≤ c / Real.log (|s.im| + 3) := by
    rw [div_le_div_iff₀ hL hlog3]
    nlinarith
  exact hzf s hs1 (by linarith)

/-- With a zero-free width `c` in the normalization `log (|Im s| + 3)` and `β ≤ c / 4`, every
zero `z` of `ζ` with `|Im z - t| ≤ 1` has `Re z ≤ 1 - 2β / log (|t| + 2)`. -/
private lemma re_le_of_riemannZeta_eq_zero {c β : ℝ}
    (hzf : ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0)
    (hβc : β ≤ c / 4) {t : ℝ} {z : ℂ} (hzim : |z.im - t| ≤ 1) (hzζ : riemannZeta z = 0) :
    z.re ≤ 1 - 2 * (β / Real.log (|t| + 2)) := by
  have hLt : 0 < Real.log (|t| + 2) :=
    (Real.log_pos one_lt_two).trans_le (Real.log_two_le_log_add_two (abs_nonneg t))
  have hβ : 2 * (β / Real.log (|t| + 2)) ≤ c / (2 * Real.log (|t| + 2)) := by
    rw [mul_div_assoc', div_le_div_iff₀ hLt (by positivity)]
    nlinarith
  suffices z.re ≤ 1 - c / (2 * Real.log (|t| + 2)) by linarith
  rcases le_or_gt c 0 with hc | hc
  · -- there are no zeros on `1 ≤ Re z`, and the width is not positive
    have hz1 : z.re < 1 := lt_of_not_ge fun h ↦ riemannZeta_ne_zero_of_one_le_re h hzζ
    have : c / (2 * Real.log (|t| + 2)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc (by positivity)
    linarith
  have hz1' : z ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hzζ
  have hlt := lt_of_not_ge fun h ↦ hzf z hz1' h hzζ
  have hLz : Real.log (|z.im| + 3) ≤ 2 * Real.log (|t| + 2) := by
    have := Real.log_add_two_le_two_mul_log_add_two (abs_nonneg t)
      (by positivity : 0 ≤ |z.im| + 1)
      (by linarith [abs_sub_abs_le_abs_sub z.im t, (abs_le.mp hzim).2])
    rwa [add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] at this
  have hlz : 0 < Real.log (|z.im| + 3) := Real.log_pos (by linarith [abs_nonneg z.im])
  have := div_le_div_of_nonneg_left hc.le hlz hLz
  linarith

/-- **The window comparison.** Let `Cw` be a constant of the window form
`TauCeti.riemannZeta_logDeriv_window`, `CN` one of the pole bound at `1` and `c` a zero-free
width. Write `L = log (|Im s| + 2)`. For `0 < β ≤ min (c / 4) (1 / 2)`, every `s ≠ 1` with
`1 - β / L ≤ Re s < 1 + 1/(2L)` has
`‖ζ′/ζ(s) + 1/(s - 1)‖ ≤ |Cw| L + (3 + 1/(2β)) ((4 + |Cw|) L + CN)`. -/
private lemma norm_logDeriv_add_one_div_le_of_re_lt {Cw CN c β : ℝ}
    (hCw : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ |z.im - s.im| ≤ 1 ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        Cw * Real.log (|s.im| + 2))
    (hNear : ∀ {η : ℝ}, 0 < η → η ≤ 1 → -(logDeriv riemannZeta (1 + η)).re ≤ η⁻¹ + CN)
    (hzf : ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0)
    (hβ : 0 < β) (hβc : β ≤ c / 4) (hβ2 : β ≤ 1 / 2) {s : ℂ} (hs1 : s ≠ 1)
    (hs : 1 - β / Real.log (|s.im| + 2) ≤ s.re)
    (hsη : s.re < 1 + (2 * Real.log (|s.im| + 2))⁻¹) :
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤
      |Cw| * Real.log (|s.im| + 2) +
        (3 + 1 / (2 * β)) * ((4 + |Cw|) * Real.log (|s.im| + 2) + CN) := by
  set t := s.im with ht
  set L := Real.log (|t| + 2)
  have hL : 1 / 2 ≤ L := by
    linarith [Real.log_two_le_log_add_two (abs_nonneg t), Real.log_two_gt_d9]
  set η := (2 * L)⁻¹
  have hη : 0 < η := by positivity
  have hη1 : η ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
  have hβL : β / L ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  set s₁ : ℂ := ((1 + η : ℝ) : ℂ) + t * I
  have hs₁re : s₁.re = 1 + η := by simp [s₁]
  have hs₁im : s₁.im = t := by simp [s₁]
  have hs₁1 : s₁ ≠ 1 := fun h ↦ by rw [h, one_re] at hs₁re; linarith
  have hζ₁ : riemannZeta s₁ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
  -- both window sums run over the window zeros in the disc of radius `4` about `2 + i t`
  classical
  set W := {z ∈ riemannZetaZerosClosedBall (2 + t * I) 4 |
    0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ riemannZeta z = 0}
  set m : ℂ → ℕ := fun z ↦ (analyticOrderAt riemannZeta z).toNat
  have hw := hCw s (by linarith) (by linarith) hs1
    (riemannZeta_ne_zero_of_one_sub_div_le hzf hβc hs)
  have hw₁ := hCw s₁ (by linarith) (by linarith) hs₁1 hζ₁
  rw [← ht, finsum_window_eq_sum_riemannZetaZerosClosedBall t fun z ↦ (m z : ℂ) / (s - z)] at hw
  rw [hs₁im, finsum_window_eq_sum_riemannZetaZerosClosedBall t fun z ↦ (m z : ℂ) / (s₁ - z)]
    at hw₁
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
    obtain ⟨-, -, -, hzim, hzζ⟩ := Finset.mem_filter.mp hz
    exact re_le_of_riemannZeta_eq_zero hzf hβc hzim hzζ
  have hS := norm_sum_div_sub_sub_sum_div_sub_le (div_pos hβ (by linarith)) hη hs₁re hs₁im
    (by linarith) hsη hzero m
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
  have hL2 := Real.log_two_le_log_add_two (abs_nonneg s.im)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : 0 < L := hlog2.trans_le hL2
  refine ⟨riemannZeta_ne_zero_of_one_sub_div_le hzf (min_le_left _ _) hs, ?_, ?_⟩
  · rw [deriv_riemannZeta_eq_neg_inv_sub_sq_add hs1, one_div, ← inv_pow, neg_add_cancel_comm]
    exact (hCd s hs).trans (by gcongr; exact le_max_left _ _)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right Cd CH) hL.le)
  have hCNL : CN ≤ CN / Real.log 2 * L := le_div_mul_of_le hCN hlog2 hL2
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
  · exact norm_logDeriv_add_one_div_le_of_re_lt hCw hNear hzf hβ (min_le_left _ _)
      (min_le_right _ _) hs1 hs hsη

/-- **The logarithmic derivative of `ζ` in the classical zero-free region.** There are `c > 0`,
`C`, an open set `U` containing `R_c = {s : 1 - c / log (|Im s| + 3) ≤ Re s}`, and `G` holomorphic
on `U`, such that every `s ∈ R_c` other than `1` has `ζ(s) ≠ 0` and `-ζ′/ζ(s) = G(s) + 1/(s - 1)`,
and `‖G(s)‖ ≤ C log (|Im s| + 3)` on `R_c`. This is the shape of the hypotheses of Ingham's
transfer theorem `TauCeti.LSeries.norm_sum_sub_mul_le_of_zeroFreeRegion`. -/
theorem exists_neg_logDeriv_riemannZeta_eq_add_and_norm_le :
    ∃ c C : ℝ, 0 < c ∧ ∃ U : Set ℂ, IsOpen U ∧
      {s : ℂ | 1 - c / Real.log (|s.im| + 3) ≤ s.re} ⊆ U ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
        (∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 3) ≤ s.re →
          riemannZeta s ≠ 0 ∧ -logDeriv riemannZeta s = G s + 1 / (s - 1)) ∧
        ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → ‖G s‖ ≤ C * Real.log (|s.im| + 3) := by
  obtain ⟨β, C, hβ, -, hζ⟩ := riemannZeta_deriv_logDeriv_bound
  set U : Set ℂ := {s | 1 - β / Real.log (|s.im| + 2) < s.re}
  have hlog (s : ℂ) : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith [abs_nonneg s.im])
  -- the region `R_β` lies strictly right of the curve of `riemannZeta_deriv_logDeriv_bound`
  have hRU {s : ℂ} (hs : 1 - β / Real.log (|s.im| + 3) ≤ s.re) : s ∈ U := by
    have : β / Real.log (|s.im| + 3) < β / Real.log (|s.im| + 2) :=
      div_lt_div_of_pos_left hβ (hlog s) (Real.log_lt_log (by positivity) (by linarith))
    exact (show 1 - β / Real.log (|s.im| + 2) < s.re by linarith)
  have hζU {s : ℂ} (hs : s ∈ U) : riemannZeta s ≠ 0 := by
    rcases eq_or_ne s 1 with rfl | hs1
    · exact riemannZeta_one_ne_zero
    · exact (hζ s hs1 (le_of_lt hs)).1
  set G : ℂ → ℂ := fun s ↦ -logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) s
  have hGU : DifferentiableOn ℂ G U := fun s hs ↦ by
    have hd := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
    exact ((((hd.analyticAt s).deriv).differentiableAt.div (hd s)
      (DirichletCharacter.LFunctionTrivChar₁_one_ne_zero (hζU hs))).neg).differentiableWithinAt
  have hGeq {s : ℂ} (hs1 : s ≠ 1) (hs : s ∈ U) :
      G s = -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1)) := by
    simp only [G]
    rw [one_div, ← logDeriv_apply, logDeriv_riemannZeta_add_inv_sub_one hs1 (hζU hs)]
  refine ⟨β, max (max C 0) (‖G 1‖ / Real.log 3), hβ, U, ?_, fun s hs ↦ hRU hs, G, hGU,
    fun s hs1 hs ↦ ⟨hζU (hRU hs), ?_⟩, fun s hs ↦ ?_⟩
  · exact isOpen_lt (continuous_const.sub (continuous_const.div
      (((continuous_abs.comp continuous_im).add continuous_const).log fun s ↦ by dsimp; positivity)
      fun s ↦ (hlog s).ne')) continuous_re
  · rw [hGeq hs1 (hRU hs), logDeriv_apply]
    ring
  rcases eq_or_ne s 1 with rfl | hs1
  · have : Real.log 3 ≤ Real.log (|(1 : ℂ).im| + 3) := by simp
    calc ‖G 1‖ = ‖G 1‖ / Real.log 3 * Real.log 3 :=
          (div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne').symm
      _ ≤ _ := mul_le_mul (le_max_right _ _) this (Real.log_nonneg (by norm_num)) (by positivity)
  rw [hGeq hs1 (hRU hs), norm_neg]
  calc _ ≤ C * Real.log (|s.im| + 2) := (hζ s hs1 (le_of_lt (hRU hs))).2.2
    _ ≤ max C 0 * Real.log (|s.im| + 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hlog s).le
    _ ≤ max (max C 0) (‖G 1‖ / Real.log 3) * Real.log (|s.im| + 3) :=
        mul_le_mul (le_max_left _ _) (Real.log_le_log (by positivity) (by linarith)) (hlog s).le
          (by positivity)

end TauCeti
