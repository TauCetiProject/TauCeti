/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.Complex.RemovableSingularity

/-!
# Taylor coefficients near a simple pole

Write `a k = (-1) ^ k / k ! * iteratedDeriv k Φ z` for the Taylor coefficients of `Φ` at `z` in the
variable `z - s`, so that `Φ (z - t) = ∑ k, a k * t ^ k`. If `Φ` is holomorphic on `ball z r` except
for a simple pole at `ρ ≠ z`, where `Φ s = c / (s - ρ) + h s` with `h` analytic, then the pole
governs the coefficients: `c / (s - ρ)` has coefficients `c / (z - ρ) ^ (k + 1)` exactly, and the
rest of `Φ` extends holomorphically to the ball, so that by Cauchy's estimates its coefficients are
`O (r' ^ (-k))` for every `r' < r`. When the pole is closer to `z` than `r'`, the coefficients of
`Φ` are therefore eventually at least half as large as those of the pole.

This is the comparison step of Darboux's method in the case of a pole strictly inside the disc of
holomorphy. In the proof of a Landau theorem it turns a pole of a Laplace transform into a lower
bound for one of its Taylor coefficients at a far-out point.

## Main results

* `TauCeti.Complex.exists_forall_norm_taylorCoeff_sub_le_of_eventuallyEq`: if
  `Φ s = c / (s - ρ) + g s` near `z` with `g` holomorphic on `ball z r`, then
  `‖a k - c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k` for all `k`.
* `TauCeti.Complex.exists_forall_norm_taylorCoeff_sub_le_of_simple_pole`: the same bound for `Φ`
  holomorphic on `ball z r \ {ρ}` with a simple pole at `ρ`.
* `TauCeti.Complex.eventually_le_norm_taylorCoeff_of_simple_pole`: for `‖z - ρ‖ < r'`,
  eventually `‖c‖ / 2 / ‖z - ρ‖ ^ (k + 1) ≤ ‖a k‖`.
* `TauCeti.Complex.eventually_le_re_taylorCoeff_of_simple_pole`: for real `ρ < z` and `0 < re c`,
  eventually `re c / 2 / (z - ρ) ^ (k + 1) ≤ re (a k)`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, section 9 (Darboux's method).
-/

public section

open Filter Metric Set
open scoped Nat Topology

namespace TauCeti.Complex

/-- For `0 < d < r'`, the sequence `M / r' ^ k` is eventually at most `δ / d ^ (k + 1)`. -/
private theorem eventually_div_pow_le_div_pow (M : ℝ) {δ d r' : ℝ} (hδ : 0 < δ) (hd : 0 < d)
    (hdr : d < r') : ∀ᶠ k : ℕ in atTop, M / r' ^ k ≤ δ / d ^ (k + 1) := by
  have hr' : 0 < r' := hd.trans hdr
  have hlim : Tendsto (fun k : ℕ ↦ M * d * (d / r') ^ k) atTop (𝓝 (M * d * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le hr'.le)
      ((div_lt_one hr').2 hdr)).const_mul _
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually_le_const hδ] with k hk
  have hrk : 0 < r' ^ k := pow_pos hr' k
  rw [div_le_div_iff₀ hrk (pow_pos hd _)]
  calc M * d ^ (k + 1) = M * d * (d / r') ^ k * r' ^ k := by
        rw [div_pow, pow_succ]
        field_simp
    _ ≤ δ * r' ^ k := mul_le_mul_of_nonneg_right hk hrk.le

/-- A sequence within `M / r' ^ k` of `c / w ^ (k + 1)`, `‖w‖ < r'`, is eventually at least half as
large as `c / w ^ (k + 1)`. -/
private theorem eventually_le_norm_of_norm_sub_div_pow_le {a : ℕ → ℂ} {w c : ℂ} {M r' : ℝ}
    (ha : ∀ k, ‖a k - c / w ^ (k + 1)‖ ≤ M / r' ^ k) (hw : ‖w‖ < r') :
    ∀ᶠ k : ℕ in atTop, ‖c‖ / 2 / ‖w‖ ^ (k + 1) ≤ ‖a k‖ := by
  rcases eq_or_ne w 0 with rfl | hw0
  · exact .of_forall fun k ↦ by simp
  rcases eq_or_ne c 0 with rfl | hc
  · exact .of_forall fun k ↦ by simp
  filter_upwards [eventually_div_pow_le_div_pow M (half_pos (norm_pos_iff.2 hc))
    (norm_pos_iff.2 hw0) hw] with k hk
  have h1 := norm_sub_norm_le (c / w ^ (k + 1)) (a k)
  rw [norm_sub_rev, norm_div, norm_pow] at h1
  have h2 : ‖c‖ / ‖w‖ ^ (k + 1) = ‖c‖ / 2 / ‖w‖ ^ (k + 1) + ‖c‖ / 2 / ‖w‖ ^ (k + 1) := by ring
  linarith [ha k]

/-- A sequence within `M / r' ^ k` of `c / x ^ (k + 1)`, with `0 < x < r'` real and `0 < re c`, has
real part eventually at least half that of `c / x ^ (k + 1)`. -/
private theorem eventually_le_re_of_norm_sub_div_pow_le {a : ℕ → ℂ} {c : ℂ} {x M r' : ℝ}
    (ha : ∀ k, ‖a k - c / (x : ℂ) ^ (k + 1)‖ ≤ M / r' ^ k) (hc : 0 < c.re) (hx : 0 < x)
    (hxr : x < r') : ∀ᶠ k : ℕ in atTop, c.re / 2 / x ^ (k + 1) ≤ (a k).re := by
  filter_upwards [eventually_div_pow_le_div_pow M (half_pos hc) hx hxr] with k hk
  have hre : (c / (x : ℂ) ^ (k + 1)).re = c.re / x ^ (k + 1) := by
    rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  have h1 := Complex.abs_re_le_norm (a k - c / (x : ℂ) ^ (k + 1))
  rw [Complex.sub_re, hre, abs_le] at h1
  have h2 : c.re / x ^ (k + 1) = c.re / 2 / x ^ (k + 1) + c.re / 2 / x ^ (k + 1) := by ring
  linarith [ha k, h1.1]

variable {Φ g h : ℂ → ℂ} {z ρ c : ℂ} {r r' : ℝ}

/-- **Taylor coefficients of a holomorphic function plus a simple pole.** If
`Φ s = c / (s - ρ) + g s` near `z ≠ ρ`, with `g` holomorphic on `ball z r`, then for `0 < r' < r`
the Taylor coefficients `(-1) ^ k / k ! * iteratedDeriv k Φ z` of `Φ` at `z` differ from those of
the pole, `c / (z - ρ) ^ (k + 1)`, by at most `M / r' ^ k`. -/
theorem exists_forall_norm_taylorCoeff_sub_le_of_eventuallyEq
    (hg : DifferentiableOn ℂ g (ball z r)) (hΦ : Φ =ᶠ[𝓝 z] fun s ↦ c / (s - ρ) + g s)
    (hzρ : z ≠ ρ) (hr' : 0 < r') (hrr : r' < r) :
    ∃ M, ∀ k : ℕ,
      ‖(-1) ^ k / (k ! : ℂ) * iteratedDeriv k Φ z - c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k := by
  obtain ⟨C, hC⟩ := (isCompact_sphere z r').exists_bound_of_continuousOn
    (hg.continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hrr)))
  refine ⟨C, fun k ↦ ?_⟩
  have hgz : ContDiffAt ℂ k g z :=
    (hg.analyticAt (ball_mem_nhds z (hr'.trans hrr))).contDiffAt
  have hpz : ContDiffAt ℂ k (fun s : ℂ ↦ c / (s - ρ)) z :=
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.2 hzρ)
  have hpole' : iteratedDeriv k (fun s : ℂ ↦ c / (s - ρ)) z =
      (-1) ^ k * (k ! : ℂ) * c / (z - ρ) ^ (k + 1) := by
    rw [show iteratedDeriv k (fun s : ℂ ↦ c / (s - ρ)) z =
      iteratedDeriv k (fun y : ℂ ↦ c / y) (z - ρ) from
      congrFun (iteratedDeriv_comp_sub_const (n := k) (f := fun y : ℂ ↦ c / y) (s := ρ)) z,
      iteratedDeriv_const_div]
  have hsplit : iteratedDeriv k Φ z =
      (-1) ^ k * (k ! : ℂ) * c / (z - ρ) ^ (k + 1) + iteratedDeriv k g z := by
    rw [hΦ.iteratedDeriv_eq k, ← hpole']
    exact iteratedDeriv_add hpz hgz
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have hone : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  have hpole : (-1 : ℂ) ^ k / (k ! : ℂ) * ((-1) ^ k * (k ! : ℂ) * c / (z - ρ) ^ (k + 1)) =
      c / (z - ρ) ^ (k + 1) := by
    calc _ = (-1 : ℂ) ^ k * (-1) ^ k * ((k ! : ℂ) / (k ! : ℂ)) * (c / (z - ρ) ^ (k + 1)) := by ring
      _ = _ := by rw [hone, div_self hk, one_mul, one_mul]
  have hD := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr'
    (hg.diffContOnCl_ball (closedBall_subset_ball hrr)) hC
  rw [hsplit, mul_add, hpole, add_sub_cancel_left, norm_mul, norm_div, norm_pow, norm_neg,
    norm_one, one_pow, Complex.norm_natCast, one_div, inv_mul_le_iff₀ (by positivity)]
  calc ‖iteratedDeriv k g z‖ ≤ k ! * C / r' ^ k := hD
    _ = k ! * (C / r' ^ k) := by ring

/-- **Taylor coefficients near a simple pole.** Let `Φ` be holomorphic on `ball z r \ {ρ}`, with
`Φ s = c / (s - ρ) + h s` near `ρ ≠ z` for a function `h` analytic at `ρ`. Then for `0 < r' < r`
the Taylor coefficients `(-1) ^ k / k ! * iteratedDeriv k Φ z` of `Φ` at `z` differ from
`c / (z - ρ) ^ (k + 1)` by at most `M / r' ^ k`. -/
theorem exists_forall_norm_taylorCoeff_sub_le_of_simple_pole
    (hΦ : DifferentiableOn ℂ Φ (ball z r \ {ρ})) (hh : AnalyticAt ℂ h ρ)
    (hΦh : ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s) (hzρ : z ≠ ρ) (hr' : 0 < r')
    (hrr : r' < r) :
    ∃ M, ∀ k : ℕ,
      ‖(-1) ^ k / (k ! : ℂ) * iteratedDeriv k Φ z - c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k := by
  have hcod : ({ρ} : Set ℂ)ᶜ ∈ codiscreteWithin (ball z r) := by
    refine mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun x _ ↦
      mem_of_superset ?_ subset_union_left
    rcases eq_or_ne x ρ with rfl | hx
    · exact self_mem_nhdsWithin
    · exact mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hx)
  obtain ⟨g, hg, hfg⟩ := exists_differentiableOn_eqOn_of_analyticAt_nhdsNE hcod
    (f := fun s ↦ Φ s - c / (s - ρ))
    (hΦ.sub fun s hs ↦ (DifferentiableAt.div (differentiableAt_const c)
      (differentiableAt_id.sub (differentiableAt_const ρ))
      (sub_ne_zero.2 hs.2)).differentiableWithinAt)
    (by
      rintro a ⟨-, ha⟩
      obtain rfl : a = ρ := ha
      exact ⟨h, hh, hΦh.mono fun s hs ↦ by
        change Φ s - c / (s - a) = h s
        rw [hs, add_sub_cancel_left]⟩)
  refine exists_forall_norm_taylorCoeff_sub_le_of_eventuallyEq hg ?_ hzρ hr' hrr
  filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds
    ⟨mem_ball_self (hr'.trans hrr), hzρ⟩] with s hs
  have h3 : Φ s - c / (s - ρ) = g s := hfg hs
  rw [← h3, add_sub_cancel]

/-- **A simple pole forces large Taylor coefficients.** Let `Φ` be holomorphic on
`ball z r \ {ρ}`, with `Φ s = c / (s - ρ) + h s` near `ρ` and `h` analytic at `ρ`. If
`‖z - ρ‖ < r' < r`, then eventually
`‖c‖ / 2 / ‖z - ρ‖ ^ (k + 1) ≤ ‖(-1) ^ k / k ! * iteratedDeriv k Φ z‖`. For `c = 0` or `z = ρ` the
left-hand side is `0`. -/
theorem eventually_le_norm_taylorCoeff_of_simple_pole
    (hΦ : DifferentiableOn ℂ Φ (ball z r \ {ρ})) (hh : AnalyticAt ℂ h ρ)
    (hΦh : ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s) (hd : ‖z - ρ‖ < r') (hrr : r' < r) :
    ∀ᶠ k : ℕ in atTop,
      ‖c‖ / 2 / ‖z - ρ‖ ^ (k + 1) ≤ ‖(-1) ^ k / (k ! : ℂ) * iteratedDeriv k Φ z‖ := by
  rcases eq_or_ne z ρ with rfl | hzρ
  · exact .of_forall fun k ↦ by
      rw [sub_self, norm_zero, zero_pow k.succ_ne_zero, div_zero]
      exact norm_nonneg _
  obtain ⟨M, hM⟩ := exists_forall_norm_taylorCoeff_sub_le_of_simple_pole hΦ hh hΦh hzρ
    ((norm_nonneg _).trans_lt hd) hrr
  exact eventually_le_norm_of_norm_sub_div_pow_le hM hd

/-- **A real simple pole with positive residue forces large positive Taylor coefficients.** Let
`y < x` be real and let `Φ` be holomorphic on `ball x r \ {y}`, with `Φ s = c / (s - y) + h s` near
`y`, `h` analytic at `y` and `0 < re c`. If `x - y < r' < r`, then eventually
`re c / 2 / (x - y) ^ (k + 1) ≤ re ((-1) ^ k / k ! * iteratedDeriv k Φ x)`. -/
theorem eventually_le_re_taylorCoeff_of_simple_pole {x y : ℝ}
    (hΦ : DifferentiableOn ℂ Φ (ball (x : ℂ) r \ {(y : ℂ)})) (hh : AnalyticAt ℂ h y)
    (hΦh : ∀ᶠ s in 𝓝[≠] (y : ℂ), Φ s = c / (s - y) + h s) (hc : 0 < c.re) (hyx : y < x)
    (hd : x - y < r') (hrr : r' < r) :
    ∀ᶠ k : ℕ in atTop,
      c.re / 2 / (x - y) ^ (k + 1) ≤ ((-1) ^ k / (k ! : ℂ) * iteratedDeriv k Φ x).re := by
  have hxy : (x : ℂ) ≠ y := by exact_mod_cast hyx.ne'
  obtain ⟨M, hM⟩ := exists_forall_norm_taylorCoeff_sub_le_of_simple_pole hΦ hh hΦh hxy
    ((sub_pos.2 hyx).trans hd) hrr
  simp_rw [← Complex.ofReal_sub] at hM
  exact eventually_le_re_of_norm_sub_div_pow_le hM hc (sub_pos.2 hyx) hd

end TauCeti.Complex
