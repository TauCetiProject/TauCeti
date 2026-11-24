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
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.SpecificLimits.Basic

/-!
# Taylor coefficients near a simple pole

Let `Φ` be holomorphic on `ball z r` except for a simple pole at `ρ ≠ z`, where
`Φ s = c / (s - ρ) + h s` with `h` analytic. The pole governs the Taylor coefficients
`iteratedDeriv k Φ z / k !` of `Φ` at `z`: those of `c / (s - ρ)` are
`(-1) ^ k * c / (z - ρ) ^ (k + 1)` exactly, and the rest of `Φ` extends holomorphically to the
ball, so that by Cauchy's estimates its coefficients are `O (r' ^ (-k))` for every `r' < r`. When
the pole is inside the ball, the coefficients of `Φ` are therefore eventually at least half as
large as those of the pole.

The sign `(-1) ^ k` disappears in the variable `t = z - s`: the coefficients of `t ↦ Φ (z - t)`
are `(-1) ^ k * (iteratedDeriv k Φ z / k !)`, and those of the pole are `c / (z - ρ) ^ (k + 1)`.
The statement about real parts is made for these.

This is the comparison step of Darboux's method in the case of a pole strictly inside the disc of
holomorphy. In the proof of a Landau theorem it turns a pole of a Laplace transform into a lower
bound for one of its Taylor coefficients at a far-out point.

## Main results

* `TauCeti.Complex.exists_forall_norm_iteratedDeriv_div_factorial_sub_le_of_eventuallyEq`: if
  `Φ s = c / (s - ρ) + g s` near `z` with `g` holomorphic on `ball z r`, then
  `‖iteratedDeriv k Φ z / k ! - (-1) ^ k * c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k` for all `k`.
* `TauCeti.Complex.exists_forall_norm_iteratedDeriv_div_factorial_sub_le_of_simple_pole`: the same
  bound for `Φ` holomorphic on `ball z r \ {ρ}` with a simple pole at `ρ`.
* `TauCeti.Complex.eventually_le_norm_iteratedDeriv_div_factorial_of_simple_pole`: for
  `‖z - ρ‖ < r`, eventually `‖c‖ / 2 / ‖z - ρ‖ ^ (k + 1) ≤ ‖iteratedDeriv k Φ z / k !‖`.
* `TauCeti.Complex.eventually_le_re_neg_one_pow_mul_iteratedDeriv_div_factorial_of_simple_pole`:
  for real `ρ < z` and `0 < re c`, eventually
  `re c / 2 / (z - ρ) ^ (k + 1) ≤ re ((-1) ^ k * (iteratedDeriv k Φ z / k !))`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, section 9 (Darboux's method).
* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet L-functions
  (<https://github.com/leanprover-community/riemann-hypothesis>), `Deduction.landau_pole_asym` in
  `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauPoleAsym.lean`: the
  source of the simple-pole statements (the comparison bound `M / r' ^ k` and the two lower bounds
  with the factor `1 / 2`). That development was not consulted; the proofs here are independent
  of it.
-/

public section

open Filter Metric Set
open scoped Nat Topology

namespace TauCeti.Complex

/-- Moving the sign `(-1) ^ k` from one term of a difference to the other does not change its
norm. -/
private theorem norm_neg_one_pow_mul_sub (k : ℕ) (u v : ℂ) :
    ‖(-1) ^ k * u - v‖ = ‖u - (-1) ^ k * v‖ := by
  have h : (-1 : ℂ) ^ k * u - v = (-1) ^ k * (u - (-1) ^ k * v) := by
    rw [mul_sub, ← mul_assoc, ← mul_pow]
    simp
  rw [h, norm_mul]
  simp

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
the Taylor coefficients `iteratedDeriv k Φ z / k !` of `Φ` at `z` differ from those of the pole,
`(-1) ^ k * c / (z - ρ) ^ (k + 1)`, by at most `M / r' ^ k`. -/
theorem exists_forall_norm_iteratedDeriv_div_factorial_sub_le_of_eventuallyEq
    (hg : DifferentiableOn ℂ g (ball z r)) (hΦ : Φ =ᶠ[𝓝 z] fun s ↦ c / (s - ρ) + g s)
    (hzρ : z ≠ ρ) (hr' : 0 < r') (hrr : r' < r) :
    ∃ M, ∀ k : ℕ,
      ‖iteratedDeriv k Φ z / (k ! : ℂ) - (-1) ^ k * c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k := by
  obtain ⟨C, hC⟩ := (isCompact_sphere z r').exists_bound_of_continuousOn
    (hg.continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hrr)))
  refine ⟨C, fun k ↦ ?_⟩
  have hgz : ContDiffAt ℂ k g z :=
    (hg.analyticAt (ball_mem_nhds z (hr'.trans hrr))).contDiffAt
  have hpz : ContDiffAt ℂ k (fun s : ℂ ↦ c / (s - ρ)) z :=
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.2 hzρ)
  have hshift : iteratedDeriv k (fun s : ℂ ↦ c / (s - ρ)) z =
      iteratedDeriv k (fun y : ℂ ↦ c / y) (z - ρ) :=
    congrFun (iteratedDeriv_comp_sub_const (n := k) (f := fun y : ℂ ↦ c / y) (s := ρ)) z
  have hsplit : iteratedDeriv k Φ z =
      (-1) ^ k * (k ! : ℂ) * c / (z - ρ) ^ (k + 1) + iteratedDeriv k g z := by
    rw [hΦ.iteratedDeriv_eq k, ← iteratedDeriv_const_div, ← hshift]
    exact iteratedDeriv_add hpz hgz
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have hw : (z - ρ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hzρ)
  have hdiff : iteratedDeriv k Φ z / (k ! : ℂ) - (-1) ^ k * c / (z - ρ) ^ (k + 1) =
      iteratedDeriv k g z / (k ! : ℂ) := by
    rw [hsplit]
    field_simp
    ring
  rw [hdiff, norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  calc ‖iteratedDeriv k g z‖ ≤ k ! * C / r' ^ k :=
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr'
          (hg.diffContOnCl_ball (closedBall_subset_ball hrr)) hC
    _ = C / r' ^ k * k ! := by ring

/-- **Taylor coefficients near a simple pole.** Let `Φ` be holomorphic on `ball z r \ {ρ}`, with
`Φ s = c / (s - ρ) + h s` near `ρ ≠ z` for a function `h` analytic at `ρ`. Then for `0 < r' < r`
the Taylor coefficients `iteratedDeriv k Φ z / k !` of `Φ` at `z` differ from
`(-1) ^ k * c / (z - ρ) ^ (k + 1)` by at most `M / r' ^ k`. -/
theorem exists_forall_norm_iteratedDeriv_div_factorial_sub_le_of_simple_pole
    (hΦ : DifferentiableOn ℂ Φ (ball z r \ {ρ})) (hh : AnalyticAt ℂ h ρ)
    (hΦh : ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s) (hzρ : z ≠ ρ) (hr' : 0 < r')
    (hrr : r' < r) :
    ∃ M, ∀ k : ℕ,
      ‖iteratedDeriv k Φ z / (k ! : ℂ) - (-1) ^ k * c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k := by
  obtain ⟨g, hg, hfg⟩ := exists_differentiableOn_eqOn_of_analyticAt_nhdsNE
    (compl_singleton_mem_codiscreteWithin ρ) (f := fun s ↦ Φ s - c / (s - ρ))
    (hΦ.sub fun s hs ↦ (DifferentiableAt.div (differentiableAt_const c)
      (differentiableAt_id.sub (differentiableAt_const ρ))
      (sub_ne_zero.2 hs.2)).differentiableWithinAt)
    (by
      rintro a ⟨-, ha⟩
      obtain rfl : a = ρ := ha
      exact ⟨h, hh, hΦh.mono fun s hs ↦ sub_eq_of_eq_add' hs⟩)
  refine exists_forall_norm_iteratedDeriv_div_factorial_sub_le_of_eventuallyEq hg ?_ hzρ hr' hrr
  filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds
    ⟨mem_ball_self (hr'.trans hrr), hzρ⟩] with s hs
  exact sub_eq_iff_eq_add'.1 (hfg hs)

/-- **A simple pole forces large Taylor coefficients.** Let `Φ` be holomorphic on
`ball z r \ {ρ}`, with `Φ s = c / (s - ρ) + h s` near `ρ` and `h` analytic at `ρ`. If the pole is
inside the ball, `‖z - ρ‖ < r`, then eventually
`‖c‖ / 2 / ‖z - ρ‖ ^ (k + 1) ≤ ‖iteratedDeriv k Φ z / k !‖`. For `c = 0` or `z = ρ` the left-hand
side is `0`. -/
theorem eventually_le_norm_iteratedDeriv_div_factorial_of_simple_pole
    (hΦ : DifferentiableOn ℂ Φ (ball z r \ {ρ})) (hh : AnalyticAt ℂ h ρ)
    (hΦh : ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s) (hd : ‖z - ρ‖ < r) :
    ∀ᶠ k : ℕ in atTop, ‖c‖ / 2 / ‖z - ρ‖ ^ (k + 1) ≤ ‖iteratedDeriv k Φ z / (k ! : ℂ)‖ := by
  rcases eq_or_ne z ρ with rfl | hzρ
  · exact .of_forall fun k ↦ by
      rw [sub_self, norm_zero, zero_pow k.succ_ne_zero, div_zero]
      exact norm_nonneg _
  obtain ⟨r', hd', hrr⟩ := exists_between hd
  obtain ⟨M, hM⟩ := exists_forall_norm_iteratedDeriv_div_factorial_sub_le_of_simple_pole hΦ hh hΦh
    hzρ ((norm_nonneg _).trans_lt hd') hrr
  have hM' : ∀ k : ℕ, ‖(-1) ^ k * (iteratedDeriv k Φ z / (k ! : ℂ)) - c / (z - ρ) ^ (k + 1)‖ ≤
      M / r' ^ k := fun k ↦ by
    rw [norm_neg_one_pow_mul_sub, ← mul_div_assoc]
    exact hM k
  filter_upwards [eventually_le_norm_of_norm_sub_div_pow_le hM' hd'] with k hk
  simpa using hk

/-- **A real simple pole with positive residue forces large positive Taylor coefficients.** Let
`y < x` be real and let `Φ` be holomorphic on `ball x r \ {y}`, with `Φ s = c / (s - y) + h s` near
`y`, `h` analytic at `y` and `0 < re c`. If the pole is inside the ball, `x - y < r`, then
eventually `re c / 2 / (x - y) ^ (k + 1) ≤ re ((-1) ^ k * (iteratedDeriv k Φ x / k !))`: the
Taylor coefficients of `t ↦ Φ (x - t)` at `0` eventually have large positive real part. -/
theorem eventually_le_re_neg_one_pow_mul_iteratedDeriv_div_factorial_of_simple_pole {x y : ℝ}
    (hΦ : DifferentiableOn ℂ Φ (ball (x : ℂ) r \ {(y : ℂ)})) (hh : AnalyticAt ℂ h y)
    (hΦh : ∀ᶠ s in 𝓝[≠] (y : ℂ), Φ s = c / (s - y) + h s) (hc : 0 < c.re) (hyx : y < x)
    (hd : x - y < r) :
    ∀ᶠ k : ℕ in atTop,
      c.re / 2 / (x - y) ^ (k + 1) ≤ ((-1) ^ k * (iteratedDeriv k Φ x / (k ! : ℂ))).re := by
  have hxy : (x : ℂ) ≠ y := by exact_mod_cast hyx.ne'
  obtain ⟨r', hd', hrr⟩ := exists_between hd
  obtain ⟨M, hM⟩ := exists_forall_norm_iteratedDeriv_div_factorial_sub_le_of_simple_pole hΦ hh hΦh
    hxy ((sub_pos.2 hyx).trans hd') hrr
  have hM' : ∀ k : ℕ, ‖(-1) ^ k * (iteratedDeriv k Φ x / (k ! : ℂ)) -
      c / ((x - y : ℝ) : ℂ) ^ (k + 1)‖ ≤ M / r' ^ k := fun k ↦ by
    rw [norm_neg_one_pow_mul_sub, ← mul_div_assoc, Complex.ofReal_sub]
    exact hM k
  exact eventually_le_re_of_norm_sub_div_pow_le hM' hc (sub_pos.2 hyx) hd'

end TauCeti.Complex
