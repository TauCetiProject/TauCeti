/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.NumberTheory.Bernoulli
public import TauCeti.Analysis.Asymptotics.Sum.AbelPlana.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.RCLike.TangentCone
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.BoseEinstein

/-!
# Bernoulli Expansion and Remainder Bound for the Abel–Plana Formula

For a function `f` that is `(2m)`-times complex continuously differentiable on a closed vertical
strip `S = {z : ℂ | a ≤ z.re ∧ z.re ≤ b}` (`a < b`) and real-valued on `[a, b]`, expanding
`y ↦ Im f(c + iy)` (`c ∈ [a, b]`) by Taylor's theorem with Lagrange remainder at `y = 0` and
integrating termwise against `(e^{2πy} - 1)⁻¹` via the Bose–Einstein moments yields the higher-order
Abel–Plana expansion (DLMF 2.10.2):

$$2 \int_0^\infty \frac{\operatorname{Im} f(c + iy)}{e^{2\pi y} - 1}\,dy
  = \sum_{s=1}^m \frac{B_{2s}}{(2s)!}\, f^{(2s-1)}(c)
  + \frac{2(-1)^m}{(2m)!} \int_0^\infty
      \operatorname{Im} f^{(2m)}(c + i\vartheta(y) y)\, \frac{y^{2m}}{e^{2\pi y} - 1}\,dy,$$

where `ϑ(y) ∈ (0, 1)` is the Lagrange intermediate point for each `y > 0`.

## Main results

* `TauCeti.exists_two_mul_integral_im_div_exp_two_pi_sub_one_eq`: Taylor–Bernoulli expansion of the
  Abel–Plana half-line integral `2 ∫₀^∞ Im f(c + iy) / (e^{2πy} - 1) dy` at any `c ∈ [a, b]` with
  Lagrange remainder of order `2m` (`m ≥ 1`).
* `TauCeti.exists_sum_Icc_eq_abelPlana_bernoulli`: the full DLMF 2.10.2 Abel–Plana summation
  formula combining `TauCeti.sum_Icc_eq_abelPlana` with the Bernoulli expansion at the upper
  endpoint `c = n`.
* `TauCeti.abs_two_mul_pow_div_factorial_integral_im_le`: supremum remainder bound
  `|R_m| ≤ 2 / (2m)! * ∫₀^∞ (sup_{0 ≤ t ≤ 1} |Im g(c + ity)|) y^{2m} / (e^{2πy} - 1) dy`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(i), formula 2.10.2.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §3.3.
-/

public section

open scoped Nat Real Topology
open Complex Filter MeasureTheory Set

namespace TauCeti

/-! ### Iterated derivatives on a closed vertical strip -/

/-- A closed vertical strip `{z : ℂ | a ≤ z.re ∧ z.re ≤ b}` with `a < b` has unique complex
derivatives everywhere, including on its vertical boundary lines. -/
private lemma uniqueDiffOn_strip {a b : ℝ} (hab : a < b) :
    UniqueDiffOn ℂ {z : ℂ | a ≤ z.re ∧ z.re ≤ b} := by
  have hconv : Convex ℝ {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    (convex_Icc a b).linear_preimage Complex.reLm
  have hopen : IsOpen {z : ℂ | a < z.re ∧ z.re < b} :=
    isOpen_Ioo.preimage Complex.continuous_re
  have hsub : {z : ℂ | a < z.re ∧ z.re < b} ⊆ interior {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    interior_maximal (fun _ hz => ⟨hz.1.le, hz.2.le⟩) hopen
  refine uniqueDiffOn_convex_of_isRCLikeNormedField hconv ⟨(((a + b) / 2 : ℝ) : ℂ), hsub ?_⟩
  exact ⟨by simp; linarith, by simp; linarith⟩

/-- If `f` is `C^N` over `ℂ` on the closed strip `{z | a ≤ z.re ∧ z.re ≤ b}` (`a < b`) and real on
`[a, b]`, then all complex iterated derivatives `iteratedDerivWithin k f S` (`k ≤ N`) are also real
on `[a, b]`. -/
private lemma iteratedDerivWithin_strip_im_eq_zero {f : ℂ → ℂ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hf : ContDiffOn ℂ (N : ℕ) f {z | a ≤ z.re ∧ z.re ≤ b})
    (hreal : ∀ x : ℝ, a ≤ x → x ≤ b → (f x).im = 0) :
    ∀ k ≤ N, ∀ x : ℝ, a ≤ x → x ≤ b →
      (iteratedDerivWithin k f {z | a ≤ z.re ∧ z.re ≤ b} x).im = 0 := by
  let S : Set ℂ := {z : ℂ | a ≤ z.re ∧ z.re ≤ b}
  have huniqS : UniqueDiffOn ℂ S := uniqueDiffOn_strip hab
  have huniqIcc : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  intro k
  induction k with
  | zero =>
    intro _ x hxa hxb
    simpa using hreal x hxa hxb
  | succ k ih =>
    intro hk x hxa hxb
    have hk_lt : k < N := Nat.lt_of_succ_le hk
    have hgdiff : DifferentiableOn ℂ (iteratedDerivWithin k f S) S :=
      hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk_lt) huniqS
    have hmaps : MapsTo (fun t : ℝ => (t : ℂ)) (Icc a b) S :=
      fun t ht => ⟨by simpa using ht.1, by simpa using ht.2⟩
    have h1 : HasDerivWithinAt (iteratedDerivWithin k f S)
        (derivWithin (iteratedDerivWithin k f S) S x) S x :=
      (hgdiff x ⟨by simpa using hxa, by simpa using hxb⟩).hasDerivWithinAt
    have h2 : HasDerivWithinAt (fun t : ℝ => (t : ℂ)) 1 (Icc a b) x :=
      ((hasDerivAt_id x).ofReal_comp).hasDerivWithinAt
    have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt x (h1.scomp x h2 hmaps)
    have h4 : HasDerivWithinAt (fun t : ℝ => (iteratedDerivWithin k f S t).im) 0 (Icc a b) x :=
      (hasDerivWithinAt_const x (Icc a b) (0 : ℝ)).congr
        (fun t ht => ih hk_lt.le t ht.1 ht.2) (ih hk_lt.le x hxa hxb)
    have heq := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) ((huniqIcc x ⟨hxa, hxb⟩).eq h3 h4)
    rw [iteratedDerivWithin_succ]
    simpa [S] using heq

/-- Derivative along a vertical line `y ↦ c + y * I` inside the strip `S`: differentiating
`y ↦ Im (I ^ j * f^{(j)}(c + y * I))` yields `Im (I ^ (j + 1) * f^{(j + 1)}(c + y * I))`. -/
private lemma hasDerivAt_im_I_pow_mul_iteratedDerivWithin {f : ℂ → ℂ} {a b c : ℝ} {N j : ℕ}
    (hab : a < b) (hc : c ∈ Icc a b)
    (hf : ContDiffOn ℂ (N : ℕ) f {z | a ≤ z.re ∧ z.re ≤ b}) (hj : j < N) (y : ℝ) :
    HasDerivAt
      (fun t : ℝ => (I ^ j * iteratedDerivWithin j f {z | a ≤ z.re ∧ z.re ≤ b} (c + t * I)).im)
      ((I ^ (j + 1) * iteratedDerivWithin (j + 1) f {z | a ≤ z.re ∧ z.re ≤ b} (c + y * I)).im)
      y := by
  let S : Set ℂ := {z : ℂ | a ≤ z.re ∧ z.re ≤ b}
  let γ : ℝ → ℂ := fun t => (c : ℂ) + (t : ℂ) * I
  have hγ_mem : ∀ t : ℝ, γ t ∈ S := fun t => by simp [S, γ, hc.1, hc.2]
  have hγ_deriv : HasDerivAt γ I y := by
    simpa [γ] using (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (c : ℂ))
  have hg_diff : DifferentiableOn ℂ (iteratedDerivWithin j f S) S :=
    hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_strip hab)
  have h1 : HasDerivWithinAt (iteratedDerivWithin j f S)
      (iteratedDerivWithin (j + 1) f S (γ y)) S (γ y) := by
    rw [iteratedDerivWithin_succ]
    exact (hg_diff (γ y) (hγ_mem y)).hasDerivWithinAt
  have h2 : HasDerivAt (fun t : ℝ => iteratedDerivWithin j f S (γ t))
      (I * iteratedDerivWithin (j + 1) f S (γ y)) y := by
    simpa [Function.comp_def] using h1.scomp_hasDerivAt y hγ_deriv hγ_mem
  have h3 : HasDerivAt (fun t : ℝ => I ^ j * iteratedDerivWithin j f S (γ t))
      (I ^ (j + 1) * iteratedDerivWithin (j + 1) f S (γ y)) y := by
    simpa [pow_succ, mul_assoc, mul_left_comm] using h2.const_mul (I ^ j)
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h3

/-- Formula for the `k`-th real derivative of `y ↦ Im f(c + y * I)` along a vertical line in `S`. -/
private lemma iteratedDeriv_im_add_mul_I {f : ℂ → ℂ} {a b c : ℝ} {N : ℕ}
    (hab : a < b) (hc : c ∈ Icc a b)
    (hf : ContDiffOn ℂ (N : ℕ) f {z | a ≤ z.re ∧ z.re ≤ b}) :
    ∀ k ≤ N, ∀ y : ℝ,
      iteratedDeriv k (fun t : ℝ => (f (c + t * I)).im) y =
        (I ^ k * iteratedDerivWithin k f {z | a ≤ z.re ∧ z.re ≤ b} (c + y * I)).im := by
  intro k
  induction k with
  | zero =>
    intro _ y
    simp
  | succ k ih =>
    intro hk y
    have hk_lt : k < N := Nat.lt_of_succ_le hk
    have hfun : iteratedDeriv k (fun t : ℝ => (f (c + t * I)).im) =
        fun t : ℝ => (I ^ k * iteratedDerivWithin k f {z | a ≤ z.re ∧ z.re ≤ b} (c + t * I)).im :=
      funext (ih hk_lt.le)
    rw [iteratedDeriv_succ, hfun]
    exact (hasDerivAt_im_I_pow_mul_iteratedDerivWithin hab hc hf hk_lt y).deriv

/-- Smoothness (`C^N` over `ℝ`) of `y ↦ Im f(c + y * I)` when `f` is `C^N` over `ℂ` on `S`. -/
private lemma contDiff_im_add_mul_I {f : ℂ → ℂ} {a b c : ℝ} {N : ℕ}
    (hab : a < b) (hc : c ∈ Icc a b)
    (hf : ContDiffOn ℂ (N : ℕ) f {z | a ≤ z.re ∧ z.re ≤ b}) :
    ContDiff ℝ (N : ℕ) (fun t : ℝ => (f (c + t * I)).im) := by
  let S : Set ℂ := {z : ℂ | a ≤ z.re ∧ z.re ≤ b}
  have huniqS : UniqueDiffOn ℂ S := uniqueDiffOn_strip hab
  have hγ_cont : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * I) := by fun_prop
  have hγ_mem : ∀ t : ℝ, (c : ℂ) + (t : ℂ) * I ∈ S := fun t => by simp [S, hc.1, hc.2]
  rw [contDiff_nat_iff_iteratedDeriv]
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hfun : iteratedDeriv k (fun t : ℝ => (f (c + t * I)).im) =
        fun t : ℝ => (I ^ k * iteratedDerivWithin k f S (c + t * I)).im :=
      funext (iteratedDeriv_im_add_mul_I hab hc hf k hk)
    rw [hfun]
    have hg_cont : ContinuousOn (iteratedDerivWithin k f S) S :=
      hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) huniqS
    exact Complex.continuous_im.comp
      (continuous_const.mul (hg_cont.comp_continuous hγ_cont hγ_mem))
  · have hfun : iteratedDeriv k (fun t : ℝ => (f (c + t * I)).im) =
        fun t : ℝ => (I ^ k * iteratedDerivWithin k f S (c + t * I)).im :=
      funext (iteratedDeriv_im_add_mul_I hab hc hf k hk.le)
    rw [hfun]
    exact fun y =>
      (hasDerivAt_im_I_pow_mul_iteratedDerivWithin hab hc hf hk y).differentiableAt

/-- Summing over `k ∈ range (2 * m)` when all even-indexed terms vanish reduces to `Icc 1 m` via
`k = 2 * s - 1`. -/
private lemma sum_range_two_mul_of_even_eq_zero {m : ℕ} {g : ℕ → ℝ}
    (heven : ∀ s < m, g (2 * s) = 0) :
    ∑ k ∈ Finset.range (2 * m), g k = ∑ s ∈ Finset.Icc 1 m, g (2 * s - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih (fun s hs => heven s (Nat.lt_succ_of_lt hs)), heven m (Nat.lt_succ_self m), add_zero,
      Finset.sum_Icc_succ_top (Nat.le_add_left 1 m)]
    congr 1

/-- Pointwise Taylor–Lagrange identity for `Im f(c + y * I)` at `y > 0` when `f` is real on `[a, b]`
and `1 ≤ m`. -/
private lemma exists_im_add_mul_I_eq_taylor_odd {f : ℂ → ℂ} {a b c y : ℝ} {m : ℕ}
    (hab : a < b) (hc : c ∈ Icc a b) (hm : 1 ≤ m) (hy : 0 < y)
    (hf : ContDiffOn ℂ (2 * m : ℕ) f {z | a ≤ z.re ∧ z.re ≤ b})
    (hreal : ∀ x : ℝ, a ≤ x → x ≤ b → (f x).im = 0) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      (f (c + y * I)).im =
        (∑ s ∈ Finset.Icc 1 m,
          (-1 : ℝ) ^ (s - 1) *
            (iteratedDerivWithin (2 * s - 1) f {z | a ≤ z.re ∧ z.re ≤ b} c).re *
            y ^ (2 * s - 1) / (2 * s - 1)!) +
        (-1 : ℝ) ^ m *
          (iteratedDerivWithin (2 * m) f {z | a ≤ z.re ∧ z.re ≤ b}
            (c + ((θ * y : ℝ) : ℂ) * I)).im *
          y ^ (2 * m) / (2 * m)! := by
  let S : Set ℂ := {z : ℂ | a ≤ z.re ∧ z.re ≤ b}
  let ψ : ℝ → ℝ := fun t => (f (c + t * I)).im
  have hψ : ContDiff ℝ (2 * m : ℕ) ψ := contDiff_im_add_mul_I hab hc hf
  have h2m : (2 * m - 1) + 1 = 2 * m := by omega
  have hψ_on : ContDiffOn ℝ (((2 * m - 1 : ℕ) : WithTop ℕ∞) + 1) ψ (uIcc 0 y) := by
    have h1 : ContDiffOn ℝ (2 * m : ℕ) ψ (uIcc 0 y) := hψ.contDiffOn
    rwa [← h2m, Nat.cast_add, Nat.cast_one] at h1
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hy.ne hψ_on
  rw [uIoo_of_lt hy] at hξ_mem
  refine ⟨ξ / y, ⟨div_pos hξ_mem.1 hy, (div_lt_one hy).mpr hξ_mem.2⟩, ?_⟩
  have hθy : ξ / y * y = ξ := div_mul_cancel₀ ξ hy.ne'
  -- Rewrite the Taylor polynomial at `x₀ = 0` using `iteratedDeriv_im_add_mul_I`.
  have htaylor : taylorWithinEval ψ (2 * m - 1) (uIcc 0 y) 0 y =
      ∑ s ∈ Finset.Icc 1 m,
        (-1 : ℝ) ^ (s - 1) * (iteratedDerivWithin (2 * s - 1) f S c).re *
          y ^ (2 * s - 1) / (2 * s - 1)! := by
    rw [taylor_within_apply, h2m]
    have hcongr : ∑ k ∈ Finset.range (2 * m),
          ((k ! : ℝ)⁻¹ * (y - 0) ^ k) • iteratedDerivWithin k ψ (uIcc 0 y) 0 =
        ∑ k ∈ Finset.range (2 * m),
          (I ^ k * iteratedDerivWithin k f S c).im * y ^ k / (k ! : ℝ) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ 2 * m := (Finset.mem_range.mp hk).le
      have hderiv0 : iteratedDerivWithin k ψ (uIcc 0 y) 0 =
          (I ^ k * iteratedDerivWithin k f S c).im := by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hy.ne)
          (hψ.contDiffAt.of_le (by exact_mod_cast hk_le)) left_mem_uIcc]
        simpa using iteratedDeriv_im_add_mul_I hab hc hf k hk_le 0
      rw [hderiv0, sub_zero, smul_eq_mul]
      ring
    rw [hcongr, sum_range_two_mul_of_even_eq_zero]
    · refine Finset.sum_congr rfl fun s hs => ?_
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      have hsm : s ≤ m := (Finset.mem_Icc.mp hs).2
      have him0 : (iteratedDerivWithin (2 * s - 1) f S c).im = 0 :=
        iteratedDerivWithin_strip_im_eq_zero hab hf hreal (2 * s - 1) (by omega) c hc.1 hc.2
      have hIodd : I ^ (2 * s - 1) = (((-1 : ℝ) ^ (s - 1) : ℝ) : ℂ) * I := by
        rw [show 2 * s - 1 = 2 * (s - 1) + 1 by omega, pow_succ, pow_mul, I_sq]
        push_cast
        rfl
      have him_val : (I ^ (2 * s - 1) * iteratedDerivWithin (2 * s - 1) f S c).im =
          (-1 : ℝ) ^ (s - 1) * (iteratedDerivWithin (2 * s - 1) f S c).re := by
        rw [hIodd, mul_assoc, mul_im, ofReal_re, ofReal_im, I_mul_im, I_mul_re, him0]
        ring
      rw [him_val]
    · intro s hs
      have him0 : (iteratedDerivWithin (2 * s) f S c).im = 0 :=
        iteratedDerivWithin_strip_im_eq_zero hab hf hreal (2 * s) (by omega) c hc.1 hc.2
      have hIeven : I ^ (2 * s) = (((-1 : ℝ) ^ s : ℝ) : ℂ) := by
        rw [pow_mul, I_sq]
        push_cast
        rfl
      rw [hIeven, mul_im, ofReal_re, ofReal_im, him0]
      ring
  -- Rewrite the Lagrange remainder term of order `2 * m`.
  have hrem : iteratedDeriv ((2 * m - 1) + 1) ψ ξ * (y - 0) ^ ((2 * m - 1) + 1) /
        ((2 * m - 1) + 1)! =
      (-1 : ℝ) ^ m * (iteratedDerivWithin (2 * m) f S (c + ((ξ / y * y : ℝ) : ℂ) * I)).im *
        y ^ (2 * m) / (2 * m)! := by
    rw [h2m, iteratedDeriv_im_add_mul_I hab hc hf (2 * m) le_rfl ξ, hθy, sub_zero]
    have hI2m : I ^ (2 * m) = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by
      rw [pow_mul, I_sq]
      push_cast
      rfl
    rw [hI2m, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  linarith [hξ_eq, htaylor, hrem]

/-! ### Main theorems -/

/-- Twice the integrated `s`-th odd Taylor term against `(e^{2πy} - 1)⁻¹` equals
`(B_{2s} / (2s)!) * A`. -/
private lemma two_mul_odd_moment_eq_bernoulli {s : ℕ} (hs : 1 ≤ s) (A : ℝ) :
    2 * (((-1 : ℝ) ^ (s - 1) * A / (2 * s - 1)!) *
      ∫ y in Ioi (0 : ℝ), y ^ (2 * s - 1) / (Real.exp (2 * π * y) - 1)) =
    (bernoulli (2 * s) : ℝ) / (2 * s)! * A := by
  rw [integral_Ioi_pow_div_exp_two_pi_mul_sub_one hs]
  have hs_add : (-1 : ℝ) ^ (s + 1) = (-1 : ℝ) ^ (s - 1) := by
    rw [show s + 1 = (s - 1) + 2 by omega, pow_add]
    norm_num
  have hs_sq : (-1 : ℝ) ^ (s - 1) * (-1 : ℝ) ^ (s - 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hfact_s : ((2 * s)! : ℝ) = (2 * s : ℝ) * ((2 * s - 1)! : ℝ) := by
    conv_lhs => rw [show 2 * s = (2 * s - 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    rw [show ((2 * s - 1 : ℕ) : ℝ) + 1 = 2 * (s : ℝ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
  have hfac_s_ne : ((2 * s - 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs_ne : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hs_add, hfact_s]
  field_simp
  linear_combination 4 * (bernoulli (2 * s) : ℝ) * A * hs_sq

/-- **Bernoulli–Taylor expansion of the Abel–Plana half-line integral** (DLMF 2.10.2, integral
expansion). Let `f` be `C^{2m}` (`m ≥ 1`) over `ℂ` on the closed vertical strip
`S = {z : ℂ | a ≤ z.re ∧ z.re ≤ b}` (`a < b`) and real on `[a, b]`. For any `c ∈ [a, b]` such that
`y ↦ Im f(c + iy) / (e^{2πy} - 1)` is integrable on `(0, ∞)`, there exists a Lagrange intermediate
point function `ϑ : ℝ → ℝ` with `ϑ(y) ∈ (0, 1)` for every `y > 0` such that the remainder integrand
is integrable on `(0, ∞)` and
`2 ∫₀^∞ Im f(c + iy) / (e^{2πy} - 1) dy
  = ∑_{s=1}^m (B_{2s} / (2s)!) Re f^{(2s-1)}(c)
    + (2 (-1)^m / (2m)!) ∫₀^∞ Im f^{(2m)}(c + i ϑ(y) y) y^{2m} / (e^{2πy} - 1) dy`.

Here `a < b` ensures that `S` has nonempty interior so complex iterated derivatives
`iteratedDerivWithin k f S` are uniquely determined up to the boundary lines, and `1 ≤ m` gives
positive Taylor order `2m` so the Lagrange intermediate point lies in `(0, 1)` (the `m = 0` case is
the unexpanded integral). -/
theorem exists_two_mul_integral_im_div_exp_two_pi_sub_one_eq {f : ℂ → ℂ} {a b c : ℝ} {m : ℕ}
    (hab : a < b) (hc : c ∈ Icc a b) (hm : 1 ≤ m)
    (hf : ContDiffOn ℂ (2 * m : ℕ) f {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
    (hreal : ∀ x : ℝ, a ≤ x → x ≤ b → (f x).im = 0)
    (hint : IntegrableOn (fun y : ℝ => (f (c + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0)) :
    ∃ ϑ : ℝ → ℝ, (∀ y > 0, ϑ y ∈ Ioo (0 : ℝ) 1) ∧
      IntegrableOn
        (fun y : ℝ =>
          (iteratedDerivWithin (2 * m) f {z | a ≤ z.re ∧ z.re ≤ b}
            (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
            y ^ (2 * m) / (Real.exp (2 * π * y) - 1))
        (Ioi 0) ∧
      2 * (∫ y in Ioi (0 : ℝ), (f (c + y * I)).im / (Real.exp (2 * π * y) - 1)) =
        (∑ s ∈ Finset.Icc 1 m,
          (bernoulli (2 * s) : ℝ) / (2 * s)! *
            (iteratedDerivWithin (2 * s - 1) f {z | a ≤ z.re ∧ z.re ≤ b} c).re) +
        2 * (-1 : ℝ) ^ m / (2 * m)! *
          ∫ y in Ioi (0 : ℝ),
            (iteratedDerivWithin (2 * m) f {z | a ≤ z.re ∧ z.re ≤ b}
              (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
              y ^ (2 * m) / (Real.exp (2 * π * y) - 1) := by
  classical
  let S : Set ℂ := {z : ℂ | a ≤ z.re ∧ z.re ≤ b}
  have hex : ∀ y : ℝ, 0 < y → ∃ θ ∈ Ioo (0 : ℝ) 1,
      (f (c + y * I)).im =
        (∑ s ∈ Finset.Icc 1 m,
          (-1 : ℝ) ^ (s - 1) * (iteratedDerivWithin (2 * s - 1) f S c).re *
            y ^ (2 * s - 1) / (2 * s - 1)!) +
        (-1 : ℝ) ^ m * (iteratedDerivWithin (2 * m) f S (c + ((θ * y : ℝ) : ℂ) * I)).im *
          y ^ (2 * m) / (2 * m)! :=
    fun y hy => exists_im_add_mul_I_eq_taylor_odd hab hc hm hy hf hreal
  let ϑ : ℝ → ℝ := fun y => if hy : 0 < y then (hex y hy).choose else 1 / 2
  have hϑ_mem : ∀ y > 0, ϑ y ∈ Ioo (0 : ℝ) 1 := by
    intro y hy
    simpa [ϑ, hy] using (hex y hy).choose_spec.1
  have hϑ_eq : ∀ y : ℝ, 0 < y →
      (f (c + y * I)).im =
        (∑ s ∈ Finset.Icc 1 m,
          (-1 : ℝ) ^ (s - 1) * (iteratedDerivWithin (2 * s - 1) f S c).re *
            y ^ (2 * s - 1) / (2 * s - 1)!) +
        (-1 : ℝ) ^ m * (iteratedDerivWithin (2 * m) f S (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
          y ^ (2 * m) / (2 * m)! := by
    intro y hy
    simpa [ϑ, hy] using (hex y hy).choose_spec.2
  -- Each odd Taylor term divided by `exp (2 * π * y) - 1` is integrable on `Ioi 0`.
  let term : ℕ → ℝ → ℝ := fun s y =>
    ((-1 : ℝ) ^ (s - 1) * (iteratedDerivWithin (2 * s - 1) f S c).re / (2 * s - 1)!) *
      (y ^ (2 * s - 1) / (Real.exp (2 * π * y) - 1))
  have hterm_int : ∀ s ∈ Finset.Icc 1 m, IntegrableOn (term s) (Ioi 0) := fun s hs =>
    (integrableOn_pow_div_exp_mul_sub_one (k := 2 * s - 1) (c := 2 * π)
      (by have := (Finset.mem_Icc.mp hs).1; omega) (by positivity)).const_mul _
  have hsum_int : IntegrableOn (fun y => ∑ s ∈ Finset.Icc 1 m, term s y) (Ioi 0) :=
    integrable_finsetSum _ hterm_int
  -- On `Ioi 0`, the remainder integrand is a constant multiple of `LHS - sum`, hence integrable.
  let remIntegrand : ℝ → ℝ := fun y =>
    (iteratedDerivWithin (2 * m) f S (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
      y ^ (2 * m) / (Real.exp (2 * π * y) - 1)
  have hfac_ne : ((2 * m)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsign_sq : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hrem_eqOn : EqOn remIntegrand
      (fun y => ((-1 : ℝ) ^ m * (2 * m)!) *
        ((f (c + y * I)).im / (Real.exp (2 * π * y) - 1) -
          ∑ s ∈ Finset.Icc 1 m, term s y)) (Ioi 0) := by
    intro y (hy : 0 < y)
    dsimp only [remIntegrand, term]
    rw [hϑ_eq y hy, add_div, Finset.sum_div]
    have hsum_eq :
        (∑ x ∈ Finset.Icc 1 m,
          (-1 : ℝ) ^ (x - 1) * (iteratedDerivWithin (2 * x - 1) f S c).re *
            y ^ (2 * x - 1) / (2 * x - 1)! / (Real.exp (2 * π * y) - 1)) =
        ∑ x ∈ Finset.Icc 1 m,
          (-1 : ℝ) ^ (x - 1) * (iteratedDerivWithin (2 * x - 1) f S c).re / (2 * x - 1)! *
            (y ^ (2 * x - 1) / (Real.exp (2 * π * y) - 1)) :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [hsum_eq, add_sub_cancel_left]
    calc
      (iteratedDerivWithin (2 * m) f S (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
          y ^ (2 * m) / (Real.exp (2 * π * y) - 1)
        = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) * (((2 * m)! : ℝ) / ((2 * m)! : ℝ)) *
            ((iteratedDerivWithin (2 * m) f S (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
              y ^ (2 * m) / (Real.exp (2 * π * y) - 1)) := by
          rw [hsign_sq, div_self hfac_ne, one_mul, one_mul]
      _ = ((-1 : ℝ) ^ m * (2 * m)!) *
            ((-1 : ℝ) ^ m *
              (iteratedDerivWithin (2 * m) f S (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
              y ^ (2 * m) / (2 * m)! / (Real.exp (2 * π * y) - 1)) := by
          ring
  have hrem_int : IntegrableOn remIntegrand (Ioi 0) :=
    IntegrableOn.congr_fun ((hint.sub hsum_int).const_mul ((-1 : ℝ) ^ m * (2 * m)!))
      hrem_eqOn.symm measurableSet_Ioi
  refine ⟨ϑ, hϑ_mem, hrem_int, ?_⟩
  -- Integrate the decomposition over `Ioi 0` and evaluate each Bose–Einstein moment.
  have hdecomp : EqOn
      (fun y : ℝ => (f (c + y * I)).im / (Real.exp (2 * π * y) - 1))
      (fun y : ℝ => (∑ s ∈ Finset.Icc 1 m, term s y) +
        ((-1 : ℝ) ^ m / (2 * m)!) * remIntegrand y) (Ioi 0) := by
    intro y (hy : 0 < y)
    dsimp only [term, remIntegrand]
    rw [hϑ_eq y hy, add_div, Finset.sum_div]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ => by ring
    · ring
  rw [setIntegral_congr_fun measurableSet_Ioi hdecomp,
    integral_add hsum_int (hrem_int.const_mul ((-1 : ℝ) ^ m / (2 * m)!)),
    integral_finsetSum _ hterm_int, integral_const_mul, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun s hs => ?_
    dsimp only [term]
    rw [integral_const_mul]
    exact two_mul_odd_moment_eq_bernoulli (Finset.mem_Icc.mp hs).1 _
  · ring

/-- **The Abel–Plana summation formula with Bernoulli expansion** (DLMF 2.10.2). Let `a < n` be
integers and `1 ≤ m`. If `f` is `C^{2m}` over `ℂ` on `{z | a ≤ Re z ≤ n}`, `f(z) = o(e^{2π|Im z|})`
uniformly in the strip, `f` is real on `[a, n]`, and `y ↦ Im f(c + iy) / (e^{2πy} - 1)` is
integrable on `(0, ∞)` at `c = a` and `c = n`, then there exists `ϑ : ℝ → ℝ` with
`ϑ(y) ∈ (0, 1)` for every `y > 0` such that
`∑_{j=a}^n f(j) = ∫_a^n f + f(a)/2 + f(n)/2
  - 2 ∫_0^∞ Im f(a + iy) / (e^{2πy} - 1) dy
  + ∑_{s=1}^m (B_{2s} / (2s)!) f^{(2s-1)}(n)
  + (2 (-1)^m / (2m)!) ∫_0^∞ Im f^{(2m)}(n + i ϑ(y) y) y^{2m} / (e^{2πy} - 1) dy`.

Here `a < n` gives the closed strip nonempty interior so `iteratedDerivWithin` is uniquely
determined at the boundary `z = n`, and `1 ≤ m` gives positive Taylor order `2m` (for `a = n` or
`m = 0`, see `TauCeti.sum_Icc_eq_abelPlana`). -/
theorem exists_sum_Icc_eq_abelPlana_bernoulli {f : ℂ → ℂ} {a n : ℤ} {m : ℕ}
    (han : a < n) (hm : 1 ≤ m)
    (hf : ContDiffOn ℂ (2 * m : ℕ) f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n})
    (hgrowth : Tendsto (fun z => f z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) (𝓝 0))
    (hreal : ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ n → (f x).im = 0)
    (hinta : IntegrableOn (fun y : ℝ => (f (a + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0))
    (hintn : IntegrableOn (fun y : ℝ => (f (n + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0)) :
    ∃ ϑ : ℝ → ℝ, (∀ y > 0, ϑ y ∈ Ioo (0 : ℝ) 1) ∧
      IntegrableOn
        (fun y : ℝ =>
          (iteratedDerivWithin (2 * m) f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}
            (n + ((ϑ y * y : ℝ) : ℂ) * I)).im *
            y ^ (2 * m) / (Real.exp (2 * π * y) - 1))
        (Ioi 0) ∧
      ∑ j ∈ Finset.Icc a n, f j =
        (∫ x in (a : ℝ)..n, f x) + f a / 2 + f n / 2 -
          2 * ((∫ y in Ioi (0 : ℝ), (f (a + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) +
          (∑ s ∈ Finset.Icc 1 m,
            ((bernoulli (2 * s) : ℂ) / (2 * s)!) *
              iteratedDerivWithin (2 * s - 1) f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n} n) +
          (2 * (-1 : ℂ) ^ m / (2 * m)!) *
            ((∫ y in Ioi (0 : ℝ),
              (iteratedDerivWithin (2 * m) f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}
                (n + ((ϑ y * y : ℝ) : ℂ) * I)).im *
                y ^ (2 * m) / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) := by
  let S : Set ℂ := {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}
  have han' : (a : ℝ) < n := by exact_mod_cast han
  have hdiff_open : DifferentiableOn ℂ f {z | (a : ℝ) < z.re ∧ z.re < n} :=
    (hf.differentiableOn (by simp; omega)).mono fun _ hz => ⟨hz.1.le, hz.2.le⟩
  have hintn' : IntegrableOn
      (fun y : ℝ => (f (((n : ℝ) : ℂ) + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0) := by
    simpa using hintn
  obtain ⟨ϑ, hϑ_mem, hϑ_int, hϑ_eq⟩ :=
    exists_two_mul_integral_im_div_exp_two_pi_sub_one_eq han' ⟨han'.le, le_rfl⟩ hm hf hreal hintn'
  refine ⟨ϑ, hϑ_mem, by simpa using hϑ_int, ?_⟩
  rw [sum_Icc_eq_abelPlana han.le hdiff_open hf.continuousOn hgrowth hreal hinta hintn]
  simp only [ofReal_intCast] at hϑ_eq
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) hϑ_eq
  rw [ofReal_mul, ofReal_ofNat, ofReal_add, ofReal_sum, ofReal_mul, ofReal_div, ofReal_mul,
    ofReal_ofNat, ofReal_pow, ofReal_neg, ofReal_one, ofReal_natCast] at hcast
  have hsum_cast :
      (∑ s ∈ Finset.Icc 1 m,
        (((bernoulli (2 * s) : ℝ) / (2 * s)! *
          (iteratedDerivWithin (2 * s - 1) f S n).re : ℝ) : ℂ)) =
      ∑ s ∈ Finset.Icc 1 m,
        ((bernoulli (2 * s) : ℂ) / (2 * s)!) * iteratedDerivWithin (2 * s - 1) f S n := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsm : s ≤ m := (Finset.mem_Icc.mp hs).2
    have him0 : (iteratedDerivWithin (2 * s - 1) f S ((n : ℝ) : ℂ)).im = 0 :=
      iteratedDerivWithin_strip_im_eq_zero han' hf hreal (2 * s - 1) (by omega) n han'.le le_rfl
    have him0' : (iteratedDerivWithin (2 * s - 1) f S n).im = 0 := by simpa using him0
    have hre_eq : (((iteratedDerivWithin (2 * s - 1) f S n).re : ℝ) : ℂ) =
        iteratedDerivWithin (2 * s - 1) f S n :=
      Complex.ext rfl him0'.symm
    rw [ofReal_mul, ofReal_div, ofReal_ratCast, ofReal_natCast, hre_eq]
  rw [hsum_cast] at hcast
  linear_combination hcast

/-- **Supremum bound for the Abel–Plana Lagrange remainder** (DLMF 2.10.2). If `ϑ(y) ∈ [0, 1]` and
`t ↦ Im g(c + i t y)` is continuous on `[0, 1]` for every `y > 0`, and the supremum envelope is
integrable against `y^{2m} / (e^{2πy} - 1)` on `(0, ∞)`, then
`|2 (-1)^m / (2m)! * ∫₀^∞ Im g(c + i ϑ(y) y) y^{2m} / (e^{2πy} - 1) dy|
  ≤ 2 / (2m)! * ∫₀^∞ (sup_{t ∈ [0, 1]} |Im g(c + i t y)|) y^{2m} / (e^{2πy} - 1) dy`. -/
theorem abs_two_mul_pow_div_factorial_integral_im_le {g : ℂ → ℂ} {c : ℝ} {m : ℕ} {ϑ : ℝ → ℝ}
    (hϑ : ∀ y > 0, ϑ y ∈ Icc (0 : ℝ) 1)
    (hcont : ∀ y > 0, ContinuousOn (fun t : ℝ => (g (c + ((t * y : ℝ) : ℂ) * I)).im) (Icc 0 1))
    (hint : IntegrableOn
      (fun y : ℝ =>
        sSup ((fun t : ℝ => |(g (c + ((t * y : ℝ) : ℂ) * I)).im|) '' Icc 0 1) *
          y ^ (2 * m) / (Real.exp (2 * π * y) - 1))
      (Ioi 0)) :
    |2 * (-1 : ℝ) ^ m / (2 * m)! *
        ∫ y in Ioi (0 : ℝ),
          (g (c + ((ϑ y * y : ℝ) : ℂ) * I)).im * y ^ (2 * m) / (Real.exp (2 * π * y) - 1)| ≤
      2 / (2 * m)! *
        ∫ y in Ioi (0 : ℝ),
          sSup ((fun t : ℝ => |(g (c + ((t * y : ℝ) : ℂ) * I)).im|) '' Icc 0 1) *
            y ^ (2 * m) / (Real.exp (2 * π * y) - 1) := by
  have hcoeff : |2 * (-1 : ℝ) ^ m / (2 * m)!| = 2 / (2 * m)! := by
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
      abs_of_nonneg (Nat.cast_nonneg (2 * m)!)]
  rw [abs_mul, hcoeff]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hint ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : 0 < y)
  have hexp_pos : 0 < Real.exp (2 * π * y) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hpow_nonneg : 0 ≤ y ^ (2 * m) := pow_nonneg hy.le _
  have hbdd : BddAbove ((fun t : ℝ => |(g (c + ((t * y : ℝ) : ℂ) * I)).im|) '' Icc 0 1) :=
    isCompact_Icc.bddAbove_image (continuous_abs.comp_continuousOn (hcont y hy))
  have hle : |(g (c + ((ϑ y * y : ℝ) : ℂ) * I)).im| ≤
      sSup ((fun t : ℝ => |(g (c + ((t * y : ℝ) : ℂ) * I)).im|) '' Icc 0 1) :=
    le_csSup hbdd (mem_image_of_mem _ (hϑ y hy))
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hpow_nonneg, abs_of_pos hexp_pos]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle hpow_nonneg) hexp_pos.le

end TauCeti

end

/-! ### Non-vacuity verification examples -/

section Examples

open scoped Nat Real Topology
open Complex Filter MeasureTheory Set TauCeti

-- Constant function `f(z) = 1`: both half-line integrals vanish and the formula reads
-- `∑_{j=a}^n 1 = (n - a) + 1/2 + 1/2`.
example {a n : ℤ} (han : a ≤ n) :
    ∑ _j ∈ Finset.Icc a n, (1 : ℂ) = ((n : ℂ) - a) + 1 := by
  have hgrowth : Tendsto (fun z : ℂ => (1 : ℂ) * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) (𝓝 0) :=
    tendsto_mul_exp_neg_two_pi_abs_im_of_norm_le (C := 1) (p := 0) (c := 0) (by positivity)
      fun _ _ _ => by simp
  have h := sum_Icc_eq_abelPlana (f := fun _ => (1 : ℂ)) han (differentiableOn_const 1)
    continuousOn_const hgrowth (fun _ _ _ => one_im) (by simp) (by simp)
  rw [h]
  simp only [intervalIntegral.integral_const, Complex.real_smul, one_im, zero_div,
    integral_zero, ofReal_zero, mul_zero, sub_zero, add_zero, ofReal_sub, ofReal_intCast]
  ring

-- Quadratic function `f(z) = z^2`: `Im f(k + iy) = 2ky` and `∫₀^∞ y / (e^{2πy} - 1) dy = 1/24`,
-- recovering Faulhaber's formula `∑_{j=a}^n j^2 = (n^3 - a^3)/3 + (a^2 + n^2)/2 + (n - a)/6`.
example {a n : ℤ} (han : a ≤ n) :
    ∑ j ∈ Finset.Icc a n, (j : ℂ) ^ 2 =
      ((n : ℂ) ^ 3 - a ^ 3) / 3 + ((a : ℂ) ^ 2 + n ^ 2) / 2 + ((n : ℂ) - a) / 6 := by
  let M : ℝ := max |(a : ℝ)| |(n : ℝ)|
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have hgrowth : Tendsto (fun z : ℂ => z ^ 2 * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) (𝓝 0) := by
    refine tendsto_mul_exp_neg_two_pi_abs_im_of_norm_le (C := M ^ 2 + 1) (p := 2) (c := 0)
      (by positivity) ?_
    intro z hza hzb
    have hre_abs : |z.re| ≤ M := by
      rw [abs_le]
      exact ⟨by linarith [le_max_left |(a : ℝ)| |(n : ℝ)|, neg_abs_le (a : ℝ), hza],
        by linarith [le_max_right |(a : ℝ)| |(n : ℝ)|, le_abs_self (n : ℝ), hzb]⟩
    have hre_sq : z.re ^ 2 ≤ M ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hM_nonneg])
    have hnorm : ‖z ^ 2‖ = z.re ^ 2 + |z.im| ^ 2 := by
      rw [norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq_abs]
      ring
    rw [hnorm, zero_mul, Real.exp_zero, mul_one,
      Real.rpow_two (1 + |z.im|)]
    nlinarith [abs_nonneg z.im, sq_nonneg M]
  have him_sq : ∀ (k : ℤ) (y : ℝ), (((k : ℂ) + y * I) ^ 2).im = 2 * (k : ℝ) * y := by
    intro k y
    simp [sq]
    ring
  have hint_k : ∀ k : ℤ,
      IntegrableOn (fun y : ℝ => (((k : ℂ) + y * I) ^ 2).im / (Real.exp (2 * π * y) - 1))
        (Ioi 0) := by
    intro k
    have h1 : IntegrableOn
        (fun y : ℝ => (2 * (k : ℝ)) * (y ^ (2 * 1 - 1) / (Real.exp (2 * π * y) - 1))) (Ioi 0) :=
      (integrableOn_pow_div_exp_mul_sub_one (k := 1) (c := 2 * π) le_rfl (by positivity)).const_mul
        (2 * (k : ℝ))
    refine h1.congr_fun (fun y _ => ?_) measurableSet_Ioi
    rw [him_sq]
    simp [mul_div_assoc]
  have hint_val : ∀ k : ℤ,
      ∫ y in Ioi (0 : ℝ), (((k : ℂ) + y * I) ^ 2).im / (Real.exp (2 * π * y) - 1) =
        (k : ℝ) / 12 := by
    intro k
    have hcongr : (∫ y in Ioi (0 : ℝ), (((k : ℂ) + y * I) ^ 2).im / (Real.exp (2 * π * y) - 1)) =
        ∫ y in Ioi (0 : ℝ), (2 * (k : ℝ)) * (y / (Real.exp (2 * π * y) - 1)) :=
      setIntegral_congr_fun measurableSet_Ioi fun y _ => by rw [him_sq]; ring
    rw [hcongr, integral_const_mul, integral_Ioi_div_exp_two_pi_mul_sub_one]
    ring
  have hmain := sum_Icc_eq_abelPlana (f := fun z : ℂ => z ^ 2) han
    (differentiable_id.pow 2).differentiableOn (continuous_id.pow 2).continuousOn hgrowth
    (fun x _ _ => by norm_cast) (hint_k a) (hint_k n)
  have hint_ab : ∫ x in (a : ℝ)..n, (x : ℂ) ^ 2 = ((n : ℂ) ^ 3 - a ^ 3) / 3 := by
    have hfn : (fun x : ℝ => (x : ℂ) ^ 2) = fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) :=
      funext fun x => by norm_cast
    rw [hfn, intervalIntegral.integral_ofReal, integral_pow]
    push_cast
    ring
  rw [hmain, hint_ab, hint_val a, hint_val n]
  push_cast
  ring

-- Linear function `f(z) = z` (`a < n`, `m = 1`): exercises both
-- `exists_sum_Icc_eq_abelPlana_bernoulli` (where `(B_2 / 2!) f'(n) = 1 / 12` cancels
-- `-2 ∫₀^∞ Im(a + iy) / (e^{2πy} - 1) dy = -1 / 12`) and
-- `abs_two_mul_pow_div_factorial_integral_im_le` (which bounds the `2m = 2` remainder by `0`).
example {a n : ℤ} (han : a < n) :
    ∑ j ∈ Finset.Icc a n, (j : ℂ) =
      ((n : ℂ) ^ 2 - a ^ 2) / 2 + ((a : ℂ) + n) / 2 := by
  let S : Set ℂ := {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}
  have han' : (a : ℝ) < n := by exact_mod_cast han
  have huniq : UniqueDiffOn ℂ S := uniqueDiffOn_strip han'
  let M : ℝ := max |(a : ℝ)| |(n : ℝ)|
  have hgrowth : Tendsto (fun z : ℂ => z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 S) (𝓝 0) := by
    refine tendsto_mul_exp_neg_two_pi_abs_im_of_norm_le (C := M + 1) (p := 1) (c := 0)
      (by positivity) ?_
    intro z hza hzb
    have hre_abs : |z.re| ≤ M := by
      rw [abs_le]
      exact ⟨by linarith [le_max_left |(a : ℝ)| |(n : ℝ)|, neg_abs_le (a : ℝ), hza],
        by linarith [le_max_right |(a : ℝ)| |(n : ℝ)|, le_abs_self (n : ℝ), hzb]⟩
    have hnorm : ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
    rw [zero_mul, Real.exp_zero, mul_one, Real.rpow_one]
    nlinarith [abs_nonneg z.re, abs_nonneg z.im]
  have hint_k : ∀ k : ℤ,
      IntegrableOn (fun y : ℝ => ((k : ℂ) + y * I).im / (Real.exp (2 * π * y) - 1)) (Ioi 0) := by
    intro k
    simpa using integrableOn_pow_div_exp_mul_sub_one (k := 1) (c := 2 * π) le_rfl (by positivity)
  obtain ⟨ϑ, hϑ_mem, _, hmain⟩ :=
    exists_sum_Icc_eq_abelPlana_bernoulli (f := fun z : ℂ => z) (m := 1) han le_rfl
      contDiff_id.contDiffOn hgrowth (fun _ _ _ => ofReal_im _) (hint_k a) (hint_k n)
  have hd1 : EqOn (iteratedDerivWithin 1 (fun z : ℂ => z) S) (fun _ => 1) S := fun w hw => by
    rw [iteratedDerivWithin_one]
    exact (hasDerivWithinAt_id w S).derivWithin (huniq w hw)
  have hd2 : EqOn (iteratedDerivWithin 2 (fun z : ℂ => z) S) (fun _ => 0) S := fun w hw => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ]
    exact ((hasDerivWithinAt_const w S (1 : ℂ)).congr hd1 (hd1 hw)).derivWithin (huniq w hw)
  let g : ℂ → ℂ := iteratedDerivWithin 2 (fun z : ℂ => z) S
  have hg_im : ∀ y t : ℝ, (g (((n : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I)).im = 0 := fun y t => by
    have hmem : ((n : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I ∈ S := ⟨by simp [han'.le], by simp⟩
    simpa [g] using congrArg Complex.im (hd2 hmem)
  have hsup0 : ∀ y : ℝ,
      sSup ((fun t : ℝ => |(g (((n : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I)).im|) '' Icc 0 1) = 0 := by
    intro y
    simp only [hg_im, abs_zero, (nonempty_Icc.mpr zero_le_one).image_const, csSup_singleton]
  have hrem_bound := abs_two_mul_pow_div_factorial_integral_im_le (g := g) (c := n) (m := 1)
    (ϑ := ϑ) (fun y hy => Ioo_subset_Icc_self (hϑ_mem y hy))
    (fun y _ => by simp only [hg_im]; exact continuousOn_const)
    (by simp only [hsup0, zero_mul, zero_div]; exact integrableOn_zero)
  simp only [hsup0, zero_mul, zero_div, integral_zero, mul_zero] at hrem_bound
  have hrem0 : ∫ y in Ioi (0 : ℝ),
      (iteratedDerivWithin 2 (fun z : ℂ => z) S ((n : ℂ) + ((ϑ y * y : ℝ) : ℂ) * I)).im *
        y ^ 2 / (Real.exp (2 * π * y) - 1) = 0 := by
    have h0 : 2 * (-1 : ℝ) ^ 1 / (2 * 1)! *
        ∫ y in Ioi (0 : ℝ),
          (g (((n : ℝ) : ℂ) + ((ϑ y * y : ℝ) : ℂ) * I)).im *
            y ^ (2 * 1) / (Real.exp (2 * π * y) - 1) = 0 :=
      abs_nonpos_iff.mp hrem_bound
    have hcoeff_ne : (2 * (-1 : ℝ) ^ 1 / (2 * 1)! : ℝ) ≠ 0 := by
      norm_num [Nat.factorial]
    simpa [g] using (mul_eq_zero.mp h0).resolve_left hcoeff_ne
  have hint_a :
      ∫ y in Ioi (0 : ℝ), ((a : ℂ) + y * I).im / (Real.exp (2 * π * y) - 1) = 1 / 24 := by
    simpa using integral_Ioi_div_exp_two_pi_mul_sub_one
  have hint_ab : ∫ x in (a : ℝ)..n, (x : ℂ) = ((n : ℂ) ^ 2 - a ^ 2) / 2 := by
    rw [intervalIntegral.integral_ofReal, integral_id]
    push_cast
    ring
  have hn_S : (n : ℂ) ∈ S := ⟨by simp [han'.le], by simp⟩
  have hb2 : (bernoulli 2 : ℂ) = 1 / 6 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two]
    norm_num
  rw [hmain]
  simp only [Nat.mul_one, Finset.Icc_self, Finset.sum_singleton, Nat.reduceSub]
  rw [hint_ab, hint_a, hd1 hn_S, hb2, hrem0]
  push_cast
  norm_num [Nat.factorial]
  ring

end Examples
