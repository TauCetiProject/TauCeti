/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.NumberTheory.Bernoulli
public import TauCeti.Analysis.Asymptotics.Sum.AbelPlana.Basic

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Complex.VerticalStrip.Basic
import TauCeti.Analysis.Complex.VerticalStrip.Growth
import TauCeti.Analysis.SpecialFunctions.Integrals.BoseEinstein

/-!
# Bernoulli Expansion and Remainder Bound for the Abel–Plana Formula

For `m ≥ 1`, a function `f` that is `(2m)`-times complex continuously differentiable on the closed
vertical strip `Complex.HadamardThreeLines.verticalClosedStrip a b` (`a < b`) and real-valued on
`[a, b]`, and a point `c ∈ [a, b]` such that the half-line integrand
`y ↦ Im f(c + iy) / (e^{2πy} - 1)` is integrable on `(0, ∞)`, expanding `y ↦ Im f(c + iy)` by
Taylor's theorem with Lagrange remainder at `y = 0` and integrating termwise against
`(e^{2πy} - 1)⁻¹` via the Bose–Einstein moments yields the higher-order Abel–Plana expansion
(DLMF 2.10.2):

$$2 \int_0^\infty \frac{\operatorname{Im} f(c + iy)}{e^{2\pi y} - 1}\,dy
  = \sum_{s=1}^m \frac{B_{2s}}{(2s)!}\, f^{(2s-1)}(c)
  + \frac{2(-1)^m}{(2m)!} \int_0^\infty
      \operatorname{Im} f^{(2m)}(c + i\vartheta(y) y)\, \frac{y^{2m}}{e^{2\pi y} - 1}\,dy,$$

where `ϑ(y) ∈ (0, 1)` is the Lagrange intermediate point for each `y > 0`, satisfying the
pointwise Taylor–Lagrange identity for `Im f(c + i y)`. When `a < n` are integers and
`y ↦ Im f(c + iy) / (e^{2πy} - 1)` is integrable on `(0, ∞)` at both `c = a` and `c = n` (along
with `f(z) = o(e^{2π|Im z|})` uniformly in the strip), substituting this expansion at `c = n` into
`TauCeti.sum_Icc_eq_abelPlana` yields the full formula
`TauCeti.exists_sum_Icc_eq_abelPlana_bernoulli`.

## Main results

* `TauCeti.exists_two_mul_integral_im_div_exp_two_pi_sub_one_eq`: Taylor–Bernoulli expansion of the
  Abel–Plana half-line integral `2 ∫₀^∞ Im f(c + iy) / (e^{2πy} - 1) dy` at any `c ∈ [a, b]` with
  Lagrange remainder of order `2m` (`m ≥ 1`) and pointwise Taylor–Lagrange identity, assuming the
  half-line integrand is integrable on `(0, ∞)`.
* `TauCeti.exists_sum_Icc_eq_abelPlana_bernoulli`: the full DLMF 2.10.2 Abel–Plana summation
  formula combining `TauCeti.sum_Icc_eq_abelPlana` with the Bernoulli expansion and pointwise
  Taylor–Lagrange identity at the upper endpoint `c = n`, assuming half-line integrability at both
  `c = a` and `c = n`.
* `TauCeti.abs_two_mul_pow_div_factorial_integral_im_le`: supremum remainder bound
  `|R_m| ≤ 2 / (2m)! * ∫₀^∞ (sup_{0 ≤ t ≤ 1} |Im g(c + ity)|) y^{2m} / (e^{2πy} - 1) dy`
  assuming integrability of both the selected remainder integrand and the supremum envelope.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(i), formula 2.10.2.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §3.3.
-/

public section

open scoped Nat Real Topology
open Complex Filter MeasureTheory Set

namespace TauCeti

/-! ### Main theorems -/

/-- Twice the integrated `s`-th odd Taylor term against `(e^{2πy} - 1)⁻¹` equals
`(B_{2s} / (2s)!) * A`. -/
private lemma two_mul_odd_moment_eq_bernoulli {s : ℕ} (hs : 1 ≤ s) (A : ℝ) :
    2 * (((-1 : ℝ) ^ (s - 1) * A / (2 * s - 1)!) *
      ∫ y in Ioi (0 : ℝ), y ^ (2 * s - 1) / (Real.exp (2 * π * y) - 1)) =
    (bernoulli (2 * s) : ℝ) / (2 * s)! * A := by
  rw [integral_Ioi_pow_div_exp_two_pi_mul_sub_one hs]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hs
  have hs_add : (-1 : ℝ) ^ (k + 1 + 1) = (-1 : ℝ) ^ k := by
    rw [add_assoc, pow_add]; norm_num
  have hs_sq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hfact_s : ((2 * (k + 1))! : ℝ) = (2 * (k + 1 : ℝ)) * ((2 * (k + 1) - 1)! : ℝ) := by
    rw [← Nat.mul_factorial_pred (by omega : 2 * (k + 1) ≠ 0)]
    push_cast; ring
  have hfac_s_ne : ((2 * (k + 1) - 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  rw [Nat.add_sub_cancel, hs_add, hfact_s]
  push_cast at hk_ne ⊢
  field_simp
  linear_combination 4 * (bernoulli (2 * (k + 1)) : ℝ) * A * hs_sq

/-- **Bernoulli–Taylor expansion of the Abel–Plana half-line integral** (DLMF 2.10.2, integral
expansion). Let `f` be `C^{2m}` (`m ≥ 1`) over `ℂ` on the closed vertical strip
`S = {z : ℂ | a ≤ z.re ∧ z.re ≤ b}` (`a < b`) and real on `[a, b]`. For any `c ∈ [a, b]` such that
`y ↦ Im f(c + iy) / (e^{2πy} - 1)` is integrable on `(0, ∞)`, there exists a Lagrange intermediate
point function `ϑ : ℝ → ℝ` with `ϑ(y) ∈ (0, 1)` for every `y > 0` satisfying the pointwise
Taylor–Lagrange identity for `Im f(c + iy)`, such that the remainder integrand is integrable on
`(0, ∞)` and
`2 ∫₀^∞ Im f(c + iy) / (e^{2πy} - 1) dy
  = ∑_{s=1}^m (B_{2s} / (2s)!) Re f^{(2s-1)}(c)
    + (2 (-1)^m / (2m)!) ∫₀^∞ Im f^{(2m)}(c + i ϑ(y) y) y^{2m} / (e^{2πy} - 1) dy`.

Here `a < b` ensures that `S` has nonempty interior so complex iterated derivatives
`iteratedDerivWithin k f S` are uniquely determined up to the boundary lines, and `1 ≤ m` gives
positive Taylor order `2m` so the Lagrange intermediate point lies in `(0, 1)` (the `m = 0` case is
the unexpanded integral). -/
theorem exists_two_mul_integral_im_div_exp_two_pi_sub_one_eq {f : ℂ → ℂ} {a b c : ℝ} {m : ℕ}
    (hab : a < b) (hc : c ∈ Icc a b) (hm : 1 ≤ m)
    (hf : ContDiffOn ℂ (2 * m : ℕ) f (Complex.HadamardThreeLines.verticalClosedStrip a b))
    (hreal : ∀ x : ℝ, a ≤ x → x ≤ b → (f x).im = 0)
    (hint : IntegrableOn (fun y : ℝ => (f (c + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0)) :
    ∃ ϑ : ℝ → ℝ, (∀ y > 0, ϑ y ∈ Ioo (0 : ℝ) 1) ∧
      (∀ y : ℝ, 0 < y → (f (c + y * I)).im =
        (∑ s ∈ Finset.Icc 1 m,
          (-1 : ℝ) ^ (s - 1) *
            (iteratedDerivWithin (2 * s - 1) f
              (Complex.HadamardThreeLines.verticalClosedStrip a b) c).re *
            y ^ (2 * s - 1) / (2 * s - 1)!) +
        (-1 : ℝ) ^ m *
          (iteratedDerivWithin (2 * m) f
            (Complex.HadamardThreeLines.verticalClosedStrip a b)
            (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
          y ^ (2 * m) / (2 * m)!) ∧
      IntegrableOn
        (fun y : ℝ =>
          (iteratedDerivWithin (2 * m) f
            (Complex.HadamardThreeLines.verticalClosedStrip a b)
            (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
            y ^ (2 * m) / (Real.exp (2 * π * y) - 1))
        (Ioi 0) ∧
      2 * (∫ y in Ioi (0 : ℝ), (f (c + y * I)).im / (Real.exp (2 * π * y) - 1)) =
        (∑ s ∈ Finset.Icc 1 m,
          (bernoulli (2 * s) : ℝ) / (2 * s)! *
            (iteratedDerivWithin (2 * s - 1) f
              (Complex.HadamardThreeLines.verticalClosedStrip a b) c).re) +
        2 * (-1 : ℝ) ^ m / (2 * m)! *
          ∫ y in Ioi (0 : ℝ),
            (iteratedDerivWithin (2 * m) f
              (Complex.HadamardThreeLines.verticalClosedStrip a b)
              (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
              y ^ (2 * m) / (Real.exp (2 * π * y) - 1) := by
  classical
  let S : Set ℂ := Complex.HadamardThreeLines.verticalClosedStrip a b
  have hex := fun (y : ℝ) (hy : 0 < y) =>
    exists_im_add_mul_I_eq_taylor_odd hab hc hm hy hf fun x hx => hreal x hx.1 hx.2
  let ϑ : ℝ → ℝ := fun y => if hy : 0 < y then (hex y hy).choose else 1 / 2
  have hϑ_mem : ∀ y > 0, ϑ y ∈ Ioo (0 : ℝ) 1 := fun y hy => by
    simpa [ϑ, hy] using (hex y hy).choose_spec.1
  have hϑ_eq : ∀ (y : ℝ), 0 < y → (f (c + y * I)).im =
      (∑ s ∈ Finset.Icc 1 m,
        (-1 : ℝ) ^ (s - 1) * (iteratedDerivWithin (2 * s - 1) f S c).re *
          y ^ (2 * s - 1) / (2 * s - 1)!) +
      (-1 : ℝ) ^ m * (iteratedDerivWithin (2 * m) f S (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
        y ^ (2 * m) / (2 * m)! := fun y hy => by
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
  -- On `Ioi 0`, the scaled remainder is `LHS - sum`, so `integrable_const_mul_iff` extracts
  -- `remIntegrand`.
  let remIntegrand : ℝ → ℝ := fun y =>
    (iteratedDerivWithin (2 * m) f S (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
      y ^ (2 * m) / (Real.exp (2 * π * y) - 1)
  have hdecomp : EqOn
      (fun y : ℝ => (f (c + y * I)).im / (Real.exp (2 * π * y) - 1))
      (fun y : ℝ => (∑ s ∈ Finset.Icc 1 m, term s y) +
        ((-1 : ℝ) ^ m / (2 * m)!) * remIntegrand y) (Ioi 0) := fun y (hy : 0 < y) => by
    dsimp only [term, remIntegrand]
    rw [hϑ_eq y hy, add_div, Finset.sum_div]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => by ring) (by ring)
  have hrem_scaled_eq : EqOn
      (fun y => ((-1 : ℝ) ^ m / (2 * m)!) * remIntegrand y)
      (fun y => (f (c + y * I)).im / (Real.exp (2 * π * y) - 1) -
        ∑ s ∈ Finset.Icc 1 m, term s y) (Ioi 0) := fun y hy => by
    have hd := hdecomp hy
    dsimp only at hd ⊢
    rw [hd, add_sub_cancel_left]
  have hrem_scaled_int :
      IntegrableOn (fun y => ((-1 : ℝ) ^ m / (2 * m)!) * remIntegrand y) (Ioi 0) :=
    (hint.sub hsum_int).congr_fun hrem_scaled_eq.symm measurableSet_Ioi
  have hcoeff_ne : ((-1 : ℝ) ^ m / (2 * m)! : ℝ) ≠ 0 :=
    div_ne_zero (pow_ne_zero m (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hrem_int : IntegrableOn remIntegrand (Ioi 0) :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hcoeff_ne) remIntegrand).mp hrem_scaled_int
  refine ⟨ϑ, hϑ_mem, hϑ_eq, hrem_int, ?_⟩
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
integers and `1 ≤ m`. If `f` is `C^{2m}` over `ℂ` on
`Complex.HadamardThreeLines.verticalClosedStrip a n`, `f(z) = o(e^{2π|Im z|})` uniformly in the
strip, `f` is real on `[a, n]`, and `y ↦ Im f(c + iy) / (e^{2πy} - 1)` is integrable on `(0, ∞)`
at `c = a` and `c = n`, then there exists `ϑ : ℝ → ℝ` with `ϑ(y) ∈ (0, 1)` for every `y > 0`
satisfying the pointwise Taylor–Lagrange identity for `Im f(n + iy)` such that
`∑_{j=a}^n f(j) = ∫_a^n f + f(a)/2 + f(n)/2
  - 2 ∫_0^∞ Im f(a + iy) / (e^{2πy} - 1) dy
  + ∑_{s=1}^m (B_{2s} / (2s)!) f^{(2s-1)}(n)
  + (2 (-1)^m / (2m)!) ∫_0^∞ Im f^{(2m)}(n + i ϑ(y) y) y^{2m} / (e^{2πy} - 1) dy`.

Here `a < n` gives the closed strip nonempty interior so `iteratedDerivWithin` is uniquely
determined at the boundary `z = n`, and `1 ≤ m` gives positive Taylor order `2m` (for `a = n` or
`m = 0`, see `TauCeti.sum_Icc_eq_abelPlana`). -/
theorem exists_sum_Icc_eq_abelPlana_bernoulli {f : ℂ → ℂ} {a n : ℤ} {m : ℕ}
    (han : a < n) (hm : 1 ≤ m)
    (hf : ContDiffOn ℂ (2 * m : ℕ) f (Complex.HadamardThreeLines.verticalClosedStrip a n))
    (hgrowth : Tendsto (fun z => f z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓
        𝓟 (Complex.HadamardThreeLines.verticalClosedStrip a n)) (𝓝 0))
    (hreal : ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ n → (f x).im = 0)
    (hinta : IntegrableOn (fun y : ℝ => (f (a + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0))
    (hintn : IntegrableOn (fun y : ℝ => (f (n + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0)) :
    ∃ ϑ : ℝ → ℝ, (∀ y > 0, ϑ y ∈ Ioo (0 : ℝ) 1) ∧
      (∀ y : ℝ, 0 < y → (f (n + y * I)).im =
        (∑ s ∈ Finset.Icc 1 m,
          (-1 : ℝ) ^ (s - 1) *
            (iteratedDerivWithin (2 * s - 1) f
              (Complex.HadamardThreeLines.verticalClosedStrip a n) n).re *
            y ^ (2 * s - 1) / (2 * s - 1)!) +
        (-1 : ℝ) ^ m *
          (iteratedDerivWithin (2 * m) f
            (Complex.HadamardThreeLines.verticalClosedStrip a n)
            (n + ((ϑ y * y : ℝ) : ℂ) * I)).im *
          y ^ (2 * m) / (2 * m)!) ∧
      IntegrableOn
        (fun y : ℝ =>
          (iteratedDerivWithin (2 * m) f
            (Complex.HadamardThreeLines.verticalClosedStrip a n)
            (n + ((ϑ y * y : ℝ) : ℂ) * I)).im *
            y ^ (2 * m) / (Real.exp (2 * π * y) - 1))
        (Ioi 0) ∧
      ∑ j ∈ Finset.Icc a n, f j =
        (∫ x in (a : ℝ)..n, f x) + f a / 2 + f n / 2 -
          2 * ((∫ y in Ioi (0 : ℝ), (f (a + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) +
          (∑ s ∈ Finset.Icc 1 m,
            ((bernoulli (2 * s) : ℂ) / (2 * s)!) *
              iteratedDerivWithin (2 * s - 1) f
                (Complex.HadamardThreeLines.verticalClosedStrip a n) n) +
          (2 * (-1 : ℂ) ^ m / (2 * m)!) *
            ((∫ y in Ioi (0 : ℝ),
              (iteratedDerivWithin (2 * m) f
                (Complex.HadamardThreeLines.verticalClosedStrip a n)
                (n + ((ϑ y * y : ℝ) : ℂ) * I)).im *
                y ^ (2 * m) / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) := by
  let S : Set ℂ := Complex.HadamardThreeLines.verticalClosedStrip a n
  have han' : (a : ℝ) < n := by exact_mod_cast han
  have hdiff_open : DifferentiableOn ℂ f (Complex.HadamardThreeLines.verticalStrip a n) :=
    (hf.differentiableOn (by simp; omega)).mono
      (TauCeti.Complex.HadamardThreeLines.verticalStrip_subset_verticalClosedStrip a n)
  have hintn' : IntegrableOn
      (fun y : ℝ => (f (((n : ℝ) : ℂ) + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0) := by
    simpa using hintn
  obtain ⟨ϑ, hϑ_mem, hϑ_pt, hϑ_int, hϑ_eq⟩ :=
    exists_two_mul_integral_im_div_exp_two_pi_sub_one_eq han' ⟨han'.le, le_rfl⟩ hm hf hreal hintn'
  refine ⟨ϑ, hϑ_mem, by simpa only [ofReal_intCast] using hϑ_pt, by simpa using hϑ_int, ?_⟩
  rw [sum_Icc_eq_abelPlana han.le hdiff_open hf.continuousOn hgrowth hreal hinta hintn]
  simp only [ofReal_intCast] at hϑ_eq
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) hϑ_eq
  push_cast at hcast
  have hsum_cast :
      (∑ s ∈ Finset.Icc 1 m,
        ((bernoulli (2 * s) : ℂ) / (2 * s)!) *
          (((iteratedDerivWithin (2 * s - 1) f S n).re : ℝ) : ℂ)) =
      ∑ s ∈ Finset.Icc 1 m,
        ((bernoulli (2 * s) : ℂ) / (2 * s)!) * iteratedDerivWithin (2 * s - 1) f S n := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have him0 : (iteratedDerivWithin (2 * s - 1) f S ((n : ℝ) : ℂ)).im = 0 :=
      hf.im_iteratedDerivWithin_verticalClosedStrip_eq_zero han' ⟨han'.le, le_rfl⟩
        (by have := (Finset.mem_Icc.mp hs).2; exact_mod_cast (by omega : 2 * s - 1 ≤ 2 * m))
        fun x hx => hreal x hx.1 hx.2
    have hre_eq : (((iteratedDerivWithin (2 * s - 1) f S n).re : ℝ) : ℂ) =
        iteratedDerivWithin (2 * s - 1) f S n :=
      Complex.ext rfl (by simpa using him0.symm)
    rw [hre_eq]
  rw [hsum_cast] at hcast
  simp only [← ofReal_mul] at hcast
  linear_combination hcast

/-- **Supremum bound for the Abel–Plana Lagrange remainder** (DLMF 2.10.2). If `ϑ(y) ∈ [0, 1]`,
`t ↦ Im g(c + i t y)` is continuous on `[0, 1]` for every `y > 0`, the selected remainder integrand
is integrable on `(0, ∞)`, and the supremum envelope is integrable against `y^{2m} / (e^{2πy} - 1)`
on `(0, ∞)`, then
`|2 (-1)^m / (2m)! * ∫₀^∞ Im g(c + i ϑ(y) y) y^{2m} / (e^{2πy} - 1) dy|
  ≤ 2 / (2m)! * ∫₀^∞ (sup_{t ∈ [0, 1]} |Im g(c + i t y)|) y^{2m} / (e^{2πy} - 1) dy`. -/
theorem abs_two_mul_pow_div_factorial_integral_im_le {g : ℂ → ℂ} {c : ℝ} {m : ℕ} {ϑ : ℝ → ℝ}
    (hϑ : ∀ y > 0, ϑ y ∈ Icc (0 : ℝ) 1)
    (hcont : ∀ y > 0, ContinuousOn (fun t : ℝ => (g (c + ((t * y : ℝ) : ℂ) * I)).im) (Icc 0 1))
    (hint_rem : IntegrableOn
      (fun y : ℝ =>
        (g (c + ((ϑ y * y : ℝ) : ℂ) * I)).im * y ^ (2 * m) / (Real.exp (2 * π * y) - 1))
      (Ioi 0))
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
    simp [abs_div, abs_mul]
  rw [abs_mul, hcoeff]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_ae hint_rem.norm hint ?_)
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
  have hgrowth :=
    (hasVerticalStripGrowth_const (c := (1 : ℂ))).tendsto_mul_exp_neg_mul_abs_im Real.two_pi_pos a n
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
  have him_sq : ∀ (k : ℤ) (y : ℝ), (((k : ℂ) + y * I) ^ 2).im = 2 * (k : ℝ) * y := fun k y => by
    simp [sq]; ring
  have hint_k : ∀ k : ℤ,
      IntegrableOn (fun y : ℝ => (((k : ℂ) + y * I) ^ 2).im / (Real.exp (2 * π * y) - 1))
        (Ioi 0) := fun k =>
    IntegrableOn.congr_fun
      ((integrableOn_pow_div_exp_mul_sub_one (k := 1) (c := 2 * π) le_rfl
        (by positivity)).const_mul (2 * (k : ℝ)))
      (fun y _ => by rw [him_sq]; ring) measurableSet_Ioi
  have hint_val : ∀ k : ℤ,
      ∫ y in Ioi (0 : ℝ), (((k : ℂ) + y * I) ^ 2).im / (Real.exp (2 * π * y) - 1) =
        (k : ℝ) / 12 := fun k => by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun y _ => by rw [him_sq]; ring : EqOn _
        (fun y => (2 * (k : ℝ)) * (y / (Real.exp (2 * π * y) - 1))) (Ioi 0)),
      integral_const_mul, integral_Ioi_div_exp_two_pi_mul_sub_one]
    ring
  have hmain := sum_Icc_eq_abelPlana (f := fun z : ℂ => z ^ 2) han
    (differentiable_id.pow 2).differentiableOn (continuous_id.pow 2).continuousOn
    ((hasVerticalStripGrowth_id.pow 2).tendsto_mul_exp_neg_mul_abs_im Real.two_pi_pos a n)
    (fun _ _ _ => by norm_cast) (hint_k a) (hint_k n)
  have hint_ab : ∫ x in (a : ℝ)..n, (x : ℂ) ^ 2 = ((n : ℂ) ^ 3 - a ^ 3) / 3 := by
    simp_rw [← Complex.ofReal_pow]
    rw [intervalIntegral.integral_ofReal, integral_pow]
    push_cast; ring
  rw [hmain, hint_ab, hint_val a, hint_val n]
  push_cast; ring

-- Linear function `f(z) = z` (`a < n`, `m = 1`): exercises both
-- `exists_sum_Icc_eq_abelPlana_bernoulli` (where `(B_2 / 2!) f'(n) = 1 / 12` cancels
-- `-2 ∫₀^∞ Im(a + iy) / (e^{2πy} - 1) dy = -1 / 12`) and
-- `abs_two_mul_pow_div_factorial_integral_im_le` (which bounds the `2m = 2` remainder by `0`).
example {a n : ℤ} (han : a < n) :
    ∑ j ∈ Finset.Icc a n, (j : ℂ) =
      ((n : ℂ) ^ 2 - a ^ 2) / 2 + ((a : ℂ) + n) / 2 := by
  let S : Set ℂ := Complex.HadamardThreeLines.verticalClosedStrip a n
  have han' : (a : ℝ) < n := by exact_mod_cast han
  have huniq : UniqueDiffOn ℂ S :=
    TauCeti.Complex.HadamardThreeLines.uniqueDiffOn_verticalClosedStrip han'
  have hgrowth : Tendsto (fun z : ℂ => z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 S) (𝓝 0) :=
    hasVerticalStripGrowth_id.tendsto_mul_exp_neg_mul_abs_im Real.two_pi_pos a n
  have hint_k : ∀ k : ℤ,
      IntegrableOn (fun y : ℝ => ((k : ℂ) + y * I).im / (Real.exp (2 * π * y) - 1)) (Ioi 0) :=
    fun _ => by
      simpa using integrableOn_pow_div_exp_mul_sub_one (k := 1) (c := 2 * π) le_rfl (by positivity)
  obtain ⟨ϑ, hϑ_mem, _, hϑ_int, hmain⟩ :=
    exists_sum_Icc_eq_abelPlana_bernoulli (f := fun z : ℂ => z) (m := 1) han le_rfl
      contDiff_id.contDiffOn hgrowth (fun _ _ _ => ofReal_im _) (hint_k a) (hint_k n)
  let g : ℂ → ℂ := iteratedDerivWithin 2 (fun z : ℂ => z) S
  have hnS : (n : ℂ) ∈ S :=
    TauCeti.Complex.HadamardThreeLines.mem_verticalClosedStrip_iff.mpr ⟨by simp [han'.le], by simp⟩
  have hd1 : iteratedDerivWithin 1 (fun z : ℂ => z) S n = 1 := by
    simp [iteratedDerivWithin_fun_id hnS huniq]
  have hd2 : ∀ u : ℝ, g (((n : ℝ) : ℂ) + (u : ℂ) * I) = 0 := fun u => by
    have hzS : (((n : ℝ) : ℂ) + (u : ℂ) * I) ∈ S :=
      TauCeti.Complex.HadamardThreeLines.mem_verticalClosedStrip_iff.mpr (by simp [han'.le])
    dsimp only [g]
    rw [iteratedDerivWithin_fun_id hzS huniq]
    simp
  have hg_im : ∀ u : ℝ, (g (((n : ℝ) : ℂ) + (u : ℂ) * I)).im = 0 := fun u => by
    rw [hd2 u, zero_im]
  have hsup0 : ∀ y : ℝ,
      sSup ((fun t : ℝ => |(g (((n : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I)).im|) '' Icc 0 1) = 0 :=
    fun _ => by
      simp only [hg_im, abs_zero, (nonempty_Icc.mpr zero_le_one).image_const, csSup_singleton]
  have hrem_bound := abs_two_mul_pow_div_factorial_integral_im_le (g := g) (c := n) (m := 1)
    (ϑ := ϑ) (fun y hy => Ioo_subset_Icc_self (hϑ_mem y hy))
    (fun _ _ => by simp only [hg_im]; exact continuousOn_const)
    (by simpa [g] using hϑ_int)
    (by simp only [hsup0, zero_mul, zero_div]; exact integrableOn_zero)
  simp only [hsup0, zero_mul, zero_div, integral_zero, mul_zero] at hrem_bound
  have hrem0 : ∫ y in Ioi (0 : ℝ),
      (iteratedDerivWithin 2 (fun z : ℂ => z) S ((n : ℂ) + ((ϑ y * y : ℝ) : ℂ) * I)).im *
        y ^ 2 / (Real.exp (2 * π * y) - 1) = 0 := by
    have h0 := abs_nonpos_iff.mp hrem_bound
    simpa [g] using (mul_eq_zero.mp h0).resolve_left (by norm_num [Nat.factorial])
  have hint_a :
      ∫ y in Ioi (0 : ℝ), ((a : ℂ) + y * I).im / (Real.exp (2 * π * y) - 1) = 1 / 24 := by
    simpa using integral_Ioi_div_exp_two_pi_mul_sub_one
  have hint_ab : ∫ x in (a : ℝ)..n, (x : ℂ) = ((n : ℂ) ^ 2 - a ^ 2) / 2 := by
    rw [intervalIntegral.integral_ofReal, integral_id]; push_cast; ring
  have hb2 : (bernoulli 2 : ℂ) = 1 / 6 := by
    rw [bernoulli_two]; norm_num
  rw [hmain]
  simp only [Nat.mul_one, Finset.Icc_self, Finset.sum_singleton, Nat.reduceSub]
  rw [hint_ab, hint_a, hd1, hb2, hrem0]
  push_cast; norm_num [Nat.factorial]; ring

end Examples
