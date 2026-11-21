/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.NumberTheory.Bernoulli
public import TauCeti.Analysis.Asymptotics.Sum.AbelPlana.Basic

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Analysis.Calculus.IteratedDeriv.Within
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Complex.VerticalStrip.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.BoseEinstein

/-!
# Bernoulli Expansion and Remainder Bound for the Abel–Plana Formula

For `m ≥ 1`, a function `f` that is `(2m)`-times complex continuously differentiable on a closed
vertical strip `S = {z : ℂ | a ≤ z.re ∧ z.re ≤ b}` (`a < b`) and real-valued on `[a, b]`, and a
point `c ∈ [a, b]` such that the half-line integrand `y ↦ Im f(c + iy) / (e^{2πy} - 1)` is
integrable on `(0, ∞)`, expanding `y ↦ Im f(c + iy)` by Taylor's theorem with Lagrange remainder at
`y = 0` and integrating termwise against `(e^{2πy} - 1)⁻¹` via the Bose–Einstein moments yields the
higher-order Abel–Plana expansion (DLMF 2.10.2):

$$2 \int_0^\infty \frac{\operatorname{Im} f(c + iy)}{e^{2\pi y} - 1}\,dy
  = \sum_{s=1}^m \frac{B_{2s}}{(2s)!}\, f^{(2s-1)}(c)
  + \frac{2(-1)^m}{(2m)!} \int_0^\infty
      \operatorname{Im} f^{(2m)}(c + i\vartheta(y) y)\, \frac{y^{2m}}{e^{2\pi y} - 1}\,dy,$$

where `ϑ(y) ∈ (0, 1)` is the Lagrange intermediate point for each `y > 0`. When `a < n` are integers
and `y ↦ Im f(c + iy) / (e^{2πy} - 1)` is integrable on `(0, ∞)` at both `c = a` and `c = n` (along
with `f(z) = o(e^{2π|Im z|})` uniformly in the strip), substituting this expansion at `c = n` into
`TauCeti.sum_Icc_eq_abelPlana` yields the full formula
`TauCeti.exists_sum_Icc_eq_abelPlana_bernoulli`.

## Main results

* `TauCeti.exists_two_mul_integral_im_div_exp_two_pi_sub_one_eq`: Taylor–Bernoulli expansion of the
  Abel–Plana half-line integral `2 ∫₀^∞ Im f(c + iy) / (e^{2πy} - 1) dy` at any `c ∈ [a, b]` with
  Lagrange remainder of order `2m` (`m ≥ 1`), assuming the half-line integrand is integrable on
  `(0, ∞)`.
* `TauCeti.exists_sum_Icc_eq_abelPlana_bernoulli`: the full DLMF 2.10.2 Abel–Plana summation
  formula combining `TauCeti.sum_Icc_eq_abelPlana` with the Bernoulli expansion at the upper
  endpoint `c = n`, assuming half-line integrability at both `c = a` and `c = n`.
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

/-! ### Taylor–Lagrange expansion along a vertical line -/

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
  have huniqS : UniqueDiffOn ℂ S :=
    TauCeti.Complex.HadamardThreeLines.uniqueDiffOn_verticalClosedStrip hab
  let γ : ℝ → ℂ := fun t => (c : ℂ) + t • I
  have hγ_mem : ∀ t : ℝ, γ t ∈ S := fun t => by simp [S, γ, Complex.real_smul, hc.1, hc.2]
  have hfγ : ContDiff ℝ (2 * m : ℕ) (f ∘ γ) :=
    (hf.restrict_scalars ℝ).comp_contDiff (by fun_prop) hγ_mem
  let ψ : ℝ → ℝ := Complex.imCLM ∘ (f ∘ γ)
  have hψ : ContDiff ℝ (2 * m : ℕ) ψ := Complex.imCLM.contDiff.comp hfγ
  have hψ_deriv : ∀ {k : ℕ}, k ≤ 2 * m → ∀ t : ℝ,
      iteratedDeriv k ψ t = (I ^ k * iteratedDerivWithin k f S ((c : ℂ) + (t : ℂ) * I)).im := by
    intro k hk t
    have hk' : (k : WithTop ℕ∞) ≤ ((2 * m : ℕ) : WithTop ℕ∞) := by exact_mod_cast hk
    rw [Complex.imCLM.iteratedDeriv_comp_left hfγ.contDiffAt hk']
    have hline := hf.iteratedDeriv_comp_add_smul huniqS hγ_mem hk' t
    simpa [γ, S, Function.comp_def, Complex.real_smul, smul_eq_mul] using congrArg Complex.im hline
  have h2m : (2 * m - 1) + 1 = 2 * m := by omega
  have hψ_on : ContDiffOn ℝ (((2 * m - 1 : ℕ) : WithTop ℕ∞) + 1) ψ (uIcc 0 y) := by
    have h1 : ContDiffOn ℝ (2 * m : ℕ) ψ (uIcc 0 y) := hψ.contDiffOn
    rwa [← h2m, Nat.cast_add, Nat.cast_one] at h1
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hy.ne hψ_on
  rw [uIoo_of_lt hy] at hξ_mem
  refine ⟨ξ / y, ⟨div_pos hξ_mem.1 hy, (div_lt_one hy).mpr hξ_mem.2⟩, ?_⟩
  have hθy : ξ / y * y = ξ := div_mul_cancel₀ ξ hy.ne'
  have hIeven : ∀ k : ℕ, I ^ (2 * k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := fun k => by
    rw [pow_mul, I_sq]; push_cast; rfl
  have him_zero : ∀ {k : ℕ}, k ≤ 2 * m → (iteratedDerivWithin k f S c).im = 0 := by
    intro k hk
    have hmaps : MapsTo (fun t : ℝ => (0 : ℂ) + t • (1 : ℂ)) (Icc a b) S := fun t ht => by
      simp [S, Complex.real_smul, ht.1, ht.2]
    have h := hf.map_pow_smul_iteratedDerivWithin_eq_zero huniqS (uniqueDiffOn_Icc hab) hmaps
      Complex.imCLM (fun t ht => by simpa [Complex.real_smul] using hreal t ht.1 ht.2)
      (by exact_mod_cast hk : (k : WithTop ℕ∞) ≤ ((2 * m : ℕ) : WithTop ℕ∞)) hc
    simpa [Complex.real_smul] using h
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
      have hψk : iteratedDeriv k ψ 0 = (I ^ k * iteratedDerivWithin k f S c).im := by
        simpa using hψ_deriv hk_le 0
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hy.ne)
        (hψ.contDiffAt.of_le (by exact_mod_cast hk_le)) left_mem_uIcc,
        hψk, sub_zero, smul_eq_mul]
      ring
    rw [hcongr, Finset.sum_range_two_mul]
    have heven : ∑ j ∈ Finset.range m,
        (I ^ (2 * j) * iteratedDerivWithin (2 * j) f S c).im * y ^ (2 * j) / ((2 * j)! : ℝ) =
        0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_le : 2 * j ≤ 2 * m := by
        have := Finset.mem_range.mp hj; omega
      rw [hIeven j, mul_im, ofReal_re, ofReal_im, him_zero hj_le]; ring
    rw [heven, zero_add]
    refine Finset.sum_nbij' (· + 1) (· - 1)
      (fun j hj => Finset.mem_Icc.mpr (by have := Finset.mem_range.mp hj; omega))
      (fun s hs => Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hs; omega))
      (fun _ _ => by omega) (fun s hs => by have := Finset.mem_Icc.mp hs; omega) fun j _ => ?_
    have hsub : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [hsub, Nat.add_sub_cancel, pow_succ, hIeven j, mul_assoc, mul_im, ofReal_re, ofReal_im,
      I_mul_im, I_mul_re]
    ring
  have hrem : iteratedDeriv ((2 * m - 1) + 1) ψ ξ * (y - 0) ^ ((2 * m - 1) + 1) /
        ((2 * m - 1) + 1)! =
      (-1 : ℝ) ^ m * (iteratedDerivWithin (2 * m) f S (c + ((ξ / y * y : ℝ) : ℂ) * I)).im *
        y ^ (2 * m) / (2 * m)! := by
    rw [h2m, hψ_deriv le_rfl ξ, hθy, sub_zero, hIeven m, mul_im, ofReal_re, ofReal_im, zero_mul,
      add_zero]
  have hψy : ψ y = (f (c + (y : ℂ) * I)).im := by simp [ψ, γ, Complex.real_smul]
  linarith [hξ_eq, htaylor, hrem, hψy]

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
    push_cast; rfl
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
  have hex := fun (y : ℝ) (hy : 0 < y) => exists_im_add_mul_I_eq_taylor_odd hab hc hm hy hf hreal
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
  -- On `Ioi 0`, the remainder integrand is a constant multiple of `LHS - sum`, hence integrable.
  let remIntegrand : ℝ → ℝ := fun y =>
    (iteratedDerivWithin (2 * m) f S (c + ((ϑ y * y : ℝ) : ℂ) * I)).im *
      y ^ (2 * m) / (Real.exp (2 * π * y) - 1)
  have hfac_ne : ((2 * m)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsign_sq : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hdecomp : EqOn
      (fun y : ℝ => (f (c + y * I)).im / (Real.exp (2 * π * y) - 1))
      (fun y : ℝ => (∑ s ∈ Finset.Icc 1 m, term s y) +
        ((-1 : ℝ) ^ m / (2 * m)!) * remIntegrand y) (Ioi 0) := fun y (hy : 0 < y) => by
    dsimp only [term, remIntegrand]
    rw [hϑ_eq y hy, add_div, Finset.sum_div]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => by ring) (by ring)
  have hrem_eqOn : EqOn remIntegrand
      (fun y => ((-1 : ℝ) ^ m * (2 * m)!) *
        ((f (c + y * I)).im / (Real.exp (2 * π * y) - 1) -
          ∑ s ∈ Finset.Icc 1 m, term s y)) (Ioi 0) := fun y hy => by
    have hd := hdecomp hy
    dsimp only at hd ⊢
    rw [hd, add_sub_cancel_left]
    field_simp [hfac_ne]
    linear_combination -remIntegrand y * hsign_sq
  have hrem_int : IntegrableOn remIntegrand (Ioi 0) :=
    IntegrableOn.congr_fun ((hint.sub hsum_int).const_mul ((-1 : ℝ) ^ m * (2 * m)!))
      hrem_eqOn.symm measurableSet_Ioi
  refine ⟨ϑ, hϑ_mem, hrem_int, ?_⟩
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
  have huniqS : UniqueDiffOn ℂ S :=
    TauCeti.Complex.HadamardThreeLines.uniqueDiffOn_verticalClosedStrip han'
  have hmaps : MapsTo (fun t : ℝ => (0 : ℂ) + t • (1 : ℂ)) (Icc (a : ℝ) n) S :=
    fun t ht => by simp [S, Complex.real_smul, ht.1, ht.2]
  have hsum_cast :
      (∑ s ∈ Finset.Icc 1 m,
        (((bernoulli (2 * s) : ℝ) / (2 * s)! *
          (iteratedDerivWithin (2 * s - 1) f S n).re : ℝ) : ℂ)) =
      ∑ s ∈ Finset.Icc 1 m,
        ((bernoulli (2 * s) : ℂ) / (2 * s)!) * iteratedDerivWithin (2 * s - 1) f S n := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have him0 : (iteratedDerivWithin (2 * s - 1) f S ((n : ℝ) : ℂ)).im = 0 := by
      have hk : ((2 * s - 1 : ℕ) : WithTop ℕ∞) ≤ ((2 * m : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast (by have := (Finset.mem_Icc.mp hs).2; omega : 2 * s - 1 ≤ 2 * m)
      simpa [Complex.real_smul] using
        hf.map_pow_smul_iteratedDerivWithin_eq_zero huniqS (uniqueDiffOn_Icc han') hmaps
          Complex.imCLM (fun t ht => by simpa [Complex.real_smul] using hreal t ht.1 ht.2)
          hk ⟨han'.le, le_rfl⟩
    have hre_eq : (((iteratedDerivWithin (2 * s - 1) f S n).re : ℝ) : ℂ) =
        iteratedDerivWithin (2 * s - 1) f S n :=
      Complex.ext rfl (by simpa using him0.symm)
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

private lemma tendsto_pow_strip_growth (a n : ℤ) (k : ℕ) :
    Tendsto (fun z : ℂ => z ^ k * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) (𝓝 0) := by
  let M : ℝ := max |(a : ℝ)| |(n : ℝ)|
  refine tendsto_mul_exp_neg_two_pi_abs_im_of_norm_le (C := (M + 1) ^ k) (p := k) (c := 0)
    (by positivity) fun z hza hzb => ?_
  have hre_abs : |z.re| ≤ M := abs_le.mpr
    ⟨by linarith [le_max_left |(a : ℝ)| |(n : ℝ)|, neg_abs_le (a : ℝ), hza],
      by linarith [le_max_right |(a : ℝ)| |(n : ℝ)|, le_abs_self (n : ℝ), hzb]⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have hz : ‖z‖ ≤ (M + 1) * (1 + |z.im|) :=
    (norm_le_abs_re_add_abs_im z).trans (by nlinarith [abs_nonneg z.im])
  rw [norm_pow, zero_mul, Real.exp_zero, mul_one, Real.rpow_natCast, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg z) hz k

-- Constant function `f(z) = 1`: both half-line integrals vanish and the formula reads
-- `∑_{j=a}^n 1 = (n - a) + 1/2 + 1/2`.
example {a n : ℤ} (han : a ≤ n) :
    ∑ _j ∈ Finset.Icc a n, (1 : ℂ) = ((n : ℂ) - a) + 1 := by
  have hgrowth : Tendsto (fun z : ℂ => (1 : ℂ) * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) (𝓝 0) := by
    simpa using tendsto_pow_strip_growth a n 0
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
    (tendsto_pow_strip_growth a n 2) (fun _ _ _ => by norm_cast) (hint_k a) (hint_k n)
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
  let S : Set ℂ := {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}
  have han' : (a : ℝ) < n := by exact_mod_cast han
  have huniq : UniqueDiffOn ℂ S :=
    TauCeti.Complex.HadamardThreeLines.uniqueDiffOn_verticalClosedStrip han'
  have hgrowth : Tendsto (fun z : ℂ => z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 S) (𝓝 0) := by
    simpa using tendsto_pow_strip_growth a n 1
  have hint_k : ∀ k : ℤ,
      IntegrableOn (fun y : ℝ => ((k : ℂ) + y * I).im / (Real.exp (2 * π * y) - 1)) (Ioi 0) :=
    fun _ => by
      simpa using integrableOn_pow_div_exp_mul_sub_one (k := 1) (c := 2 * π) le_rfl (by positivity)
  obtain ⟨ϑ, hϑ_mem, _, hmain⟩ :=
    exists_sum_Icc_eq_abelPlana_bernoulli (f := fun z : ℂ => z) (m := 1) han le_rfl
      contDiff_id.contDiffOn hgrowth (fun _ _ _ => ofReal_im _) (hint_k a) (hint_k n)
  have hd1 : EqOn (iteratedDerivWithin 1 (fun z : ℂ => z) S) (fun _ => 1) S := fun w hw => by
    rw [iteratedDerivWithin_one]
    exact (hasDerivWithinAt_id w S).derivWithin (huniq w hw)
  have hd2 : EqOn (iteratedDerivWithin 2 (fun z : ℂ => z) S) (fun _ => 0) S := fun w hw => by
    rw [← one_add_one_eq_two, iteratedDerivWithin_succ]
    exact ((hasDerivWithinAt_const w S (1 : ℂ)).congr hd1 (hd1 hw)).derivWithin (huniq w hw)
  let g : ℂ → ℂ := iteratedDerivWithin 2 (fun z : ℂ => z) S
  have hg_im : ∀ y t : ℝ, (g (((n : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I)).im = 0 := fun y t => by
    simpa [g] using congrArg Complex.im (hd2 ⟨by simp [han'.le], by simp⟩)
  have hsup0 : ∀ y : ℝ,
      sSup ((fun t : ℝ => |(g (((n : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I)).im|) '' Icc 0 1) = 0 :=
    fun _ => by
      simp only [hg_im, abs_zero, (nonempty_Icc.mpr zero_le_one).image_const, csSup_singleton]
  have hrem_bound := abs_two_mul_pow_div_factorial_integral_im_le (g := g) (c := n) (m := 1)
    (ϑ := ϑ) (fun y hy => Ioo_subset_Icc_self (hϑ_mem y hy))
    (fun _ _ => by simp only [hg_im]; exact continuousOn_const)
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
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two]; norm_num
  rw [hmain]
  simp only [Nat.mul_one, Finset.Icc_self, Finset.sum_singleton, Nat.reduceSub]
  rw [hint_ab, hint_a, hd1 ⟨by simp [han'.le], by simp⟩, hb2, hrem0]
  push_cast; norm_num [Nat.factorial]; ring

end Examples
