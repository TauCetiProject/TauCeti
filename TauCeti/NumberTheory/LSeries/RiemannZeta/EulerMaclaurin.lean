/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.NumberTheory.ZetaValues

/-!
# Euler–Maclaurin continuation and derivatives of the Riemann zeta function

Applying the even-order Euler–Maclaurin summation formula on `[1, N]` to `x ↦ (x : ℂ) ^ (-s)` and
letting `N → ∞` on `1 < Re s` represents `riemannZeta s` as a rational-plus-polynomial sum plus a
tail integral on `(1, ∞)` against `(B_{2m} - B_{2m}({x})) / (2m)! * (x : ℂ) ^ (-s - 2m)`. Because
that tail integral is a Mellin transform of a bounded function supported on `[1, ∞)`, it is
holomorphic on the whole half-plane `1 - 2m < Re s`; by the identity theorem for `(s - 1) ζ(s)`,
the Euler–Maclaurin representation continues `riemannZeta s` to `1 - 2m < Re s`, `s ≠ 1`.

Specializing `m = 2` near `s = -1` isolates a factor `(s + 1)` in front of the remainder integral,
evaluating `deriv riemannZeta (-1)` in terms of `∫ x in Ioi 1, (B_4 - B_4({x})) * x ^ (-3 : ℤ)`
without differentiating under the integral sign. Differentiating the functional equation
`riemannZeta_one_sub` at `s = 2` then relates `1 / 12 - deriv riemannZeta (-1)` to
`deriv riemannZeta 2` and Euler's constant `γ` (DLMF 2.10.6).

## Main results

* `TauCeti.deriv_riemannZeta_conj`, `TauCeti.riemannZeta_im_ofReal`, and
  `TauCeti.deriv_riemannZeta_im_ofReal`: conjugation symmetry of `deriv riemannZeta` and reality
  of `riemannZeta` and `deriv riemannZeta` on `ℝ`.
* `TauCeti.riemannZeta_eq_eulerMaclaurin`: the order-`2m` Euler–Maclaurin representation of
  `riemannZeta s` on `1 - 2m < Re s`, `s ≠ 1`, together with its real specialization
  `TauCeti.riemannZeta_neg_ofReal_re_eq_eulerMaclaurin`.
* `TauCeti.deriv_riemannZeta_neg_one` and `TauCeti.deriv_riemannZeta_neg_one_re`: integral
  evaluation of `ζ'(-1)` via `B_4 - B_4({x})`.
* `TauCeti.one_div_twelve_sub_deriv_riemannZeta_neg_one` and
  `TauCeti.one_div_twelve_sub_deriv_riemannZeta_neg_one_re`:
  `1 / 12 - ζ'(-1) = (γ + log(2π)) / 12 - ζ'(2) / (2π²)` (DLMF 2.10.6).

## References

* NIST *Digital Library of Mathematical Functions*, §§2.10(i), 25.2(ii), formulas 2.10.6 and
  25.2.9.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §2.
-/

public section

open Complex Filter Finset intervalIntegral MeasureTheory
open scoped Nat Real Topology

namespace TauCeti

/-! ### Conjugation symmetry and real arguments -/

/-- Complex conjugation commutes with `deriv riemannZeta`. -/
@[simp]
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (deriv riemannZeta s) := by
  have hfn : (starRingEnd ℂ ∘ riemannZeta ∘ starRingEnd ℂ) = riemannZeta :=
    funext fun z => by simp [riemannZeta_conj]
  have h := congrFun (deriv_conj_conj (f := riemannZeta)) s
  rw [hfn] at h
  simpa using congrArg (starRingEnd ℂ) h.symm

/-- At every real argument `x`, `riemannZeta x` has zero imaginary part. -/
@[simp]
theorem riemannZeta_im_ofReal (x : ℝ) : (riemannZeta x).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using (riemannZeta_conj x).symm)

/-- At every real argument `x`, `deriv riemannZeta x` has zero imaginary part. -/
@[simp]
theorem deriv_riemannZeta_im_ofReal (x : ℝ) : (deriv riemannZeta x).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using (deriv_riemannZeta_conj x).symm)

/-! ### Holomorphy of the Euler–Maclaurin tail integral -/

/-- Derivative of `x ↦ (descPochhammer ℂ i).eval (-s) * (x : ℂ) ^ (-s - i)` on `(0, ∞)`. -/
private theorem hasDerivAt_descPochhammer_mul_ofReal_cpow (s : ℂ) (i : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (descPochhammer ℂ i).eval (-s) * (y : ℂ) ^ (-s - i))
      ((descPochhammer ℂ (i + 1)).eval (-s) * (x : ℂ) ^ (-s - (i + 1 : ℕ))) x := by
  rcases eq_or_ne (-s - i) 0 with h0 | h0
  · have hfn : (fun y : ℝ => (descPochhammer ℂ i).eval (-s) * (y : ℂ) ^ (-s - i)) =
        fun _ => (descPochhammer ℂ i).eval (-s) := by ext y; simp [h0]
    rw [hfn, descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_natCast, h0, mul_zero, zero_mul]
    exact hasDerivAt_const x _
  · have hd := (hasDerivAt_ofReal_cpow_const hx.ne' h0).const_mul ((descPochhammer ℂ i).eval (-s))
    refine hd.congr_deriv ?_
    rw [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_natCast, Nat.cast_add, Nat.cast_one]
    ring_nf

/-- Express the Euler–Maclaurin tail integral on `(1, ∞)` as a Mellin transform. -/
private theorem tailIntegral_eq_mellin (m : ℕ) (s : ℂ) :
    ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
          (x : ℂ) ^ (-s - 2 * m) =
      mellin ((Set.Ici (1 : ℝ)).indicator fun x : ℝ =>
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ))
        (1 - s - 2 * m) := by
  set ψ : ℝ → ℂ := fun x =>
    ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ)
  have hEq : Set.EqOn
      (fun x : ℝ => (x : ℂ) ^ (1 - s - 2 * m - 1) • (Set.Ici (1 : ℝ)).indicator ψ x)
      ((Set.Ici (1 : ℝ)).indicator fun x => ψ x * (x : ℂ) ^ (-s - 2 * m)) (Set.Ioi 0) := by
    intro x _
    by_cases hx : 1 ≤ x
    · simp only [Set.indicator_of_mem (Set.mem_Ici.mpr hx), smul_eq_mul, mul_comm]
      ring_nf
    · simp [Set.indicator_of_notMem (Set.notMem_Ici.mpr (not_le.mp hx))]
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hEq, setIntegral_indicator measurableSet_Ici,
    Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr zero_lt_one), integral_Ici_eq_integral_Ioi]

/-- The Euler–Maclaurin tail integral on `(1, ∞)` is complex-differentiable on
`1 - 2 * m < Re s` for `m ≥ 1`. -/
private theorem differentiableAt_tailIntegral {m : ℕ} (hm : 1 ≤ m) {s : ℂ}
    (hs : 1 - 2 * (m : ℝ) < s.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
          (x : ℂ) ^ (-z - 2 * m)) s := by
  set ψ : ℝ → ℂ := (Set.Ici (1 : ℝ)).indicator fun x : ℝ =>
    (((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℝ)
  have hψ_eq : ψ = (Set.Ici (1 : ℝ)).indicator fun x : ℝ =>
      ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) := by
    ext x; by_cases hx : 1 ≤ x <;> simp [ψ, hx]
  have hmeas : Measurable ψ :=
    Measurable.indicator (Complex.measurable_ofReal.comp
      ((measurable_const.sub
        ((continuous_bernoulliFun (2 * m)).measurable.comp measurable_fract)).div
        measurable_const)) measurableSet_Ici
  have hbound : ∀ x : ℝ, ‖ψ x‖ ≤ 2 * |(bernoulli (2 * m) : ℝ)| / (2 * m)! := fun x => by
    by_cases hx : 1 ≤ x
    · simp only [ψ, Set.indicator_of_mem (Set.mem_Ici.mpr hx), Complex.norm_real,
        Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 * m)!)]
      exact div_le_div_of_nonneg_right
        (abs_bernoulli_sub_bernoulliFun_fract_le (by omega) x) (by positivity)
    · dsimp [ψ]
      rw [Set.indicator_of_notMem (Set.notMem_Ici.mpr (not_le.mp hx)), norm_zero]; positivity
  have hloc : LocallyIntegrableOn ψ (Set.Ioi 0) := fun x _ =>
    ⟨Set.Ioo (x - 1) (x + 1), nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) (by linarith)),
      IntegrableOn.of_bound measure_Ioo_lt_top hmeas.aestronglyMeasurable _
        (Filter.Eventually.of_forall fun y => hbound y)⟩
  have htop : ψ =O[atTop] fun x : ℝ => x ^ (-(0 : ℝ)) :=
    Asymptotics.isBigO_iff.mpr ⟨2 * |(bernoulli (2 * m) : ℝ)| / (2 * m)!, by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
      simpa [Real.rpow_zero] using hbound x⟩
  have hbot : ψ =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-((1 - s - 2 * m).re - 1)) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
    simp [ψ, Set.indicator_of_notMem (Set.notMem_Ici.mpr hx.2)]
  have hre : (1 - s - 2 * (m : ℂ)).re < 0 := by
    simp only [sub_re, one_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero,
      sub_zero]
    linarith
  have hd : DifferentiableAt ℂ (mellin ψ) (1 - s - 2 * m) :=
    mellin_differentiableAt_of_isBigO_rpow hloc htop hre hbot (sub_one_lt _)
  have hmellin : DifferentiableAt ℂ (fun z : ℂ => mellin ψ (1 - z - 2 * m)) s := by
    simpa [Function.comp_def] using
      hd.comp s (((differentiableAt_const (1 : ℂ)).fun_sub differentiableAt_id).fun_sub
        (differentiableAt_const (2 * (m : ℂ))))
  simp_rw [tailIntegral_eq_mellin, ← hψ_eq]
  exact hmellin

/-- Finite-interval Euler–Maclaurin identity on `[1, N]` for `∑_{j=1}^N 1 / j ^ s` (`s ≠ 1`). -/
private theorem sum_Icc_one_div_cpow_eq_eulerMaclaurin {s : ℂ} (hs₁ : s ≠ 1) {m N : ℕ}
    (hm : 1 ≤ m) (hN1 : 1 ≤ N) :
    ∑ j ∈ Icc 1 N, (1 / (j : ℂ) ^ s) =
      ((N : ℂ) ^ (-s + 1) - 1) / (-s + 1) + 1 / 2 + (N : ℂ) ^ (-s) / 2 +
        ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
          ((descPochhammer ℂ (2 * r - 1)).eval (-s) * ((N : ℂ) ^ (-s - (2 * r - 1 : ℕ)) - 1)) +
        (descPochhammer ℂ (2 * m)).eval (-s) *
          ∫ x in (1 : ℝ)..N,
            ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
              (x : ℂ) ^ (-s - 2 * m) := by
  set g : ℕ → ℝ → ℂ := fun i x => (descPochhammer ℂ i).eval (-s) * (x : ℂ) ^ (-s - i)
  have hs1 : -s ≠ -1 := fun h => hs₁ (neg_inj.mp h)
  have h0pos : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) N := by
    rw [Set.uIcc_of_le (by exact_mod_cast hN1), Set.mem_Icc]; intro h; linarith [h.1]
  have hcont : ∀ i, ContinuousOn (g i) (Set.Icc ((1 : ℤ) : ℝ) ((N : ℤ) : ℝ)) := fun i x hx => by
    have hx1 : 1 ≤ x := by simpa using hx.1
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const x _
      (Or.inr (by linarith)))).continuousWithinAt
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt_two_mul (g := g)
    (a := 1) (n := (N : ℤ)) (by exact_mod_cast hN1) hm (fun i _ => hcont i)
    (fun i _ x hx => hasDerivAt_descPochhammer_mul_ofReal_cpow s i
      (zero_lt_one.trans (by simpa using hx.1)))
    ((hcont (2 * m)).intervalIntegrable_of_Icc (by exact_mod_cast hN1))
  have hsum_cast : ∑ j ∈ Icc 1 N, (1 / (j : ℂ) ^ s) = ∑ j ∈ Icc (1 : ℤ) N, g 0 j := by
    have himg : (Icc 1 N).image (Nat.cast : ℕ → ℤ) = Icc (1 : ℤ) N := by
      ext z; simp only [mem_image, mem_Icc]
      exact ⟨fun ⟨k, hk, hkz⟩ => hkz ▸ ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩,
        fun hz => ⟨z.toNat, ⟨by omega, by omega⟩, by omega⟩⟩
    rw [← himg, Finset.sum_image (f := fun j : ℤ => g 0 (j : ℝ)) Nat.cast_injective.injOn]
    exact sum_congr rfl fun j _ => by simp [g, cpow_neg, one_div]
  have hint0 : ∫ x in (1 : ℝ)..N, g 0 x = ((N : ℂ) ^ (-s + 1) - 1) / (-s + 1) := by
    have : (fun x : ℝ => g 0 x) = fun x : ℝ => (x : ℂ) ^ (-s) := by ext x; simp [g]
    rw [this, integral_cpow (Or.inr ⟨hs1, h0pos⟩), ofReal_one, one_cpow, ofReal_natCast]
  have hrem : ∫ x in (1 : ℝ)..N,
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)!) • g (2 * m) x =
      (descPochhammer ℂ (2 * m)).eval (-s) *
        ∫ x in (1 : ℝ)..N,
          ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
            (x : ℂ) ^ (-s - 2 * m) := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_congr fun x _ => by simp only [g, Complex.real_smul]; push_cast; ring
  rw [Int.cast_one, Int.cast_natCast] at hEM
  rw [hsum_cast, hEM, hint0, hrem]
  simp only [g, Complex.real_smul, descPochhammer_zero, Polynomial.eval_one, one_mul,
    Nat.cast_zero, sub_zero, ofReal_one, one_cpow, ofReal_natCast]
  have hsum_mid : ∑ x ∈ Ico 1 m, (((bernoulli (2 * x) : ℝ) / (2 * x)! : ℝ) : ℂ) *
        ((descPochhammer ℂ (2 * x - 1)).eval (-s) * (N : ℂ) ^ (-s - (2 * x - 1 : ℕ)) -
          (descPochhammer ℂ (2 * x - 1)).eval (-s) * 1) =
      ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
        ((descPochhammer ℂ (2 * r - 1)).eval (-s) *
          ((N : ℂ) ^ (-s - (2 * r - 1 : ℕ)) - 1)) :=
    sum_congr rfl fun r _ => by push_cast; ring
  rw [hsum_mid]
  push_cast; ring

/-- Integrability of the order-`2m` Euler–Maclaurin tail on `(1, ∞)` when `1 < Re s`. -/
private theorem integrableOn_tail_of_one_lt_re {s : ℂ} (m : ℕ) (hs : 1 < s.re) :
    IntegrableOn
      (fun x : ℝ => ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
        (x : ℂ) ^ (-s - 2 * m)) (Set.Ioi 1) := by
  have hre : (-s - 2 * (m : ℂ)).re < -1 := by
    simp only [sub_re, neg_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero,
      sub_zero]
    linarith
  refine IntegrableOn.congr_fun
    (((integrableOn_Ioi_cpow_of_lt hre zero_lt_one).bernoulli_sub_bernoulliFun_fract_smul
      (2 * m)).smul ((2 * m)! : ℝ)⁻¹) (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.smul_apply, Complex.real_smul]; push_cast; ring

/-- Limit of the finite Euler–Maclaurin formula on `[1, N]` as `N → ∞` when `1 < Re s`. -/
private theorem riemannZeta_eq_eulerMaclaurin_of_one_lt_re {s : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hs : 1 < s.re) :
    riemannZeta s = 1 / (s - 1) + 1 / 2 -
      ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
        (descPochhammer ℂ (2 * r - 1)).eval (-s) +
      (descPochhammer ℂ (2 * m)).eval (-s) *
        ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
            (x : ℂ) ^ (-s - 2 * m) := by
  have hs₁ : s ≠ 1 := fun h => by simp [h] at hs
  have hpow0 : ∀ w : ℂ, w.re < 0 → Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := fun w hw =>
    tendsto_zero_iff_norm_tendsto_zero.mpr <|
      (tendsto_rpow_neg_atTop (neg_pos.mpr hw)).comp tendsto_natCast_atTop_atTop |>.congr' <| by
        filter_upwards [eventually_gt_atTop 0] with N hN; simp [Complex.norm_natCast_cpow_of_pos hN]
  have hLHS : Tendsto (fun N : ℕ => ∑ j ∈ Icc 1 N, (1 / (j : ℂ) ^ s)) atTop
      (𝓝 (riemannZeta s)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs,
      show (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) = ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ s from
        tsum_congr fun n => by push_cast; rfl]
    refine ((Complex.summable_one_div_nat_cpow.mpr hs).comp_injective
      (add_left_injective 1)).hasSum.tendsto_sum_nat.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N _
    rw [← Finset.Ico_add_one_right_eq_Icc 1 N, Finset.sum_Ico_eq_sum_range]
    exact sum_congr rfl fun k _ => by simp [add_comm]
  have hint_tail := integrableOn_tail_of_one_lt_re m hs
  have hRHS : Tendsto (fun N : ℕ =>
      ((N : ℂ) ^ (-s + 1) - 1) / (-s + 1) + 1 / 2 + (N : ℂ) ^ (-s) / 2 +
        ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
          ((descPochhammer ℂ (2 * r - 1)).eval (-s) * ((N : ℂ) ^ (-s - (2 * r - 1 : ℕ)) - 1)) +
        (descPochhammer ℂ (2 * m)).eval (-s) * ∫ x in (1 : ℝ)..N,
          ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
            (x : ℂ) ^ (-s - 2 * m)) atTop
      (𝓝 ((0 - 1) / (-s + 1) + 1 / 2 + 0 / 2 +
        ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
          ((descPochhammer ℂ (2 * r - 1)).eval (-s) * (0 - 1)) +
        (descPochhammer ℂ (2 * m)).eval (-s) * ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
            (x : ℂ) ^ (-s - 2 * m))) :=
    (((((hpow0 _ (by simp; linarith)).sub tendsto_const_nhds).div_const _).add
      tendsto_const_nhds).add ((hpow0 _ (by simp; linarith)).div_const _)).add
      (tendsto_finsetSum _ fun r _ => (((hpow0 _ (by simp; linarith)).sub
        tendsto_const_nhds).const_mul _).const_mul _) |>.add
      ((intervalIntegral_tendsto_integral_Ioi 1 hint_tail
        tendsto_natCast_atTop_atTop).const_mul _)
  have heq := tendsto_nhds_unique hLHS (hRHS.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    exact (sum_Icc_one_div_cpow_eq_eulerMaclaurin hs₁ hm hN1).symm))
  rw [heq, show -s + 1 = -(s - 1) by ring, zero_sub, div_neg, neg_div, neg_neg, zero_div, add_zero,
    sub_eq_add_neg (1 / (s - 1) + 1 / 2), ← Finset.sum_neg_distrib]
  exact congrArg (· + _) (congrArg (1 / (s - 1) + 1 / 2 + ·) (sum_congr rfl fun _ _ => by ring))

/-- **Euler–Maclaurin continuation of `riemannZeta`** (DLMF 25.2.9). For `m ≥ 1` and every `s ≠ 1`
in the half-plane `1 - 2 * m < Re s`,
`ζ(s) = 1 / (s - 1) + 1 / 2 - ∑_{r=1}^{m-1} B_{2r}/(2r)! * (-s)_{2r-1}
  + (-s)_{2m} * ∫_1^∞ (B_{2m} - B_{2m}({x}))/(2m)! * x^(-s - 2m) dx`,
where `(z)_k` denotes the descending Pochhammer polynomial `(descPochhammer ℂ k).eval z`. -/
theorem riemannZeta_eq_eulerMaclaurin {s : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hs : 1 - 2 * (m : ℝ) < s.re) (hs₁ : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + 1 / 2 -
      ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
        (descPochhammer ℂ (2 * r - 1)).eval (-s) +
      (descPochhammer ℂ (2 * m)).eval (-s) *
        ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
            (x : ℂ) ^ (-s - 2 * m) := by
  -- Clear the simple pole at `s = 1` by multiplying by `s - 1` on the convex half-plane.
  set H : ℂ → ℂ := fun z => 1 / 2 -
    ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
      (descPochhammer ℂ (2 * r - 1)).eval (-z) +
    (descPochhammer ℂ (2 * m)).eval (-z) *
      ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
          (x : ℂ) ^ (-z - 2 * m)
  have hopen : IsOpen {z : ℂ | 1 - 2 * (m : ℝ) < z.re} :=
    isOpen_lt continuous_const continuous_re
  have hpoly : ∀ k : ℕ, Differentiable ℂ (fun z : ℂ => (descPochhammer ℂ k).eval (-z)) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      simp_rw [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_natCast]
      exact ih.mul (differentiable_neg.sub_const _)
  have hH_diff : DifferentiableOn ℂ H {z : ℂ | 1 - 2 * (m : ℝ) < z.re} := fun z hz =>
    ((((differentiableAt_const _).sub
      (DifferentiableAt.fun_sum fun r _ => ((hpoly _).differentiableAt).const_mul _)).add
      (((hpoly _).differentiableAt).mul
        (differentiableAt_tailIntegral hm hz)))).differentiableWithinAt
  have hF : AnalyticOnNhd ℂ (fun z => 1 + (z - 1) * H z) {z : ℂ | 1 - 2 * (m : ℝ) < z.re} :=
    ((differentiableOn_const 1).add ((differentiableOn_id.sub_const 1).mul hH_diff)).analyticOnNhd
      hopen
  have hZ : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | 1 - 2 * (m : ℝ) < z.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hopen
  have heq : (fun z => 1 + (z - 1) * H z) =ᶠ[𝓝 (2 : ℂ)] riemannZeta₁ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz1 : z ≠ 1 := fun h => by simp [h] at hz
    have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    calc
      1 + (z - 1) * H z = (z - 1) * (1 / (z - 1) + H z) := by field_simp
      _ = (z - 1) * riemannZeta z := by
        rw [riemannZeta_eq_eulerMaclaurin_of_one_lt_re hm hz]; dsimp [H]; ring
      _ = riemannZeta₁ z := by rw [riemannZeta_eq_inv_sub_mul hz1]; field_simp
  have h2mem : (2 : ℂ) ∈ {z : ℂ | 1 - 2 * (m : ℝ) < z.re} := by
    simp only [Set.mem_ofPred, re_ofNat]; linarith
  have hid := hF.eqOn_of_preconnected_of_eventuallyEq hZ
    (convex_halfSpace_re_gt _).isPreconnected h2mem heq hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  rw [riemannZeta_eq_inv_sub_mul hs₁, ← hid]
  dsimp [H]; field_simp; ring

/-- Real specialization of `riemannZeta_eq_eulerMaclaurin` at `-α` for real `α ≠ -1` with
`α < 2 * m - 1`. -/
theorem riemannZeta_neg_ofReal_re_eq_eulerMaclaurin {α : ℝ} (hα : α ≠ -1) {m : ℕ} (hm : 1 ≤ m)
    (hαm : α < 2 * (m : ℝ) - 1) :
    (riemannZeta (-α : ℂ)).re = -1 / (α + 1) + 1 / 2 -
      ∑ r ∈ Ico 1 m, (bernoulli (2 * r) : ℝ) / (2 * r)! *
        (descPochhammer ℝ (2 * r - 1)).eval α +
      (descPochhammer ℝ (2 * m)).eval α *
        ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! *
            x ^ (α - 2 * m) := by
  have hs : 1 - 2 * (m : ℝ) < (-(α : ℂ)).re := by simp; linarith
  have hs1 : (-(α : ℂ)) ≠ 1 := fun h => hα (by
    have := congrArg re h; simp at this; linarith)
  have hpoch : ∀ k : ℕ, (descPochhammer ℂ k).eval (-(-(α : ℂ))) =
      (((descPochhammer ℝ k).eval α : ℝ) : ℂ) := fun k => by
    simp [descPochhammer_eval_eq_prod_range]
  have hint_eq : ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
          (x : ℂ) ^ (-(-(α : ℂ)) - 2 * m) =
      ((∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! *
          x ^ (α - 2 * m) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [ofReal_mul, ofReal_cpow (zero_lt_one.trans hx).le]
    push_cast; congr 2; ring
  have hζ := riemannZeta_eq_eulerMaclaurin hm hs hs1
  have h1 : (1 : ℂ) / (-(α : ℂ) - 1) = ((-1 / (α + 1) : ℝ) : ℂ) := by
    have hne : (α : ℂ) + 1 ≠ 0 := by exact_mod_cast fun h : α + 1 = 0 => hα (by linarith)
    push_cast; field_simp; ring
  have hsum_eq : ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
        (descPochhammer ℂ (2 * r - 1)).eval (-(-(α : ℂ))) =
      ((∑ r ∈ Ico 1 m, (bernoulli (2 * r) : ℝ) / (2 * r)! *
        (descPochhammer ℝ (2 * r - 1)).eval α : ℝ) : ℂ) := by
    push_cast
    exact sum_congr rfl fun r _ => by rw [hpoch]
  have hhalf : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
  rw [hζ, h1, hsum_eq, hpoch, hint_eq]
  simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, hhalf]

/-! ### Evaluation of `ζ'(-1)` and DLMF 2.10.6 -/

/-- Integral representation of `deriv riemannZeta (-1)` from the order-`4` Euler–Maclaurin
formula:
`ζ'(-1) = -1/6 - 1/12 * ∫_1^∞ (B_4 - B_4({x})) * x ^ (-3 : ℤ) dx`. -/
theorem deriv_riemannZeta_neg_one :
    deriv riemannZeta (-1) = -1 / 6 - (1 / 12 : ℂ) *
      ∫ x in Set.Ioi (1 : ℝ),
        (((bernoulli 4 : ℝ) - bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-3 : ℤ) := by
  set I : ℂ → ℂ := fun z => ∫ x in Set.Ioi (1 : ℝ),
    ((bernoulli 4 - bernoulliFun 4 (Int.fract x)) / (4 : ℕ)! : ℂ) * (x : ℂ) ^ (-z - 2 * (2 : ℕ))
  set G : ℂ → ℂ := fun z => z * (z + 2) * (z + 3) * I z
  have hev : riemannZeta =ᶠ[𝓝 (-1 : ℂ)]
      fun z => 1 / (z - 1) + 1 / 2 + z / 12 + (z + 1) * G z := by
    filter_upwards [((isOpen_lt continuous_const continuous_re).inter
      isOpen_compl_singleton).mem_nhds
      ⟨(by norm_num : (1 - 2 * (2 : ℝ)) < (-1 : ℂ).re), (by norm_num : (-1 : ℂ) ≠ 1)⟩] with z hz
    have hsum : ∑ r ∈ Ico 1 2, (bernoulli (2 * r) / (2 * r)! : ℂ) *
        (descPochhammer ℂ (2 * r - 1)).eval (-z) = -z / 12 := by
      rw [Nat.Ico_succ_singleton]
      simp [descPochhammer_eval_eq_prod_range,
        bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two, Nat.factorial]
      ring
    have hpoch4 : (descPochhammer ℂ 4).eval (-z) = (z + 1) * (z * (z + 2) * (z + 3)) := by
      simp [descPochhammer_eval_eq_prod_range, Finset.prod_range_succ]; ring
    rw [riemannZeta_eq_eulerMaclaurin (m := 2) (by omega) hz.1 hz.2, hsum, show 2 * 2 = 4 from rfl,
      hpoch4]
    dsimp [G, I]; ring
  have hd1 : HasDerivAt (fun z : ℂ => 1 / (z - 1)) (-1 / 4) (-1) := by
    simpa [one_div] using
      (((hasDerivAt_id' (-1 : ℂ)).sub_const 1).fun_inv (by norm_num)).congr_deriv (by norm_num)
  have hd2 : HasDerivAt (fun z : ℂ => z / 12) (1 / 12) (-1) := by
    simpa using (hasDerivAt_id' (-1 : ℂ)).div_const (12 : ℂ)
  have hG_diff : DifferentiableAt ℂ G (-1) :=
    (((differentiableAt_id.mul (differentiableAt_id.add_const 2)).mul
      (differentiableAt_id.add_const 3)).mul
      (differentiableAt_tailIntegral (m := 2) (by omega) (s := -1) (by norm_num)))
  have hdG : HasDerivAt (fun z : ℂ => (z + 1) * G z) (G (-1)) (-1) := by
    simpa using ((hasDerivAt_id' (-1 : ℂ)).add_const 1).fun_mul hG_diff.hasDerivAt
  rw [((((hd1.add (hasDerivAt_const (-1 : ℂ) (1 / 2))).add hd2).add hdG).congr_of_eventuallyEq
    hev).deriv]
  have hG_val : G (-1) = -(1 / 12 : ℂ) * ∫ x in Set.Ioi (1 : ℝ),
      (((bernoulli 4 : ℝ) - bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-3 : ℤ) := by
    dsimp [G, I]
    rw [show (-1 : ℂ) * (-1 + 2) * (-1 + 3) = -2 by ring, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [show (-(-1 : ℂ) - 2 * 2 : ℂ) = ((-3 : ℤ) : ℂ) by norm_num, cpow_intCast,
      show (4 : ℕ)! = 24 by decide]
    push_cast; ring
  rw [hG_val]; ring

/-- Real-part form of `deriv_riemannZeta_neg_one`:
`(deriv riemannZeta (-1)).re = -1/6 - 1/12 * ∫_1^∞ (B_4 - B_4({x})) * x ^ (-3 : ℤ) dx`. -/
theorem deriv_riemannZeta_neg_one_re :
    (deriv riemannZeta (-1)).re = -1 / 6 - (1 / 12 : ℝ) *
      ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli 4 : ℝ) - bernoulliFun 4 (Int.fract x)) * x ^ (-3 : ℤ) := by
  have hint : ∫ x in Set.Ioi (1 : ℝ),
        (((bernoulli 4 : ℝ) - bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-3 : ℤ) =
      ((∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli 4 : ℝ) - bernoulliFun 4 (Int.fract x)) * x ^ (-3 : ℤ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp
  have h := congrArg re deriv_riemannZeta_neg_one
  have h6 : (-1 / 6 : ℂ).re = (-1 / 6 : ℝ) := by norm_num
  have h12 : (1 / 12 : ℂ).re = (1 / 12 : ℝ) := by norm_num
  have h12i : (1 / 12 : ℂ).im = 0 := by norm_num
  rw [hint] at h
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, h6, h12, h12i, mul_zero, sub_zero] at h
  exact h

/-- **Functional-equation evaluation of `1 / 12 - ζ'(-1)`** (DLMF 2.10.6, complex form):
`1 / 12 - deriv riemannZeta (-1) = (γ + log(2π)) / 12 - deriv riemannZeta 2 / (2π²)`. -/
theorem one_div_twelve_sub_deriv_riemannZeta_neg_one :
    1 / 12 - deriv riemannZeta (-1) =
      (Real.eulerMascheroniConstant + Complex.log (2 * π)) / 12 -
        deriv riemannZeta 2 / (2 * π ^ 2) := by
  set L : ℂ := Complex.log (2 * π)
  have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hev : (fun z : ℂ => riemannZeta (1 - z)) =ᶠ[𝓝 (2 : ℂ)]
      fun z => 2 * (2 * π) ^ (-z) * Gamma z * Complex.cos (π * z / 2) * riemannZeta z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact riemannZeta_one_sub
      (fun n h => by simp [h] at hz; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
      (fun h => by simp [h] at hz)
  have hd_lhs : HasDerivAt (fun z : ℂ => riemannZeta (1 - z)) (-deriv riemannZeta (-1)) 2 := by
    have h := (differentiableAt_riemannZeta (s := 1 - (2 : ℂ)) (by norm_num)).hasDerivAt.comp
      (2 : ℂ) ((hasDerivAt_const (2 : ℂ) (1 : ℂ)).sub (hasDerivAt_id' 2))
    simpa [Function.comp_def, show (1 : ℂ) - 2 = -1 by ring] using h
  have hd_pow : HasDerivAt (fun z : ℂ => 2 * (2 * π : ℂ) ^ (-z)) (-L / (2 * π ^ 2)) 2 := by
    have h := ((hasDerivAt_neg' (2 : ℂ)).const_cpow (c := 2 * π) (Or.inl h2π)).const_mul 2
    refine h.congr_deriv ?_
    rw [show -(2 : ℂ) = ((-2 : ℤ) : ℂ) by norm_num, cpow_intCast, zpow_neg, zpow_ofNat]
    dsimp [L]; field_simp
  have hd_gam : HasDerivAt Gamma (1 - Real.eulerMascheroniConstant) 2 := by
    have h := Complex.hasDerivAt_Gamma_nat 1
    simp only [Nat.factorial_one, Nat.cast_one, one_mul, harmonic_succ, zero_add,
      harmonic_zero] at h
    simpa [show (-Real.eulerMascheroniConstant : ℂ) + 1 = 1 - Real.eulerMascheroniConstant by ring,
      show (1 : ℂ) + 1 = 2 by norm_num] using h
  have hd_cos : HasDerivAt (fun z : ℂ => Complex.cos (π * z / 2)) 0 2 := by
    have hlin : HasDerivAt (fun z : ℂ => π * z / 2) (π / 2) 2 := by
      simpa using ((hasDerivAt_id' (2 : ℂ)).const_mul (π : ℂ)).div_const 2
    simpa [mul_div_cancel_right₀ (π : ℂ) two_ne_zero] using hlin.ccos
  have hd_zeta : HasDerivAt riemannZeta (deriv riemannZeta 2) 2 :=
    (differentiableAt_riemannZeta (by norm_num)).hasDerivAt
  have hval_pow : 2 * (2 * π : ℂ) ^ (-(2 : ℂ)) = 1 / (2 * π ^ 2) := by
    rw [show -(2 : ℂ) = ((-2 : ℤ) : ℂ) by norm_num, cpow_intCast, zpow_neg, zpow_ofNat]
    field_simp
  have hval_gam : Gamma (2 : ℂ) = 1 := by simp
  have hval_cos : Complex.cos (π * (2 : ℂ) / 2) = -1 := by
    rw [mul_div_cancel_right₀ (π : ℂ) two_ne_zero, Complex.cos_pi]
  have hd_rhs := (((hd_pow.fun_mul hd_gam).fun_mul hd_cos).fun_mul hd_zeta).congr_of_eventuallyEq
    hev
  have heq := hd_lhs.unique hd_rhs
  rw [hval_pow, hval_gam, hval_cos, riemannZeta_two] at heq
  linear_combination (norm := (field_simp; ring)) heq

/-- **DLMF 2.10.6** (real form):
`1 / 12 - (deriv riemannZeta (-1)).re = (γ + log(2π)) / 12 - (deriv riemannZeta 2).re / (2π²)`. -/
theorem one_div_twelve_sub_deriv_riemannZeta_neg_one_re :
    1 / 12 - (deriv riemannZeta (-1)).re =
      (Real.eulerMascheroniConstant + Real.log (2 * π)) / 12 -
        (deriv riemannZeta 2).re / (2 * π ^ 2) := by
  have hlog : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [← ofReal_ofNat, ← ofReal_mul, ofReal_log Real.two_pi_pos.le]
  have h := congrArg re one_div_twelve_sub_deriv_riemannZeta_neg_one
  have h12 : (1 / 12 : ℂ).re = (1 / 12 : ℝ) := by norm_num
  have hmid : (((Real.eulerMascheroniConstant : ℂ) + Complex.log (2 * π)) / 12).re =
      (Real.eulerMascheroniConstant + Real.log (2 * π)) / 12 := by
    rw [hlog, ← ofReal_add, show (12 : ℂ) = ((12 : ℝ) : ℂ) by norm_num, div_ofReal_re, ofReal_re]
  have hlast : (deriv riemannZeta 2 / (2 * (π : ℂ) ^ 2)).re =
      (deriv riemannZeta 2).re / (2 * π ^ 2) := by
    rw [show (2 * (π : ℂ) ^ 2 : ℂ) = ((2 * π ^ 2 : ℝ) : ℂ) by push_cast; ring, div_ofReal_re]
  simp only [sub_re] at h
  linarith [h, h12, hmid, hlast]

end TauCeti
