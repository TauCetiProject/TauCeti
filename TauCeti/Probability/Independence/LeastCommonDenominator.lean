/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Analysis.InnerProductSpace.Euclidean.LeastCommonDenominator
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Bochner.CharFun.Basic
import TauCeti.MeasureTheory.Integral.LayerCake
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Modulus
import TauCeti.Probability.Independence.CharacteristicFunction

/-!
# Small-ball probabilities through the least common denominator

Let `ξ k` be independent real random variables with a common law `μ` satisfying the Lévy
concentration bound `μ (closedBall v 1) ≤ 1 - b` for every `v`, and let `a` be a nonzero real
vector. If the essential least common denominator `LCD_{α,γ}(a)` of `a`
(`TauCeti.leastCommonDenominator`) is at least `L > 0`, then for every `ε ≥ 0` and every `v`,

`P (|∑ k, a k * ξ k - v| ≤ ε) ≤ 16 π (ε + L⁻¹) / (γ ‖a‖ √b) + 4 exp (1 - α² b / 2)`

(`iIndepFun.measureReal_abs_sum_mul_sub_le_le_of_ofReal_le_leastCommonDenominator`).
So the less arithmetic structure the coefficients have, the more spread out the weighted sum is:
for `ε ≥ L⁻¹` the small-ball probability is of order `ε / (γ ‖a‖ √b)`, up to the error
`exp (1 - α² b / 2)`, which is exponentially small in `n` for `α` of order `√n`. For an
incompressible unit vector `a`,
`TauCeti.IsIncompressibleVector.ofReal_sqrt_div_two_le_leastCommonDenominator` provides `L` of
order `√n`. Applied to the coordinates of a random vector against a unit normal of an independent
random hyperplane, this is how Rudelson and Vershynin bound the distance from a random vector to
a random hyperplane, the key step in their lower bound for the least singular value of a square
random matrix.

The proof combines Esseen's inequality
(`ProbabilityTheory.iIndepFun.measureReal_abs_sum_mul_sub_le_le_integral_prod_norm_charFun`) with
the conditioning bound `TauCeti.prod_norm_charFun_le_setAverage_exp`, applied on the set of
`|w| ≥ 1`, which carries mass at least `b` for the symmetrized law of `μ`. For a fixed `w` with
`|w| ≥ 1`, the frequencies `t` at which `∑ k, (1 - cos (a k * t * w))` is small bring the dilation
`(t w / (2π)) • a` close to an integer point, and the recurrence bound
`TauCeti.volume_setOf_mem_Icc_exists_norm_smul_sub_le_le` controls their measure through the LCD.

## References

* M. Rudelson and R. Vershynin, *Smallest singular value of a random rectangular matrix*,
  Comm. Pure Appl. Math. 62 (2009), Theorem 3.3, here in dimension `m = 1` and with explicit
  constants. Their condition `ε ≥ 1 / LCD_{α,γ}(a)` is replaced by the term `L⁻¹` of the bound.
* O. Friedland and S. Sodin, *Bounds on the concentration function in terms of Diophantine
  approximation*, C. R. Math. Acad. Sci. Paris 345 (2007), 513–518. Rudelson and Vershynin follow
  an argument communicated to them by Friedland and Sodin, and so does the proof here.
-/

public section

open MeasureTheory ProbabilityTheory Metric Set Real
open scoped ENNReal NNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι] {α γ L : ℝ} {a : EuclideanSpace ℝ ι}

/-- For `1 ≤ |w|`, `c > 0` and `r < 2 c α²`, the frequencies `t ∈ (-ε⁻¹, ε⁻¹]` at which
`c * ∑ k, (1 - cos (a k * t * w)) < r` form a set of measure at most
`(4 / (ε L) + 2π) * (√(r / (2c)) / (γ ‖a‖))`, where `L > 0` is at most the LCD of `a`. -/
private theorem volume_setOf_mul_sum_one_sub_cos_lt_inter_Ioc_le {ε c w r : ℝ} (hL : 0 < L)
    (hγ : 0 < γ) (ha : a ≠ 0) (hLa : ENNReal.ofReal L ≤ leastCommonDenominator α γ a)
    (hε : 0 < ε) (hc : 0 < c) (hw : 1 ≤ |w|) (hα : 0 < α) (hrα : r < 2 * c * α ^ 2) :
    volume ({t | c * ∑ k, (1 - cos (a k * t * w)) < r} ∩ Ioc (-ε⁻¹) ε⁻¹) ≤
      ENNReal.ofReal ((4 / (ε * L) + 2 * π) * (√(r / (2 * c)) / (γ * ‖a‖))) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    norm_num at hw
  set d := w / (2 * π) with hd
  have hd0 : d ≠ 0 := div_ne_zero hw0 (by positivity)
  set s := √(r / (8 * c))
  have hs2 : 2 * s = √(r / (2 * c)) := by
    have : r / (2 * c) = 2 ^ 2 * (r / (8 * c)) := by field_simp; ring
    rw [this, sqrt_mul (by positivity), sqrt_sq zero_le_two]
  have hsα : 2 * s < α := by
    rw [hs2, sqrt_lt' hα, div_lt_iff₀ (by positivity)]
    linarith
  set T := |d| / ε with hT
  -- At a frequency of the set, `(t * d) • a` is within `s` of the rounded integer point.
  have hsub : {t | c * ∑ k, (1 - cos (a k * t * w)) < r} ∩ Ioc (-ε⁻¹) ε⁻¹ ⊆
      (· * d) ⁻¹' {θ ∈ Icc (-T) T | ∃ p : ι → ℤ, ‖θ • a - latticePoint p‖ ≤ s} := by
    rintro t ⟨hlt, ht⟩
    replace hlt : c * ∑ k, (1 - cos (a k * t * w)) < r := hlt
    refine ⟨?_, fun k ↦ round (((t * d) • a) k), ?_⟩
    · rw [mem_Icc, ← abs_le, abs_mul, hT, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (abs_le.2 ⟨ht.1.le, ht.2⟩) (abs_nonneg d)
    have h8 := eight_mul_norm_sub_latticePoint_round_sq_le_sum_one_sub_cos ((t * d) • a)
    have hsum : ∑ k, (1 - cos (2 * π * ((t * d) • a) k)) = ∑ k, (1 - cos (a k * t * w)) :=
      Finset.sum_congr rfl fun k _ ↦ by
        rw [PiLp.smul_apply, smul_eq_mul, hd]
        field_simp
    rw [hsum] at h8
    refine ((lt_sqrt (norm_nonneg _)).2 ?_).le
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  calc
    volume ({t | c * ∑ k, (1 - cos (a k * t * w)) < r} ∩ Ioc (-ε⁻¹) ε⁻¹) ≤
        volume ((· * d) ⁻¹' {θ ∈ Icc (-T) T | ∃ p : ι → ℤ, ‖θ • a - latticePoint p‖ ≤ s}) :=
      measure_mono hsub
    _ = ENNReal.ofReal |d⁻¹| *
        volume {θ ∈ Icc (-T) T | ∃ p : ι → ℤ, ‖θ • a - latticePoint p‖ ≤ s} :=
      Real.volume_preimage_mul_right hd0 _
    _ ≤ ENNReal.ofReal |d⁻¹| * ENNReal.ofReal ((4 * T / L + 1) * (2 * s / (γ * ‖a‖))) := by
      gcongr
      exact volume_setOf_mem_Icc_exists_norm_smul_sub_le_le hL hγ ha hsα hLa
    _ = ENNReal.ofReal ((4 / (ε * L) + |d|⁻¹) * (√(r / (2 * c)) / (γ * ‖a‖))) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _), ← hs2, abs_inv, hT]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal ((4 / (ε * L) + 2 * π) * (√(r / (2 * c)) / (γ * ‖a‖))) := by
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (add_le_add le_rfl ?_)
        (by positivity))
      rw [hd, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), inv_div,
        div_le_iff₀ (by positivity)]
      nlinarith [pi_pos]

/-- For `1 ≤ |w|`, `c > 0` and `j + 1 < 2 c α²`, the frequencies `t ∈ (-ε⁻¹, ε⁻¹]` at which
`c * ∑ k, (1 - cos (a k * t * w)) < j + 1` form a set of measure at most
`(4 / (ε L) + 2π) / (γ ‖a‖ √(2c)) * (3 / 2) ^ j`, where `L > 0` is at most the LCD of `a`. -/
private theorem measureReal_setOf_mul_sum_one_sub_cos_lt_inter_Ioc_le {ε c w : ℝ} (hL : 0 < L)
    (hγ : 0 < γ) (ha : a ≠ 0) (hLa : ENNReal.ofReal L ≤ leastCommonDenominator α γ a)
    (hε : 0 < ε) (hc : 0 < c) (hw : 1 ≤ |w|) (hα : 0 < α) {j : ℕ}
    (hj : (j : ℝ) + 1 < 2 * c * α ^ 2) :
    volume.real ({t | c * ∑ k, (1 - cos (a k * t * w)) < j + 1} ∩ Ioc (-ε⁻¹) ε⁻¹) ≤
      (4 / (ε * L) + 2 * π) / (γ * ‖a‖ * √(2 * c)) * (3 / 2) ^ j := by
  -- `√(j + 1) ≤ (3 / 2) ^ j`, since `j + 1 ≤ (9 / 4) ^ j` by Bernoulli's inequality.
  have hsqrt : √(((j : ℝ) + 1) / (2 * c)) ≤ (3 / 2) ^ j / √(2 * c) := by
    rw [sqrt_div' _ (by positivity)]
    refine div_le_div_of_nonneg_right ?_ (sqrt_nonneg _)
    rw [← sqrt_sq (by positivity : (0 : ℝ) ≤ (3 / 2) ^ j), ← pow_mul, mul_comm, pow_mul]
    refine sqrt_le_sqrt ?_
    have := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 5 / 4) j
    norm_num at this ⊢
    linarith
  refine ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((volume_setOf_mul_sum_one_sub_cos_lt_inter_Ioc_le hL hγ ha hLa hε hc hw hα hj).trans
      (ENNReal.ofReal_le_ofReal ?_))
  calc (4 / (ε * L) + 2 * π) * (√(((j : ℝ) + 1) / (2 * c)) / (γ * ‖a‖)) ≤
        (4 / (ε * L) + 2 * π) * ((3 / 2) ^ j / √(2 * c) / (γ * ‖a‖)) := by
        gcongr
    _ = (4 / (ε * L) + 2 * π) / (γ * ‖a‖ * √(2 * c)) * (3 / 2) ^ j := by
        field_simp

/-- For `1 ≤ |w|` and `c > 0`, the integral over `t ∈ (-ε⁻¹, ε⁻¹]` of
`exp (-(c * ∑ k, (1 - cos (a k * t * w))))` is at most
`4 (4 / (ε L) + 2π) / (γ ‖a‖ √(2c)) + (2 / ε) exp (1 - c α²)`, where `L > 0` is at most the LCD of
`a`. -/
private theorem setIntegral_exp_neg_mul_sum_one_sub_cos_le {ε c w : ℝ} (hL : 0 < L)
    (hγ : 0 < γ) (ha : a ≠ 0) (hLa : ENNReal.ofReal L ≤ leastCommonDenominator α γ a)
    (hε : 0 < ε) (hc : 0 < c) (hw : 1 ≤ |w|) (hα : 0 < α) :
    ∫ t in Ioc (-ε⁻¹) ε⁻¹, exp (-(c * ∑ k, (1 - cos (a k * t * w)))) ≤
      4 * (4 / (ε * L) + 2 * π) / (γ * ‖a‖ * √(2 * c)) + 2 / ε * exp (1 - c * α ^ 2) := by
  set f : ℝ → ℝ := fun t ↦ c * ∑ k, (1 - cos (a k * t * w))
  set N := ⌊c * α ^ 2⌋₊
  set K := (4 / (ε * L) + 2 * π) / (γ * ‖a‖ * √(2 * c))
  have hf0 : ∀ t, 0 ≤ f t := fun t ↦
    mul_nonneg hc.le (Finset.sum_nonneg fun k _ ↦ sub_nonneg.2 (cos_le_one _))
  have hfm : Measurable f := by fun_prop
  have hexp : ∀ j : ℕ, exp (-(j : ℝ)) ≤ (1 / 2) ^ j := fun j ↦ by
    rw [← mul_neg_one, exp_natCast_mul]
    refine pow_le_pow_left₀ (exp_pos _).le ?_ j
    rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
    linarith [add_one_le_exp (1 : ℝ)]
  -- The layer-cake bound at the heights `j + 1 ≤ ⌊c α²⌋₊`, each below `2 c α²`.
  have hlc := integral_exp_neg_le_add_sum_measureReal_setOf_lt
    (ν := volume.restrict (Ioc (-ε⁻¹) ε⁻¹)) (ae_of_all _ hf0) N
  rw [measureReal_restrict_apply_univ, volume_real_Ioc_of_le (by linarith [inv_pos.2 hε])] at hlc
  refine hlc.trans ?_
  calc exp (-(N : ℝ)) * (ε⁻¹ - -ε⁻¹) + ∑ j ∈ Finset.range N,
        exp (-(j : ℝ)) * (volume.restrict (Ioc (-ε⁻¹) ε⁻¹)).real {t | f t < j + 1} ≤
        exp (1 - c * α ^ 2) * (2 / ε) + ∑ j ∈ Finset.range N, K * (3 / 4) ^ j := by
        have hεi := inv_pos.2 hε
        refine add_le_add (mul_le_mul (exp_le_exp.2 ?_) (le_of_eq (by ring)) (by linarith)
          (exp_pos _).le) (Finset.sum_le_sum fun j hj ↦ ?_)
        · linarith [Nat.lt_floor_add_one (c * α ^ 2)]
        have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hj
        have hj' : (j : ℝ) + 1 < 2 * c * α ^ 2 := by
          nlinarith [Nat.floor_le (by positivity : 0 ≤ c * α ^ 2), mul_pos hc (pow_pos hα 2)]
        rw [measureReal_restrict_apply (measurableSet_lt hfm measurable_const)]
        calc exp (-(j : ℝ)) * volume.real ({t | f t < j + 1} ∩ Ioc (-ε⁻¹) ε⁻¹) ≤
              (1 / 2) ^ j * (K * (3 / 2) ^ j) :=
              mul_le_mul (hexp j) (measureReal_setOf_mul_sum_one_sub_cos_lt_inter_Ioc_le hL hγ ha
                hLa hε hc hw hα hj') measureReal_nonneg (by positivity)
          _ = K * (3 / 4) ^ j := by rw [mul_comm, mul_assoc, ← mul_pow]; norm_num
    _ ≤ exp (1 - c * α ^ 2) * (2 / ε) + K * 4 := by
        rw [← Finset.mul_sum, Finset.range_eq_Ico]
        gcongr
        exact (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans_eq (by norm_num)
    _ = _ := by ring

/-- Let `ρ` be the law of `x - y` under `μ ⊗ μ`, with `p = ρ {w | 1 ≤ |w|} > 0`. The integral of
`∏ k, ‖charFun μ (a k * t)‖` over `t ∈ [-ε⁻¹, ε⁻¹]` is at most
`4 (4 / (ε L) + 2π) / (γ ‖a‖ √p) + (2 / ε) exp (1 - (p / 2) α²)`, where `L > 0` is at most the LCD
of `a`. -/
private theorem intervalIntegral_prod_norm_charFun_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ε : ℝ} (hL : 0 < L) (hγ : 0 < γ) (ha : a ≠ 0)
    (hLa : ENNReal.ofReal L ≤ leastCommonDenominator α γ a) (hε : 0 < ε) (hα : 0 < α)
    (hp : 0 < ((μ.prod μ).map fun p ↦ p.1 - p.2).real {w | 1 ≤ |w|}) :
    ∫ t in -ε⁻¹..ε⁻¹, ∏ k, ‖charFun μ (a k * t)‖ ≤
      4 * (4 / (ε * L) + 2 * π) /
          (γ * ‖a‖ * √(((μ.prod μ).map fun p ↦ p.1 - p.2).real {w | 1 ≤ |w|})) +
        2 / ε * exp (1 - ((μ.prod μ).map fun p ↦ p.1 - p.2).real {w | 1 ≤ |w|} / 2 * α ^ 2) := by
  set ρ := (μ.prod μ).map fun p : ℝ × ℝ ↦ p.1 - p.2
  set A : Set ℝ := {w | 1 ≤ |w|}
  set p := ρ.real A
  set B := 4 * (4 / (ε * L) + 2 * π) / (γ * ‖a‖ * √p) + 2 / ε * exp (1 - p / 2 * α ^ 2)
  set I := Ioc (-ε⁻¹) ε⁻¹
  have hA : MeasurableSet A := measurableSet_le measurable_const continuous_abs.measurable
  have hρA : ρ A ≠ 0 := fun h ↦ by simp [p, Measure.real, h] at hp
  set g : ℝ → ℝ → ℝ := fun t w ↦ exp (-(p / 2 * ∑ k, (1 - cos (a k * t * w))))
  have hgI : Integrable (Function.uncurry g) ((volume.restrict I).prod (ρ.restrict A)) :=
    (integrable_const (1 : ℝ)).mono
      (by fun_prop : Continuous (Function.uncurry g)).aestronglyMeasurable (ae_of_all _ fun x ↦ by
        rw [norm_one, Function.uncurry_apply_pair, Real.norm_of_nonneg (exp_pos _).le,
          exp_le_one_iff, neg_nonpos]
        exact mul_nonneg (div_nonneg measureReal_nonneg zero_le_two)
          (Finset.sum_nonneg fun k _ ↦ sub_nonneg.2 (cos_le_one _)))
  -- For each `w` with `|w| ≥ 1`, the inner integral is at most `B`.
  have hw : ∀ w ∈ A, ∫ t in I, g t w ≤ B := by
    intro w hw
    have := setIntegral_exp_neg_mul_sum_one_sub_cos_le hL hγ ha hLa hε (half_pos hp) hw hα
    rwa [mul_div_cancel₀ _ two_ne_zero] at this
  rw [intervalIntegral.integral_of_le (by linarith [inv_pos.2 hε])]
  calc ∫ t in I, ∏ k, ‖charFun μ (a k * t)‖ ≤ ∫ t in I, p⁻¹ * ∫ w in A, g t w ∂ρ :=
        setIntegral_mono
          (by fun_prop : Continuous fun t ↦ ∏ k, ‖charFun μ (a k * t)‖).integrableOn_Ioc
          (hgI.integral_prod_left.const_mul _) fun t ↦
            (prod_norm_charFun_le_setAverage_exp Finset.univ (fun k ↦ a k * t) hρA).trans_eq
              (by rw [setAverage_eq, smul_eq_mul])
    _ = p⁻¹ * ∫ t in I, ∫ w in A, g t w ∂ρ := integral_const_mul _ _
    _ = p⁻¹ * ∫ w in A, (∫ t in I, g t w) ∂ρ := by rw [integral_integral_swap hgI]
    _ ≤ p⁻¹ * ∫ _ in A, B ∂ρ :=
        mul_le_mul_of_nonneg_left
          (setIntegral_mono_on hgI.integral_prod_right integrableOn_const hA hw)
          (inv_nonneg.2 hp.le)
    _ = B := by
        rw [setIntegral_const, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

/-- The small-ball bound of
`ProbabilityTheory.iIndepFun.measureReal_abs_sum_mul_sub_le_le_of_ofReal_le_leastCommonDenominator`
for `ε > 0`, `b > 0` and `α > 0`. -/
private theorem measureReal_abs_sum_mul_sub_le_le_of_pos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ : ι → Ω → ℝ} {μ : Measure ℝ} (hξ : iIndepFun ξ P)
    (hμ : ∀ k, HasLaw (ξ k) μ P) {b : ℝ} (hb : ∀ v, μ.real (closedBall v 1) ≤ 1 - b)
    (hb0 : 0 < b) (ha : a ≠ 0) (hγ : 0 < γ) (hL : 0 < L)
    (hLa : ENNReal.ofReal L ≤ leastCommonDenominator α γ a) (hα : 0 < α) (v : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    P.real {ω | |∑ k, a k * ξ k ω - v| ≤ ε} ≤
      16 * π * (ε + L⁻¹) / (γ * ‖a‖ * √b) + 4 * exp (1 - α ^ 2 * b / 2) := by
  have := hξ.isProbabilityMeasure
  obtain ⟨k₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact ha (by ext k; exact isEmptyElim k)
  have : IsProbabilityMeasure μ := (hμ k₀).isProbabilityMeasure_iff.1 ‹_›
  set ρ := (μ.prod μ).map fun p : ℝ × ℝ ↦ p.1 - p.2
  have hA : MeasurableSet {w : ℝ | 1 ≤ |w|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  -- The symmetrized law gives `|w| < 1` mass at most `1 - b`, slice by slice.
  have hAc : ρ.real {w : ℝ | 1 ≤ |w|}ᶜ ≤ 1 - b := by
    have hb1 : 0 ≤ 1 - b := measureReal_nonneg.trans (hb 0)
    refine ENNReal.toReal_le_of_le_ofReal hb1 ?_
    rw [Measure.map_apply measurable_sub hA.compl, Measure.prod_apply (measurable_sub hA.compl)]
    refine (lintegral_mono fun x ↦ ?_).trans_eq (by rw [lintegral_const, measure_univ, mul_one])
    refine (measure_mono fun y hy ↦ ?_).trans
      ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hb1).2 (hb x))
    simp only [mem_preimage, mem_compl_iff, mem_ofPred_eq, not_le] at hy
    rw [mem_closedBall, Real.dist_eq, abs_sub_comm]
    exact hy.le
  have hpb : b ≤ ρ.real {w : ℝ | 1 ≤ |w|} := by
    rw [probReal_compl_eq_one_sub hA] at hAc
    linarith
  have hmap : ∀ k, P.map (ξ k) = μ := fun k ↦ (hμ k).map_eq
  have hE := hξ.measureReal_abs_sum_mul_sub_le_le_integral_prod_norm_charFun
    (fun k ↦ (hμ k).aemeasurable) (fun k ↦ a k) v hε
  simp only [hmap] at hE
  have hI := intervalIntegral_prod_norm_charFun_le (μ := μ) hL hγ ha hLa hε hα
    (hb0.trans_le hpb)
  set p := ρ.real {w : ℝ | 1 ≤ |w|}
  have hp : 0 < p := hb0.trans_le hpb
  calc P.real {ω | |∑ k, a k * ξ k ω - v| ≤ ε} ≤
        2 * ε * ∫ t in -ε⁻¹..ε⁻¹, ∏ k, ‖charFun μ (a k * t)‖ := hE
    _ ≤ 2 * ε * (4 * (4 / (ε * L) + 2 * π) / (γ * ‖a‖ * √p) + 2 / ε * exp (1 - p / 2 * α ^ 2)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = 8 * (4 * L⁻¹ + 2 * π * ε) / (γ * ‖a‖ * √p) + 4 * exp (1 - p / 2 * α ^ 2) := by
        field_simp
        ring
    _ ≤ 16 * π * (ε + L⁻¹) / (γ * ‖a‖ * √b) + 4 * exp (1 - α ^ 2 * b / 2) := by
        have hπ := two_le_pi
        have hLi : 0 < L⁻¹ := inv_pos.2 hL
        refine add_le_add (div_le_div₀ (by positivity) (by nlinarith) (by positivity)
          (by gcongr)) (mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by norm_num))
        nlinarith [sq_nonneg α]

end TauCeti

namespace ProbabilityTheory

open TauCeti

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}

/-- **Small-ball probabilities through the least common denominator** (Rudelson–Vershynin).
Let `ξ k` be independent real random variables with a common law `μ` whose closed balls of radius
`1` have mass at most `1 - b`. If `L > 0` is at most the least common denominator
`LCD_{α,γ}(a)` of a nonzero vector `a` with `γ > 0`, then for every `ε ≥ 0` and every `v`,
`P (|∑ k, a k * ξ k - v| ≤ ε) ≤ 16 π (ε + L⁻¹) / (γ ‖a‖ √b) + 4 exp (1 - α² b / 2)`. -/
theorem iIndepFun.measureReal_abs_sum_mul_sub_le_le_of_ofReal_le_leastCommonDenominator
    {ξ : ι → Ω → ℝ} {μ : Measure ℝ} (hξ : iIndepFun ξ P) (hμ : ∀ k, HasLaw (ξ k) μ P) {b : ℝ}
    (hb : ∀ v, μ.real (closedBall v 1) ≤ 1 - b) {a : EuclideanSpace ℝ ι} (ha : a ≠ 0)
    {α : ℝ≥0} {γ L : ℝ} (hγ : 0 < γ) (hL : 0 < L)
    (hLa : ENNReal.ofReal L ≤ leastCommonDenominator α γ a) (v : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | |∑ k, a k * ξ k ω - v| ≤ ε} ≤
      16 * π * (ε + L⁻¹) / (γ * ‖a‖ * √b) + 4 * exp (1 - α ^ 2 * b / 2) := by
  have := hξ.isProbabilityMeasure
  have hP1 : P.real {ω | |∑ k, a k * ξ k ω - v| ≤ ε} ≤ 1 := measureReal_le_one
  have hfirst : 0 ≤ 16 * π * (ε + L⁻¹) / (γ * ‖a‖ * √b) := by positivity
  -- If `b ≤ 0` or `α = 0`, the exponential term alone is at least `4`.
  rcases le_or_gt b 0 with hb0 | hb0
  · have : 1 ≤ exp (1 - α ^ 2 * b / 2) :=
      one_le_exp (by nlinarith [sq_nonneg (α : ℝ)])
    linarith
  rcases eq_or_ne α 0 with rfl | hα
  · norm_num
    linarith [one_le_exp zero_le_one]
  have hα' : (0 : ℝ) < α := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hα)
  rcases hε.eq_or_lt with rfl | hε
  -- The case `ε = 0` follows from the bounds at every `δ > 0`.
  · refine le_of_forall_pos_le_add fun η hη ↦ ?_
    have hδ : 0 < η * (γ * ‖a‖ * √b) / (16 * π) := by positivity
    calc P.real {ω | |∑ k, a k * ξ k ω - v| ≤ 0} ≤
          P.real {ω | |∑ k, a k * ξ k ω - v| ≤ η * (γ * ‖a‖ * √b) / (16 * π)} :=
          measureReal_mono fun ω hω ↦ (mem_ofPred.1 hω).trans hδ.le
      _ ≤ 16 * π * (η * (γ * ‖a‖ * √b) / (16 * π) + L⁻¹) / (γ * ‖a‖ * √b) +
            4 * exp (1 - α ^ 2 * b / 2) :=
          measureReal_abs_sum_mul_sub_le_le_of_pos hξ hμ hb hb0 ha hγ hL hLa hα' v hδ
      _ = 16 * π * (0 + L⁻¹) / (γ * ‖a‖ * √b) + 4 * exp (1 - α ^ 2 * b / 2) + η := by
          field_simp
          ring
  · exact measureReal_abs_sum_mul_sub_le_le_of_pos hξ hμ hb hb0 ha hγ hL hLa hα' v hε

end ProbabilityTheory
