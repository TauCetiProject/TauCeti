/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.InverseMoment
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.GiryMonad
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# The Marchenko–Pastur law

For an aspect ratio `y ≥ 0`, the Marchenko–Pastur law `MP_y` is the limiting empirical spectral
law of sample covariance matrices `X Xᴴ / n` of size `p × p` with `p / n → y`. For `y > 0`, with
edges `a = (1 - √y)²` and `b = (1 + √y)²`, it has an atom of mass `(1 - 1/y)₊` at `0` and the
density `√((b - x)(x - a)) / (2π y x)` on `(a, b)`; at `y = 0` it is the point mass `δ₁`.

Since `(b - x)(x - a) = 4y - (x - (1 + y))²`, this density is `x⁻¹` times the density of the
semicircle law with centre `1 + y` and variance `y`. We therefore define `marchenkoPastur y` as
the atom plus `x⁻¹` times `semicircleReal (1 + y) y`, which also covers `y = 0` uniformly, and
prove the explicit density formula as `marchenkoPastur_eq_withDensity`. Equivalently, the
size-biased law `x · MP_y` is exactly `semicircleReal (1 + y) y`
(`withDensity_ofReal_marchenkoPastur`), which transfers integrals of `x • g x` against `MP_y` to
integrals of `g` against the semicircle law. In particular
`∫ x^(k+1) dMP_y = ∫ x^k d(semicircleReal (1 + y) y)`, so `MP_y` has mean `1`, second moment
`1 + y` and variance `y`.

## Main declarations

* `TauCeti.Probability.marchenkoPastur`: the Marchenko–Pastur law of ratio `y`.
* `TauCeti.Probability.marchenkoPastur_eq_withDensity`: its atom and density for `y > 0`.
* `TauCeti.Probability.isProbabilityMeasure_marchenkoPastur`: it is a probability measure.
* `TauCeti.Probability.measurable_marchenkoPastur`: parameter measurability of `y ↦ MP_y`.
* `TauCeti.Probability.marchenkoPastur_singleton_zero`,
  `TauCeti.Probability.marchenkoPastur_compl_singleton_zero`: the atom mass `(1 - 1/y)₊` at `0`
  and the complementary continuous mass `min 1 (1/y)` for `y > 0`.
* `TauCeti.Probability.support_marchenkoPastur`,
  `TauCeti.Probability.zero_mem_support_marchenkoPastur_iff`: its exact topological support is
  `[(1 - √y)², (1 + √y)²]` for `y ≤ 1` and `{0} ∪ [(1 - √y)², (1 + √y)²]` for `1 ≤ y`, and `0`
  belongs to the support iff `1 ≤ y`.
* `TauCeti.Probability.withDensity_ofReal_marchenkoPastur`: its size-biased law is a semicircle.
* `TauCeti.Probability.memLp_id_marchenkoPastur`,
  `TauCeti.Probability.integrable_pow_marchenkoPastur`: it has moments of all orders.
* `TauCeti.Probability.integral_pow_succ_marchenkoPastur`: its moments as semicircle moments.

## References

* V. A. Marchenko, L. A. Pastur, *Distribution of eigenvalues for some sets of random matrices*,
  Mat. Sb. 72 (1967), 507–536.
* Z. D. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer, 2010, §3.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- The Marchenko–Pastur law of aspect ratio `y`: an atom at `0` plus `x⁻¹` times the semicircle
law with centre `1 + y` and variance `y`. The atom weight is written `(y - 1) / y`; for `y > 0` its
positive part is the atom mass `(1 - 1/y)₊`, which vanishes for `y ≤ 1`. At `y = 0` the weight is
`0` under Lean's convention `1 / 0 = 0`, so there is no atom and the law is `δ₁`. -/
def marchenkoPastur (y : ℝ≥0) : Measure ℝ :=
  ENNReal.ofReal ((y - 1) / y) • Measure.dirac 0 +
    (semicircleReal (1 + y) y).withDensity fun x ↦ ENNReal.ofReal x⁻¹

/-- The Marchenko–Pastur law is its atom at `0` plus a reweighted semicircle law. -/
theorem marchenkoPastur_def (y : ℝ≥0) :
    marchenkoPastur y = ENNReal.ofReal ((y - 1) / y) • Measure.dirac 0 +
      (semicircleReal (1 + y) y).withDensity fun x ↦ ENNReal.ofReal x⁻¹ :=
  (rfl)

/-- The Marchenko–Pastur law of ratio `0` is the point mass at `1`. -/
@[simp]
theorem marchenkoPastur_zero : marchenkoPastur 0 = Measure.dirac 1 := by
  simp [marchenkoPastur_def, dirac_withDensity]

/-- For `y > 0`, the Marchenko–Pastur law has an atom of mass `(1 - 1/y)₊` at `0` and the density
`√((b - x)(x - a)) / (2π y x)` with `a = (1 - √y)²`, `b = (1 + √y)²`. The real square root makes
the density zero outside `(a, b)`. -/
theorem marchenkoPastur_eq_withDensity {y : ℝ≥0} (hy : 0 < y) :
    marchenkoPastur y = ENNReal.ofReal ((y - 1) / y) • Measure.dirac 0 +
      volume.withDensity fun x ↦ ENNReal.ofReal
        (√(((1 + √y) ^ 2 - x) * (x - (1 - √y) ^ 2)) / (2 * π * y * x)) := by
  rw [marchenkoPastur_def, semicircleReal_eq_withDensity _ hy,
    ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 2
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hs := sq_sqrt y.coe_nonneg
  have hq : 4 * (y : ℝ) - (x - (1 + y)) ^ 2 = ((1 + √y) ^ 2 - x) * (x - (1 - √y) ^ 2) := by
    linear_combination (y + √(y : ℝ) ^ 2 - 2 - 2 * x) * hs
  rw [hq]
  ring

/-- Every Marchenko–Pastur law is a probability measure: for `y > 0` the continuous part has
mass `min 1 (1/y)`, complementing the atom `(1 - 1/y)₊`. -/
instance isProbabilityMeasure_marchenkoPastur (y : ℝ≥0) :
    IsProbabilityMeasure (marchenkoPastur y) := by
  rcases eq_zero_or_pos y with rfl | hy
  · rw [marchenkoPastur_zero]
    infer_instance
  have hy' : (0 : ℝ) < y := hy
  have h2 : 2 * √(y : ℝ) ≤ 1 + y := by
    nlinarith [sq_nonneg (1 - √(y : ℝ)), sq_sqrt y.coe_nonneg]
  have hd : (1 + (y : ℝ)) ^ 2 - 4 * y = (1 - y) ^ 2 := by ring
  have hsq : √((1 + (y : ℝ)) ^ 2 - 4 * y) = |1 - (y : ℝ)| := by
    rw [hd, sqrt_sq_eq_abs]
  constructor
  simp only [marchenkoPastur_def, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, measure_univ, smul_eq_mul, mul_one, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_inv_semicircleReal h2)
      ((ae_pos_semicircleReal h2 (by positivity)).mono fun x hx ↦ (inv_pos.2 hx).le),
    integral_inv_semicircleReal hy h2, hsq]
  rcases le_or_gt (y : ℝ) 1 with h1 | h1
  · rw [abs_of_nonneg (sub_nonneg.2 h1),
      ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h1) hy'.le),
      zero_add, ← ENNReal.ofReal_one]
    congr 1
    field_simp
    ring
  · rw [abs_of_neg (by linarith), ← ENNReal.ofReal_add (div_nonneg (by linarith) hy'.le)
      (div_nonneg (by linarith) (by positivity)), ← ENNReal.ofReal_one]
    congr 1
    field_simp
    ring

/-- The Marchenko–Pastur law depends measurably on its aspect ratio. -/
@[fun_prop]
theorem measurable_marchenkoPastur : Measurable marchenkoPastur := by
  refine Measure.measurable_measure.2 fun s hs ↦ ?_
  have hf : Measurable (s.indicator fun x : ℝ ↦ ENNReal.ofReal x⁻¹) :=
    (by fun_prop : Measurable fun x : ℝ ↦ ENNReal.ofReal x⁻¹).indicator hs
  have hsemi : Measurable fun y : ℝ≥0 ↦ semicircleReal (1 + y) y :=
    measurable_semicircleReal.comp (by fun_prop : Measurable fun y : ℝ≥0 ↦ (1 + (y : ℝ), y))
  simp only [marchenkoPastur_def, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, withDensity_apply _ hs, ← lintegral_indicator hs]
  exact ((by fun_prop : Measurable fun y : ℝ≥0 ↦ ENNReal.ofReal (((y : ℝ) - 1) / y)).mul_const
    (Measure.dirac 0 s)).add ((Measure.measurable_lintegral hf).comp hsemi)

/-- The atom of the Marchenko–Pastur law at `0`: its mass is `ENNReal.ofReal ((y - 1) / y)`, which
is `(1 - 1/y)₊` for `y > 0` and `0` for `y = 0`. -/
@[simp]
theorem marchenkoPastur_singleton_zero (y : ℝ≥0) :
    marchenkoPastur y {0} = ENNReal.ofReal ((y - 1) / y) := by
  simp [marchenkoPastur_def]

/-- For `y > 0`, the mass of the Marchenko–Pastur law outside `0` is `min 1 (1 / y)`. At `y = 0`
the law is `δ₁`, so the mass outside `0` is `1` whereas `(0 : ℝ)⁻¹ = 0`. -/
theorem marchenkoPastur_compl_singleton_zero {y : ℝ≥0} (hy : 0 < y) :
    marchenkoPastur y {0}ᶜ = ENNReal.ofReal (min 1 (y : ℝ)⁻¹) := by
  have hy' : (0 : ℝ) < y := hy
  rw [prob_compl_eq_one_sub (measurableSet_singleton 0), marchenkoPastur_singleton_zero,
    ← ENNReal.ofReal_one]
  rcases le_or_gt (y : ℝ) 1 with h1 | h1
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h1) hy'.le),
      tsub_zero, min_eq_left (one_le_inv₀ hy' |>.2 h1)]
  · rw [min_eq_right ((inv_le_one₀ hy').2 h1.le),
      ← ENNReal.ofReal_sub _ (div_nonneg (by linarith) hy'.le)]
    congr 1
    field_simp
    ring

/-- The Marchenko–Pastur law is carried by `{0} ∪ [(1 - √y)², (1 + √y)²]`. -/
theorem ae_eq_zero_or_mem_Icc_marchenkoPastur (y : ℝ≥0) :
    ∀ᵐ x ∂marchenkoPastur y, x = 0 ∨ x ∈ Icc ((1 - √y) ^ 2) ((1 + √y) ^ 2) := by
  rw [marchenkoPastur_def, ae_add_measure_iff]
  refine ⟨Measure.ae_smul_measure (by simp [ae_dirac_eq]) _,
    (withDensity_absolutelyContinuous _ _).ae_le ?_⟩
  filter_upwards [ae_mem_Icc_semicircleReal (1 + y) y] with x hx
  have hs := sq_sqrt y.coe_nonneg
  exact Or.inr ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩

/-- A Marchenko–Pastur variable is almost surely nonnegative. -/
theorem ae_nonneg_marchenkoPastur (y : ℝ≥0) : ∀ᵐ x ∂marchenkoPastur y, 0 ≤ x := by
  filter_upwards [ae_eq_zero_or_mem_Icc_marchenkoPastur y] with x hx
  rcases hx with rfl | hx
  · exact le_rfl
  · exact (sq_nonneg _).trans hx.1

/-- The Marchenko–Pastur law is carried by `[0, (1 + √y)²]`. -/
theorem ae_mem_Icc_zero_marchenkoPastur (y : ℝ≥0) :
    ∀ᵐ x ∂marchenkoPastur y, x ∈ Icc 0 ((1 + √y) ^ 2) := by
  filter_upwards [ae_eq_zero_or_mem_Icc_marchenkoPastur y] with x hx
  rcases hx with rfl | hx
  · exact ⟨le_rfl, sq_nonneg _⟩
  · exact ⟨(sq_nonneg _).trans hx.1, hx.2⟩

/-- The support of the continuous part `x⁻¹ · semicircleReal (1 + y) y` is
`[(1 - √y)², (1 + √y)²]`. -/
private theorem support_withDensity_inv_semicircleReal (y : ℝ≥0) :
    ((semicircleReal (1 + y) y).withDensity fun x ↦ ENNReal.ofReal x⁻¹).support =
      Icc ((1 - √y) ^ 2) ((1 + √y) ^ 2) := by
  have h2 : 2 * √(y : ℝ) ≤ 1 + y := by
    nlinarith [sq_nonneg (1 - √(y : ℝ)), sq_sqrt y.coe_nonneg]
  have hne : ∀ᵐ x ∂semicircleReal (1 + y) y, ENNReal.ofReal x⁻¹ ≠ 0 := by
    filter_upwards [ae_pos_semicircleReal h2 (by positivity)] with x hx
    exact (ENNReal.ofReal_pos.2 (inv_pos.2 hx)).ne'
  have hs := sq_sqrt y.coe_nonneg
  rw [Measure.support_withDensity_eq (by fun_prop) hne, support_semicircleReal]
  congr 1 <;> linear_combination -hs

/-- For `y ≤ 1`, the topological support of `marchenkoPastur y` is `[(1 - √y)², (1 + √y)²]`; at
`y = 0` this is `{1}` and at `y = 1` it is `[0, 4]`. -/
theorem support_marchenkoPastur_of_le_one {y : ℝ≥0} (hy : y ≤ 1) :
    (marchenkoPastur y).support = Icc ((1 - √y) ^ 2) ((1 + √y) ^ 2) := by
  have h0 : ENNReal.ofReal (((y : ℝ) - 1) / y) = 0 :=
    ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (mod_cast hy))
      y.coe_nonneg)
  rw [marchenkoPastur_def, h0, zero_smul, zero_add, support_withDensity_inv_semicircleReal]

/-- For `1 ≤ y`, the topological support of `marchenkoPastur y` is
`{0} ∪ [(1 - √y)², (1 + √y)²]`; for `1 < y` the atom `{0}` is strictly separated from the bulk
interval, while at `y = 1` it coincides with the lower edge `0`. -/
theorem support_marchenkoPastur_of_one_le {y : ℝ≥0} (hy : 1 ≤ y) :
    (marchenkoPastur y).support = insert 0 (Icc ((1 - √y) ^ 2) ((1 + √y) ^ 2)) := by
  rcases eq_or_lt_of_le hy with rfl | hy'
  · rw [support_marchenkoPastur_of_le_one le_rfl]
    norm_num
  · have hyr : (1 : ℝ) < y := mod_cast hy'
    have hc : ENNReal.ofReal (((y : ℝ) - 1) / y) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (div_pos (by linarith) (by linarith))).ne'
    rw [marchenkoPastur_def, Measure.support_add, Measure.support_smul hc, Measure.support_dirac,
      isClosed_singleton.closure_eq, support_withDensity_inv_semicircleReal, singleton_union]

/-- The exact topological support of the Marchenko–Pastur law `MP_y`: the interval
`[(1 - √y)², (1 + √y)²]`, together with `{0}` when `1 < y`. -/
theorem support_marchenkoPastur (y : ℝ≥0) :
    (marchenkoPastur y).support =
      if y ≤ 1 then Icc ((1 - √y) ^ 2) ((1 + √y) ^ 2)
      else insert 0 (Icc ((1 - √y) ^ 2) ((1 + √y) ^ 2)) := by
  split_ifs with hy
  · exact support_marchenkoPastur_of_le_one hy
  · exact support_marchenkoPastur_of_one_le (le_of_not_ge hy)

/-- The topological support of `MP_1` is `[0, 4]`. -/
@[simp]
theorem support_marchenkoPastur_one : (marchenkoPastur 1).support = Icc 0 4 := by
  rw [support_marchenkoPastur_of_le_one le_rfl]
  norm_num

/-- Zero belongs to the topological support of `marchenkoPastur y` if and only if `1 ≤ y`. -/
@[simp]
theorem zero_mem_support_marchenkoPastur_iff {y : ℝ≥0} :
    (0 : ℝ) ∈ (marchenkoPastur y).support ↔ 1 ≤ y := by
  rcases le_or_gt 1 y with hy | hy
  · simp [support_marchenkoPastur_of_one_le hy, hy]
  · rw [support_marchenkoPastur_of_le_one hy.le, mem_Icc, iff_false_right (not_le.2 hy)]
    intro h0
    have hsqrt : √(y : ℝ) < 1 := (sqrt_lt' zero_lt_one).2 (by norm_num; exact_mod_cast hy)
    have hpos : 0 < (1 - √(y : ℝ)) ^ 2 := sq_pos_of_pos (sub_pos.2 hsqrt)
    linarith [h0.1]

/-- The topological support of `MP_y` is contained in `[0, (1 + √y)²]`. -/
theorem support_marchenkoPastur_subset_Icc (y : ℝ≥0) :
    (marchenkoPastur y).support ⊆ Icc 0 ((1 + √y) ^ 2) :=
  Measure.support_subset_of_isClosed isClosed_Icc (ae_mem_Icc_zero_marchenkoPastur y)

/-- The topological support of `MP_y` is compact. -/
theorem isCompact_support_marchenkoPastur (y : ℝ≥0) :
    IsCompact (marchenkoPastur y).support :=
  isCompact_Icc.of_isClosed_subset Measure.isClosed_support (support_marchenkoPastur_subset_Icc y)

/-- The identity is in every `Lᵖ` space of the Marchenko–Pastur law, which has bounded support. -/
theorem memLp_id_marchenkoPastur (y : ℝ≥0) (p : ℝ≥0∞) : MemLp id p (marchenkoPastur y) :=
  memLp_of_bounded (ae_mem_Icc_zero_marchenkoPastur y) measurable_id.aestronglyMeasurable p

/-- A Marchenko–Pastur variable is integrable. -/
theorem integrable_id_marchenkoPastur (y : ℝ≥0) : Integrable id (marchenkoPastur y) :=
  memLp_one_iff_integrable.1 (memLp_id_marchenkoPastur y 1)

/-- Every natural power is integrable against the Marchenko–Pastur law. -/
theorem integrable_pow_marchenkoPastur (y : ℝ≥0) (k : ℕ) :
    Integrable (fun x ↦ x ^ k) (marchenkoPastur y) := by
  refine memLp_one_iff_integrable.1 <| memLp_of_bounded (a := 0) (b := ((1 + √y) ^ 2) ^ k) ?_
    (by fun_prop) 1
  filter_upwards [ae_mem_Icc_zero_marchenkoPastur y] with x hx
  exact ⟨pow_nonneg hx.1 k, pow_le_pow_left₀ hx.1 hx.2 k⟩

/-- The size-biased Marchenko–Pastur law `x · MP_y` is the semicircle law with centre `1 + y`
and variance `y`. -/
theorem withDensity_ofReal_marchenkoPastur (y : ℝ≥0) :
    (marchenkoPastur y).withDensity (fun x ↦ ENNReal.ofReal x) = semicircleReal (1 + y) y := by
  simp only [marchenkoPastur_def, withDensity_add_measure, withDensity_smul_measure,
    dirac_withDensity, ENNReal.ofReal_zero, zero_smul, smul_zero, zero_add]
  rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
  conv_rhs => rw [← withDensity_one (μ := semicircleReal (1 + y) y)]
  refine withDensity_congr_ae ?_
  have h2 : 2 * √(y : ℝ) ≤ 1 + y := by
    nlinarith [sq_nonneg (1 - √(y : ℝ)), sq_sqrt y.coe_nonneg]
  filter_upwards [ae_pos_semicircleReal h2 (by positivity)] with x hx
  simp [← ENNReal.ofReal_mul (inv_nonneg.2 hx.le), inv_mul_cancel₀ hx.ne']

/-- Integrating `x • g x` against the Marchenko–Pastur law is integrating `g` against the
semicircle law with centre `1 + y` and variance `y`. -/
theorem integral_smul_marchenkoPastur {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : ℝ≥0) (g : ℝ → E) :
    ∫ x, x • g x ∂marchenkoPastur y = ∫ x, g x ∂semicircleReal (1 + y) y := by
  rw [← withDensity_ofReal_marchenkoPastur, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_nonneg_marchenkoPastur y] with x hx
  rw [ENNReal.toReal_ofReal hx]

/-- The moment of order `k + 1` of the Marchenko–Pastur law is the moment of order `k` of the
semicircle law with centre `1 + y` and variance `y`. -/
theorem integral_pow_succ_marchenkoPastur (y : ℝ≥0) (k : ℕ) :
    ∫ x, x ^ (k + 1) ∂marchenkoPastur y = ∫ x, x ^ k ∂semicircleReal (1 + y) y := by
  simpa [smul_eq_mul, ← pow_succ'] using integral_smul_marchenkoPastur y fun x ↦ x ^ k

/-- The Marchenko–Pastur law has mean `1`. -/
@[simp]
theorem integral_id_marchenkoPastur (y : ℝ≥0) : ∫ x, x ∂marchenkoPastur y = 1 := by
  simpa using integral_pow_succ_marchenkoPastur y 0

/-- The second moment of the Marchenko–Pastur law is `1 + y`. -/
@[simp]
theorem integral_sq_marchenkoPastur (y : ℝ≥0) : ∫ x, x ^ 2 ∂marchenkoPastur y = 1 + y := by
  simp only [integral_pow_succ_marchenkoPastur y 1, pow_one, integral_id_semicircleReal]

/-- The Marchenko–Pastur law has variance `y`. -/
@[simp]
theorem variance_id_marchenkoPastur (y : ℝ≥0) : variance id (marchenkoPastur y) = y := by
  rw [variance_eq_sub (memLp_id_marchenkoPastur y 2)]
  simp

end TauCeti.Probability
