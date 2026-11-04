/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.DiscreteLaplace.Basic
public import TauCeti.Probability.Distributions.Geometric.Basic
import TauCeti.Probability.Distributions.Sums
import TauCeti.Probability.Distributions.NegativeBinomial.Transforms

/-!
# Moments and transforms of the discrete Laplace law

The real cast of a discrete Laplace count is a translated difference of independent geometric
counts. This gives its mean, variance, and characteristic function. For `0 < q < 1`, its exact
exponential-integrability domain is `|t| < -log q`; at `q = 0` it is all of `ℝ`.
All natural moments are absolutely integrable, including the point-mass boundary.

The proofs reuse the geometric-difference identity in `Distributions.Sums` and the geometric
moment and transform formulas.

## References

* S. Inusah and T. J. Kozubowski, *A discrete analogue of the Laplace distribution*, Journal of
  Statistical Planning and Inference 136 (2006), 1090–1102.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

private theorem map_intCast_discreteLaplaceMeasure (m : ℤ) {p : unitInterval} (hp : p ≠ 0) :
    (discreteLaplaceMeasure m (1 - p)).map (Int.cast : ℤ → ℝ) =
      (((geometricMeasure p).map (Nat.cast : ℕ → ℝ)).prod
        ((geometricMeasure p).map (Nat.cast : ℕ → ℝ))).map
          (fun z : ℝ × ℝ => z.1 - z.2 + m) := by
  have hmap := congrArg (fun μ : Measure ℤ => μ.map (fun k : ℤ => (k + m : ℤ)))
    (map_sub_prod_geometricMeasure hp)
  rw [map_add_const_discreteLaplaceMeasure, zero_add] at hmap
  rw [← hmap, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp

private theorem mgf_intCast_discreteLaplaceMeasure_eq_product (m : ℤ) {p : unitInterval}
    (hp : p ≠ 0) (t : ℝ) :
    mgf (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m (1 - p)) t =
      exp (t * m) * mgf id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) t *
        mgf id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) (-t) := by
  rw [← mgf_id_map (by fun_prop), map_intCast_discreteLaplaceMeasure m hp,
    mgf_id_map (by fun_prop), mgf_add_const]
  simp only [mgf, id_eq]
  have hfun : (fun z : ℝ × ℝ => exp (t * (z.1 - z.2))) =
      fun z => exp (t * z.1) * exp ((-t) * z.2) := by
    funext z
    rw [← exp_add]
    congr 1
    ring
  rw [hfun, integral_prod_mul (fun x : ℝ => exp (t * x))
    (fun y : ℝ => exp ((-t) * y))]
  ring

/-- For valid parameters, exponential integrability is exactly the intersection of the two
geometric domains. This form includes the full domain at `q = 0`. -/
theorem integrable_exp_mul_intCast_discreteLaplaceMeasure_iff (m : ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    Integrable (fun k : ℤ => exp (t * k)) (discreteLaplaceMeasure m q) ↔
      q * exp t < 1 ∧ q * exp (-t) < 1 := by
  have := isProbabilityMeasure_discreteLaplaceMeasure m hq0 hq1
  let p : unitInterval := ⟨1 - q, by constructor <;> linarith⟩
  have hp : p ≠ 0 := ne_of_gt (unitInterval.coe_pos.mp (by dsimp [p]; linarith))
  have hq : 1 - (p : ℝ) = q := by simp [p]
  have hprod := mgf_intCast_discreteLaplaceMeasure_eq_product m hp t
  rw [hq] at hprod
  rw [← mgf_pos_iff, hprod, mul_assoc, mul_pos_iff_of_pos_left (exp_pos _), mul_pos_iff]
  simp only [not_lt_of_ge (mgf_nonneg (X := id)), and_false, or_false]
  rw [mgf_pos_iff, mgf_pos_iff]
  simp only [id_eq]
  rw [integrable_exp_mul_id_map_cast_geometricMeasure_iff hp,
    integrable_exp_mul_id_map_cast_geometricMeasure_iff hp, hq]

/-- The exact exponential-integrability domain for a positive discrete Laplace parameter. Both
endpoints are excluded. -/
theorem integrableExpSet_intCast_discreteLaplaceMeasure (m : ℤ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    integrableExpSet (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) =
      {t | |t| < -log q} := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq]
  rw [integrable_exp_mul_intCast_discreteLaplaceMeasure_iff m hq0.le hq1]
  have h (s : ℝ) : q * exp s < 1 ↔ s < -log q := by
    calc
      q * exp s < 1 ↔ exp (log q + s) < exp 0 := by
        rw [exp_add, exp_log hq0, exp_zero]
      _ ↔ s < -log q := by rw [exp_lt_exp]; constructor <;> intro h <;> linarith
  rw [h, h, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The moment-generating function of the signed count, on its exact domain, including `q = 0`. -/
theorem mgf_intCast_discreteLaplaceMeasure (m : ℤ) {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ht : q * exp t < 1 ∧ q * exp (-t) < 1) :
    mgf (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) t =
      exp (t * m) * (1 - q) ^ 2 / ((1 - q * exp t) * (1 - q * exp (-t))) := by
  let p : unitInterval := ⟨1 - q, by constructor <;> linarith⟩
  have hp : p ≠ 0 := ne_of_gt (unitInterval.coe_pos.mp (by dsimp [p]; linarith))
  have hq : 1 - (p : ℝ) = q := by simp [p]
  have hprod := mgf_intCast_discreteLaplaceMeasure_eq_product m hp t
  rw [hq] at hprod
  rw [hprod, mgf_id_map_cast_geometricMeasure hp (by simpa [hq] using ht.1),
    mgf_id_map_cast_geometricMeasure hp (by simpa [hq] using ht.2)]
  simp only [hq, p, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The cumulant-generating function on the exact domain, with the translation separated from
the two geometric contributions. -/
theorem cgf_intCast_discreteLaplaceMeasure (m : ℤ) {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ht : q * exp t < 1 ∧ q * exp (-t) < 1) :
    cgf (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) t =
      t * m + 2 * log (1 - q) - log (1 - q * exp t) - log (1 - q * exp (-t)) := by
  rw [cgf, mgf_intCast_discreteLaplaceMeasure m hq0 hq1 ht,
    log_div (mul_ne_zero (exp_ne_zero _) (pow_ne_zero _ (by linarith)))
      (mul_ne_zero (by linarith) (by linarith)),
    log_mul (exp_ne_zero _) (pow_ne_zero _ (by linarith)), log_exp,
    log_pow, log_mul (by linarith) (by linarith)]
  ring

/-- Every natural moment of the signed count is absolutely integrable. This includes the
point-mass boundary and the zero measure at invalid parameters. -/
theorem integrable_pow_intCast_discreteLaplaceMeasure (m : ℤ) (q : ℝ) (n : ℕ) :
    Integrable (fun k : ℤ => (k : ℝ) ^ n) (discreteLaplaceMeasure m q) := by
  by_cases hq : 0 ≤ q ∧ q < 1
  · have hdom : integrableExpSet (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) =
        {t | q * exp t < 1 ∧ q * exp (-t) < 1} := by
      ext t
      exact integrable_exp_mul_intCast_discreteLaplaceMeasure_iff m hq.1 hq.2 t
    have hzero : 0 ∈ interior
        (integrableExpSet (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q)) := by
      have hopen : IsOpen {t : ℝ | q * exp t < 1 ∧ q * exp (-t) < 1} :=
        (isOpen_lt (by fun_prop : Continuous fun t : ℝ => q * exp t) continuous_const).inter
          (isOpen_lt (by fun_prop : Continuous fun t : ℝ => q * exp (-t)) continuous_const)
      rw [hdom, hopen.interior_eq]
      simpa using And.intro hq.2 hq.2
    exact integrable_pow_of_mem_interior_integrableExpSet hzero n
  · simp [discreteLaplaceMeasure_eq_zero_of_invalid m hq]

/-- The mean of a discrete Laplace count is its integer center. -/
@[simp]
theorem integral_intCast_discreteLaplaceMeasure (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∫ k : ℤ, (k : ℝ) ∂discreteLaplaceMeasure m q = m := by
  have := isProbabilityMeasure_discreteLaplaceMeasure 0 hq0 hq1
  have hzero : ∫ k : ℤ, (k : ℝ) ∂discreteLaplaceMeasure 0 q = 0 := by
    have h := congrArg (fun μ : Measure ℤ => ∫ k : ℤ, (k : ℝ) ∂μ)
      (map_neg_discreteLaplaceMeasure 0 q)
    rw [integral_map (by fun_prop) (by fun_prop)] at h
    simp only [Int.cast_neg, integral_neg, neg_zero] at h
    linarith
  rw [← zero_add m, ← map_add_const_discreteLaplaceMeasure,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [Int.cast_add]
  rw [integral_add (by simpa using integrable_pow_intCast_discreteLaplaceMeasure 0 q 1)
    (integrable_const _)]
  simp [hzero]

/-- The variance of a discrete Laplace count, including the zero-parameter point mass. -/
@[simp]
theorem variance_intCast_discreteLaplaceMeasure (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    variance (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) = 2 * q / (1 - q) ^ 2 := by
  let p : unitInterval := ⟨1 - q, by constructor <;> linarith⟩
  have hp : p ≠ 0 := ne_of_gt (unitInterval.coe_pos.mp (by dsimp [p]; linarith))
  have hq : 1 - (p : ℝ) = q := by simp [p]
  have hG : MemLp id 2 ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) := by
    rw [geometricMeasure_eq_negativeBinomialMeasure_one p hp]
    exact memLp_id_map_cast_negativeBinomialMeasure zero_le_one
      (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)) p.2.2 2
  have hmap := map_intCast_discreteLaplaceMeasure m hp
  rw [hq] at hmap
  rw [← variance_id_map (by fun_prop), hmap, variance_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, id_eq]
  rw [variance_add_const (by fun_prop)]
  simp only [sub_eq_add_neg]
  have hvar := variance_add_prod hG hG.neg
  simp only [id_eq, Pi.neg_apply] at hvar
  rw [hvar, variance_neg, variance_id_map_cast_geometricMeasure]
  simp only [p, sub_sub_cancel, ← sub_eq_add_neg]
  ring

/-- The characteristic function of the real-cast discrete Laplace law. -/
theorem charFun_map_intCast_discreteLaplaceMeasure (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (t : ℝ) :
    charFun ((discreteLaplaceMeasure m q).map (Int.cast : ℤ → ℝ)) t =
      Complex.exp ((t : ℂ) * m * Complex.I) * (1 - (q : ℂ)) ^ 2 /
        ((1 - q * Complex.exp ((t : ℂ) * Complex.I)) *
          (1 - q * Complex.exp (-(t : ℂ) * Complex.I))) := by
  let p : unitInterval := ⟨1 - q, by constructor <;> linarith⟩
  have hp : p ≠ 0 := ne_of_gt (unitInterval.coe_pos.mp (by dsimp [p]; linarith))
  have hq : 1 - (p : ℝ) = q := by simp [p]
  have hmap := map_intCast_discreteLaplaceMeasure m hp
  rw [hq] at hmap
  rw [hmap, charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  have hfun :
      (fun z : ℝ × ℝ => Complex.exp ((t : ℂ) * ((z.1 - z.2 + m : ℝ) : ℂ) * Complex.I)) =
        fun z => Complex.exp ((t : ℂ) * m * Complex.I) *
          (Complex.exp ((t : ℂ) * z.1 * Complex.I) *
            Complex.exp ((-t : ℂ) * z.2 * Complex.I)) := by
    funext z
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun, integral_const_mul, integral_prod_mul
    (fun x : ℝ => Complex.exp ((t : ℂ) * x * Complex.I))
    (fun x : ℝ => Complex.exp ((-t : ℂ) * x * Complex.I)),
    ← charFun_apply_real, ← Complex.ofReal_neg, ← charFun_apply_real,
    charFun_map_cast_geometricMeasure hp, charFun_map_cast_geometricMeasure hp]
  simp only [p, Complex.ofReal_sub, Complex.ofReal_one, sub_sub_cancel,
    div_eq_mul_inv, mul_inv_rev]
  ring_nf

end TauCeti.Probability
