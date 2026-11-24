/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Real.Sqrt
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.AbsolutelyContinuous
import TauCeti.MeasureTheory.Measure.Decomposition.RNDeriv

/-!
# The Hellinger affinity and the squared Hellinger distance

For measures `P` and `Q` on a measurable space, with densities `p = dP/dν` and `q = dQ/dν`
relative to `ν = P + Q`, the *Hellinger affinity* is `∫ √(p q) dν` and the *squared Hellinger
distance* is `2 (1 - ∫ √(p q) dν)`. For probability measures the latter equals
`∫ (√(dP/dμ) - √(dQ/dμ))² dμ` for every σ-finite measure `μ` dominating `P` and `Q`. The
normalization is Tsybakov's: the squared distance is not halved, and takes values in `[0, 2]`.

These quantities measure how far apart two probability laws are. The affinity bounds the least
total error of a test between two laws from below, and it is multiplicative over products of
laws, which is why it is used in lower bounds involving many independent observations.

## Main definitions

* `TauCeti.hellingerAffinity P Q`: the Hellinger affinity `∫ √(dP/dν · dQ/dν) dν`, with
  `ν = P + Q`.
* `TauCeti.sqHellinger P Q`: the squared Hellinger distance `2 (1 - hellingerAffinity P Q)`.

## Main results

* `TauCeti.hellingerAffinity_eq_integral`: for σ-finite `P` and `Q`, the affinity may be computed
  from the densities with respect to any σ-finite measure dominating both measures.
* `TauCeti.sqHellinger_eq_integral`: for probability measures,
  `sqHellinger P Q = ∫ (√(dP/dμ) - √(dQ/dμ))² dμ` for any σ-finite dominating `μ`.
* `TauCeti.ofReal_sqrt_sqHellinger_eq_eLpNorm`: for probability measures, the Hellinger distance
  `√(sqHellinger P Q)` is the `L²(μ)` seminorm of `√(dP/dμ) - √(dQ/dμ)`.
* `TauCeti.hellingerAffinity_mem_Icc`, `TauCeti.sqHellinger_mem_Icc`: for probability measures
  the affinity lies in `[0, 1]` and the squared distance in `[0, 2]`.
* `TauCeti.sqHellinger_eq_zero_iff`: the squared distance vanishes exactly on the diagonal.
* `TauCeti.sqrt_sqHellinger_triangle`: the Hellinger distance `√(sqHellinger P Q)`, symmetric by
  `TauCeti.sqHellinger_comm`, satisfies the triangle inequality, so it is a metric on
  probability measures.
* `TauCeti.hellingerAffinity_eq_zero_iff`, `TauCeti.sqHellinger_eq_two_iff`: the affinity
  vanishes, and the squared distance is maximal, exactly for mutually singular measures.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Definition 2.3
  and its properties (i)–(iii), p. 83.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]

/-- The Hellinger affinity `∫ √(p q) dν` of two measures `P` and `Q`, where `p` and `q` are the
densities of `P` and `Q` with respect to `ν = P + Q`. By `hellingerAffinity_eq_integral`, for
σ-finite `P` and `Q` any σ-finite measure dominating both gives the same value. -/
noncomputable def hellingerAffinity (P Q : Measure X) : ℝ :=
  ∫ x, √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) ∂(P + Q)

/-- The squared Hellinger distance `2 (1 - hellingerAffinity P Q)`. For probability measures it
is `∫ (√p - √q)²` (`sqHellinger_eq_integral`) and lies in `[0, 2]` (`sqHellinger_mem_Icc`); it is
not halved. -/
noncomputable def sqHellinger (P Q : Measure X) : ℝ := 2 * (1 - hellingerAffinity P Q)

section Basic

variable (P Q : Measure X)

/-- The defining formula of the Hellinger affinity, with densities relative to `P + Q`. -/
theorem hellingerAffinity_def :
    hellingerAffinity P Q =
      ∫ x, √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) ∂(P + Q) :=
  (rfl)

/-- The defining formula of the squared Hellinger distance. -/
theorem sqHellinger_def : sqHellinger P Q = 2 * (1 - hellingerAffinity P Q) := (rfl)

/-- The Hellinger affinity is symmetric. -/
theorem hellingerAffinity_comm : hellingerAffinity P Q = hellingerAffinity Q P := by
  simp only [hellingerAffinity, add_comm Q P, mul_comm]

/-- The squared Hellinger distance is symmetric. -/
theorem sqHellinger_comm : sqHellinger P Q = sqHellinger Q P := by
  rw [sqHellinger, sqHellinger, hellingerAffinity_comm]

/-- The Hellinger affinity is nonnegative. -/
theorem hellingerAffinity_nonneg : 0 ≤ hellingerAffinity P Q :=
  integral_nonneg fun _ ↦ Real.sqrt_nonneg _

/-- The squared Hellinger distance is at most `2`, since the affinity is nonnegative. -/
theorem sqHellinger_le_two : sqHellinger P Q ≤ 2 := by
  rw [sqHellinger]
  linarith [hellingerAffinity_nonneg P Q]

end Basic

/-- The Hellinger affinity of σ-finite `P` and `Q` does not depend on the dominating measure: for
every σ-finite `μ` with `P ≪ μ` and `Q ≪ μ`, it is `∫ √(dP/dμ · dQ/dμ) dμ`. -/
theorem hellingerAffinity_eq_integral {P Q μ : Measure X} [SigmaFinite P] [SigmaFinite Q]
    [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ) :
    hellingerAffinity P Q = ∫ x, √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) ∂μ := by
  refine (integral_toReal_rnDeriv_mul (hP.add_left hQ)).symm.trans
    (integral_congr_ae ?_)
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := μ) (Measure.absolutelyContinuous_self_add P Q),
    Measure.rnDeriv_mul_rnDeriv (κ := μ) (Measure.absolutelyContinuous_add_self P Q)]
    with x hPx hQx
  rw [← hPx, ← hQx, Pi.mul_apply, Pi.mul_apply, ENNReal.toReal_mul, ENNReal.toReal_mul,
    mul_mul_mul_comm, Real.sqrt_mul' _ (mul_self_nonneg _),
    Real.sqrt_mul_self ENNReal.toReal_nonneg, mul_comm]

/-- The Hellinger affinity of a σ-finite measure with itself is its total mass (the junk value
`0` when that mass is infinite). -/
@[simp]
theorem hellingerAffinity_self (P : Measure X) [SigmaFinite P] :
    hellingerAffinity P P = P.real univ := by
  rw [hellingerAffinity_eq_integral (μ := P) .rfl .rfl]
  simp only [Real.sqrt_mul_self ENNReal.toReal_nonneg]
  exact Measure.integral_toReal_rnDeriv .rfl

/-- The squared Hellinger distance of a probability measure to itself is `0`. -/
@[simp]
theorem sqHellinger_self (P : Measure X) [IsProbabilityMeasure P] : sqHellinger P P = 0 := by
  simp [sqHellinger]

/-- The Hellinger affinity of two finite measures is at most the average of their masses. -/
theorem hellingerAffinity_le_add_div_two (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] :
    hellingerAffinity P Q ≤ (P.real univ + Q.real univ) / 2 := by
  have hP := Measure.absolutelyContinuous_self_add P Q
  have hQ := Measure.absolutelyContinuous_add_self P Q
  calc hellingerAffinity P Q
      ≤ ∫ x, ((P.rnDeriv (P + Q) x).toReal + (Q.rnDeriv (P + Q) x).toReal) / 2 ∂(P + Q) :=
        integral_mono (Measure.integrable_sqrt_toReal_rnDeriv_mul P Q _)
          ((Measure.integrable_toReal_rnDeriv.add Measure.integrable_toReal_rnDeriv).div_const 2)
          fun _ ↦ Real.sqrt_mul_le_half_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ = (P.real univ + Q.real univ) / 2 := by
        rw [integral_div, integral_add Measure.integrable_toReal_rnDeriv
          Measure.integrable_toReal_rnDeriv, Measure.integral_toReal_rnDeriv hP,
          Measure.integral_toReal_rnDeriv hQ]

section Probability

variable (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- The Hellinger affinity of two probability measures is at most `1`. -/
theorem hellingerAffinity_le_one : hellingerAffinity P Q ≤ 1 :=
  (hellingerAffinity_le_add_div_two P Q).trans_eq (by norm_num)

/-- The Hellinger affinity of two probability measures lies in `[0, 1]`. -/
theorem hellingerAffinity_mem_Icc : hellingerAffinity P Q ∈ Icc 0 1 :=
  ⟨hellingerAffinity_nonneg P Q, hellingerAffinity_le_one P Q⟩

/-- The squared Hellinger distance between probability measures is nonnegative. -/
theorem sqHellinger_nonneg : 0 ≤ sqHellinger P Q := by
  rw [sqHellinger]
  linarith [hellingerAffinity_le_one P Q]

/-- The squared Hellinger distance between probability measures lies in `[0, 2]`. -/
theorem sqHellinger_mem_Icc : sqHellinger P Q ∈ Icc 0 2 :=
  ⟨sqHellinger_nonneg P Q, sqHellinger_le_two P Q⟩

variable {P Q}

/-- For probability measures, the squared Hellinger distance is `∫ (√(dP/dμ) - √(dQ/dμ))² dμ`
for every σ-finite measure `μ` dominating `P` and `Q`. -/
theorem sqHellinger_eq_integral {μ : Measure X} [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ) :
    sqHellinger P Q = ∫ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 ∂μ := by
  simp only [Real.sq_sqrt_sub_sqrt ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  have hp : Integrable (fun x ↦ (P.rnDeriv μ x).toReal) μ := Measure.integrable_toReal_rnDeriv
  have hq : Integrable (fun x ↦ (Q.rnDeriv μ x).toReal) μ := Measure.integrable_toReal_rnDeriv
  have hpq : Integrable (fun x ↦ (P.rnDeriv μ x).toReal + (Q.rnDeriv μ x).toReal) μ := hp.add hq
  rw [integral_sub hpq ((Measure.integrable_sqrt_toReal_rnDeriv_mul P Q μ).const_mul 2),
    integral_add hp hq,
    integral_const_mul, Measure.integral_toReal_rnDeriv hP, Measure.integral_toReal_rnDeriv hQ,
    ← hellingerAffinity_eq_integral hP hQ, sqHellinger]
  simp only [probReal_univ]
  ring

/-- For probability measures, the Hellinger distance `√(sqHellinger P Q)` is the `L²(μ)` seminorm
of `√(dP/dμ) - √(dQ/dμ)` for every σ-finite measure `μ` dominating `P` and `Q`. -/
theorem ofReal_sqrt_sqHellinger_eq_eLpNorm {μ : Measure X} [SigmaFinite μ] (hP : P ≪ μ)
    (hQ : Q ≪ μ) :
    ENNReal.ofReal √(sqHellinger P Q) =
      eLpNorm (fun x ↦ √(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) 2 μ := by
  refine Eq.trans ?_ ((Measure.memLp_two_sqrt_toReal_rnDeriv P μ).sub
    (Measure.memLp_two_sqrt_toReal_rnDeriv Q μ)).eLpNorm_two_eq_ofReal_sqrt_integral.symm
  rw [sqHellinger_eq_integral hP hQ]
  simp only [Pi.sub_apply, Real.norm_eq_abs, sq_abs]

/-- The squared Hellinger distance between probability measures vanishes exactly when the
measures are equal. -/
theorem sqHellinger_eq_zero_iff : sqHellinger P Q = 0 ↔ P = Q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ sqHellinger_self P⟩
  have hP := Measure.absolutelyContinuous_self_add P Q
  have hQ := Measure.absolutelyContinuous_add_self P Q
  rw [sqHellinger_eq_integral hP hQ, integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _)
    (Measure.integrable_sq_sqrt_toReal_rnDeriv_sub P Q _)] at h
  refine (Measure.withDensity_rnDeriv_eq P _ hP).symm.trans
    ((withDensity_congr_ae ?_).trans (Measure.withDensity_rnDeriv_eq Q _ hQ))
  filter_upwards [h, Measure.rnDeriv_ne_top P (P + Q), Measure.rnDeriv_ne_top Q (P + Q)]
    with x hx hPx hQx
  rw [Pi.zero_apply, sq_eq_zero_iff, sub_eq_zero,
    Real.sqrt_inj ENNReal.toReal_nonneg ENNReal.toReal_nonneg] at hx
  exact (ENNReal.toReal_eq_toReal_iff' hPx hQx).mp hx

end Probability

/-- The Hellinger affinity of two finite measures vanishes exactly when they are mutually
singular. -/
theorem hellingerAffinity_eq_zero_iff {P Q : Measure X} [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity P Q = 0 ↔ P ⟂ₘ Q := by
  have hP := Measure.absolutelyContinuous_self_add P Q
  have hQ := Measure.absolutelyContinuous_add_self P Q
  -- A measure `S ≪ P + Q` vanishes on `s` iff `P + Q` does on the part of `s` where `dS/d(P + Q)`
  -- is nonzero.
  have hzero (S : Measure X) [IsFiniteMeasure S] (hS : S ≪ P + Q) (s : Set X) :
      S s = 0 ↔ (P + Q) ({x | S.rnDeriv (P + Q) x ≠ 0} ∩ s) = 0 := by
    rw [← withDensity_apply_eq_zero (S.measurable_rnDeriv _), Measure.withDensity_rnDeriv_eq S _ hS]
  rw [hellingerAffinity, integral_eq_zero_iff_of_nonneg (fun _ ↦ Real.sqrt_nonneg _)
    (Measure.integrable_sqrt_toReal_rnDeriv_mul P Q _)]
  constructor
  · intro h
    refine ⟨{x | P.rnDeriv (P + Q) x = 0},
      measurableSet_eq_fun (P.measurable_rnDeriv _) measurable_const, ?_, ?_⟩
    · rw [hzero P hP]
      convert measure_empty (μ := P + Q)
      ext x
      simp
    · rw [hzero Q hQ, measure_eq_zero_iff_ae_notMem]
      filter_upwards [h, Measure.rnDeriv_ne_top P (P + Q), Measure.rnDeriv_ne_top Q (P + Q)]
        with x hx hPx hQx
      rw [Pi.zero_apply, Real.sqrt_eq_zero (by positivity), mul_eq_zero,
        ENNReal.toReal_eq_zero_iff, ENNReal.toReal_eq_zero_iff] at hx
      simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
      tauto
  · intro h
    rw [Filter.EventuallyEq, ae_add_measure_iff]
    constructor
    · filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular h.symm hP] with x hx
      simp [hx]
    · filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular h hQ] with x hx
      simp [hx]

/-- The squared Hellinger distance between probability measures takes its maximal value `2`
exactly when the measures are mutually singular. -/
theorem sqHellinger_eq_two_iff {P Q : Measure X} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : sqHellinger P Q = 2 ↔ P ⟂ₘ Q := by
  rw [← hellingerAffinity_eq_zero_iff, sqHellinger]
  constructor <;> intro h <;> linarith

/-- The Hellinger distance `√(sqHellinger P Q)` satisfies the triangle inequality: it is the
`L²(μ)` distance between `√(dP/dμ)` and `√(dQ/dμ)` for `μ = P + Q + R`. -/
theorem sqrt_sqHellinger_triangle (P Q R : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    √(sqHellinger P R) ≤ √(sqHellinger P Q) + √(sqHellinger Q R) := by
  have hP : P ≪ P + Q + R := (Measure.absolutelyContinuous_self_add P Q).add_right R
  have hQ : Q ≪ P + Q + R := (Measure.absolutelyContinuous_add_self P Q).add_right R
  have hR : R ≪ P + Q + R := Measure.absolutelyContinuous_add_self _ R
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
    ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ofReal_sqrt_sqHellinger_eq_eLpNorm hP hR, ofReal_sqrt_sqHellinger_eq_eLpNorm hP hQ,
    ofReal_sqrt_sqHellinger_eq_eLpNorm hQ hR]
  -- Minkowski's inequality in `L²(P + Q + R)`.
  refine le_of_eq_of_le (congrArg (eLpNorm · 2 (P + Q + R)) (funext fun x ↦ ?_))
    (eLpNorm_add_le (μ := P + Q + R)
      (f := fun x ↦ √(P.rnDeriv (P + Q + R) x).toReal - √(Q.rnDeriv (P + Q + R) x).toReal)
      (g := fun x ↦ √(Q.rnDeriv (P + Q + R) x).toReal - √(R.rnDeriv (P + Q + R) x).toReal)
      one_le_two)
  simp only [Pi.add_apply, sub_add_sub_cancel]

end TauCeti
