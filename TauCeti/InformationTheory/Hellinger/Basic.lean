/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Hellinger affinity and squared Hellinger distance

For two measures `P` and `Q` on a measurable space `α`, their **Hellinger affinity** is
$$\rho(P, Q) = \int \sqrt{\frac{\mathrm{d}P}{\mathrm{d}(P + Q)}
  \frac{\mathrm{d}Q}{\mathrm{d}(P + Q)}}\,\mathrm{d}(P + Q),$$
and their **squared Hellinger distance** is
$$H^2(P, Q) = 2\bigl(1 - \rho(P, Q)\bigr).$$

With this normalization (Tsybakov, Definition 2.3, p. 83; Samworth and Shah, p. 233), probability
measures satisfy $0 \le \rho(P, Q) \le 1$, $0 \le H^2(P, Q) \le 2$, and
$$H^2(P, Q) = \int \Bigl(\sqrt{\frac{\mathrm{d}P}{\mathrm{d}\mu}} -
  \sqrt{\frac{\mathrm{d}Q}{\mathrm{d}\mu}}\Bigr)^2\,\mathrm{d}\mu$$
for any σ-finite dominating measure `μ` with `P ≪ μ` and `Q ≪ μ`. Moreover, `√(sqHellinger P Q)`
is a metric on probability measures: it is symmetric, satisfies the triangle inequality, vanishes
precisely when `P = Q`, and equals `√2` (equivalently `sqHellinger P Q = 2`) precisely when
`P ⟂ₘ Q`.

Properties of `hellingerAffinity` that do not require unit mass are proved for general finite
measures (and symmetry, nonnegativity, and zero-measure identities require no finiteness
hypotheses at all).

## Main definitions

* `TauCeti.hellingerAffinity`: the Hellinger affinity of two measures.
* `TauCeti.sqHellinger`: the squared Hellinger distance `2 * (1 - hellingerAffinity P Q)`.

## Main results

* `TauCeti.hellingerAffinity_eq_integral`: independence of the σ-finite dominating measure.
* `TauCeti.hellingerAffinity_eq_integral_of_withDensity`: explicit integral formula for measures
  given as densities against a common σ-finite measure.
* `TauCeti.integral_sq_sqrt_rnDeriv_sub` and `TauCeti.sqHellinger_eq_integral`: squared `L²`
  representation of `sqHellinger`.
* `TauCeti.hellingerAffinity_le_sqrt_mul` and `TauCeti.hellingerAffinity_le_one`: Cauchy–Schwarz
  upper bound on the Hellinger affinity.
* `TauCeti.hellingerAffinity_eq_zero_iff` and `TauCeti.sqHellinger_eq_two_iff`: characterization
  of mutual singularity.
* `TauCeti.hellingerAffinity_eq_one_iff` and `TauCeti.sqHellinger_eq_zero_iff`: characterization
  of equality of probability measures.
* `TauCeti.sqrt_sqHellinger_triangle`: triangle inequality for the Hellinger distance
  `√(sqHellinger P Q)`.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Definition 2.3,
  p. 83.
* R. J. Samworth and R. D. Shah, *Modern Statistical Methods and Theory*, Cambridge University
  Press, 2026, p. 233.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {α : Type*} {mα : MeasurableSpace α}

/-- The **Hellinger affinity** of two measures `P` and `Q`, defined via their Radon–Nikodym
derivatives with respect to the canonical dominating measure `P + Q`. -/
def hellingerAffinity (P Q : Measure α) : ℝ :=
  ∫ x, √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) ∂(P + Q)

/-- The **squared Hellinger distance** `2 * (1 - hellingerAffinity P Q)`. For probability measures
this takes values in `[0, 2]` and equals `∫ (√(dP/dμ) - √(dQ/dμ))² dμ` for any σ-finite dominating
measure `μ`. -/
def sqHellinger (P Q : Measure α) : ℝ :=
  2 * (1 - hellingerAffinity P Q)

theorem hellingerAffinity_def (P Q : Measure α) :
    hellingerAffinity P Q =
      ∫ x, √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) ∂(P + Q) := by
  rfl

theorem sqHellinger_def (P Q : Measure α) :
    sqHellinger P Q = 2 * (1 - hellingerAffinity P Q) := by
  rfl

theorem hellingerAffinity_comm (P Q : Measure α) :
    hellingerAffinity P Q = hellingerAffinity Q P := by
  rw [hellingerAffinity_def, hellingerAffinity_def, add_comm P Q]
  congr 1 with x
  rw [mul_comm]

theorem sqHellinger_comm (P Q : Measure α) :
    sqHellinger P Q = sqHellinger Q P := by
  rw [sqHellinger_def, sqHellinger_def, hellingerAffinity_comm]

theorem hellingerAffinity_nonneg (P Q : Measure α) :
    0 ≤ hellingerAffinity P Q :=
  integral_nonneg fun _ => Real.sqrt_nonneg _

@[simp]
theorem hellingerAffinity_zero_left (Q : Measure α) :
    hellingerAffinity 0 Q = 0 := by
  rw [hellingerAffinity_def, zero_add]
  have hae : ∀ᵐ x ∂Q,
      √(((0 : Measure α).rnDeriv Q x).toReal * (Q.rnDeriv Q x).toReal) = 0 := by
    filter_upwards [Measure.rnDeriv_zero Q] with x hx
    simp [hx]
  rw [integral_congr_ae hae, integral_zero]

@[simp]
theorem hellingerAffinity_zero_right (P : Measure α) :
    hellingerAffinity P 0 = 0 := by
  rw [hellingerAffinity_comm, hellingerAffinity_zero_left]

/-- For finite measures `P` and `Q`, the geometric mean of their Radon–Nikodym derivatives with
respect to any measure `μ` is `μ`-integrable. -/
theorem integrable_sqrt_rnDeriv_mul (P Q μ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (fun x => √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal)) μ := by
  refine (P.integrable_toReal_rnDeriv.add Q.integrable_toReal_rnDeriv).mono' ?_ ?_
  · exact (((P.measurable_rnDeriv μ).ennreal_toReal.mul
      (Q.measurable_rnDeriv μ).ennreal_toReal).sqrt).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have ha : 0 ≤ (P.rnDeriv μ x).toReal := ENNReal.toReal_nonneg
    have hb : 0 ≤ (Q.rnDeriv μ x).toReal := ENNReal.toReal_nonneg
    have hsq : 0 ≤ (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 := sq_nonneg _
    rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb, mul_assoc, ← Real.sqrt_mul ha] at hsq
    simp only [Pi.add_apply]
    linarith [Real.sqrt_nonneg ((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal)]

/-- **Independence of the dominating measure.** For finite measures `P` and `Q` absolutely
continuous with respect to a σ-finite measure `μ`, the Hellinger affinity equals the integral of
`√((dP/dμ) * (dQ/dμ))` against `μ`. -/
theorem hellingerAffinity_eq_integral {P Q μ : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ) :
    hellingerAffinity P Q =
      ∫ x, √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) ∂μ := by
  have hPν : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hνμ : P + Q ≪ μ := hP.add_left hQ
  rw [hellingerAffinity_def, ← integral_toReal_rnDeriv_mul hνμ]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := μ) hPν,
    Measure.rnDeriv_mul_rnDeriv (κ := μ) hQν] with x hPx hQx
  simp only [Pi.mul_apply] at hPx hQx
  rw [← hPx, ← hQx, ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hc : 0 ≤ ((P + Q).rnDeriv μ x).toReal := ENNReal.toReal_nonneg
  calc
    ((P + Q).rnDeriv μ x).toReal *
        √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal)
      = √(((P + Q).rnDeriv μ x).toReal ^ 2) *
          √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) := by
        rw [Real.sqrt_sq hc]
    _ = √(((P + Q).rnDeriv μ x).toReal ^ 2 *
          ((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal)) := by
        rw [← Real.sqrt_mul (sq_nonneg _)]
    _ = √((P.rnDeriv (P + Q) x).toReal * ((P + Q).rnDeriv μ x).toReal *
          ((Q.rnDeriv (P + Q) x).toReal * ((P + Q).rnDeriv μ x).toReal)) := by
        congr 1; ring

/-- Hellinger affinity of two finite measures given as densities with respect to a common σ-finite
measure `μ`. -/
theorem hellingerAffinity_eq_integral_of_withDensity {μ : Measure α} [SigmaFinite μ]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    [IsFiniteMeasure (μ.withDensity f)] [IsFiniteMeasure (μ.withDensity g)] :
    hellingerAffinity (μ.withDensity f) (μ.withDensity g) =
      ∫ x, √((f x).toReal * (g x).toReal) ∂μ := by
  rw [hellingerAffinity_eq_integral (withDensity_absolutelyContinuous μ f)
    (withDensity_absolutelyContinuous μ g)]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity₀ μ hf, Measure.rnDeriv_withDensity₀ μ hg] with x hx hy
  rw [hx, hy]

@[simp]
theorem hellingerAffinity_self (P : Measure α) [IsFiniteMeasure P] :
    hellingerAffinity P P = P.real Set.univ := by
  rw [hellingerAffinity_eq_integral (μ := P) .rfl .rfl]
  have h : ∫ x, √((P.rnDeriv P x).toReal * (P.rnDeriv P x).toReal) ∂P = ∫ _, (1 : ℝ) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [P.rnDeriv_self] with x hx
    simp [hx]
  rw [h, integral_const, smul_eq_mul, mul_one]

@[simp]
theorem sqHellinger_self (P : Measure α) [IsProbabilityMeasure P] :
    sqHellinger P P = 0 := by
  simp [sqHellinger_def]

theorem hellingerAffinity_smul_left (c : ℝ≥0) (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity (c • P) Q = √(c : ℝ) * hellingerAffinity P Q := by
  have hcP : c • P ≪ P + Q := fun s hs => by
    simp [(Measure.AbsolutelyContinuous.rfl.add_right Q) hs]
  have hQ : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  rw [hellingerAffinity_eq_integral hcP hQ, hellingerAffinity_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_smul_left' P (P + Q) c] with x hx
  rw [hx, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, mul_assoc, Real.sqrt_mul c.coe_nonneg]

theorem hellingerAffinity_smul_right (P : Measure α) (c : ℝ≥0) (Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity P (c • Q) = √(c : ℝ) * hellingerAffinity P Q := by
  rw [hellingerAffinity_comm, hellingerAffinity_smul_left, hellingerAffinity_comm]

/-- For finite measures `P` and `Q` dominated by a σ-finite measure `μ`, the squared `L²(μ)`
distance between `√(dP/dμ)` and `√(dQ/dμ)` equals `P(univ) + Q(univ) - 2 * hellingerAffinity P Q`.
-/
theorem integral_sq_sqrt_rnDeriv_sub {P Q μ : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ) :
    ∫ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 ∂μ =
      P.real Set.univ + Q.real Set.univ - 2 * hellingerAffinity P Q := by
  have hexp : ∀ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 =
      ((P.rnDeriv μ x).toReal + (Q.rnDeriv μ x).toReal) -
        2 * √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) := fun x => by
    have ha : 0 ≤ (P.rnDeriv μ x).toReal := ENNReal.toReal_nonneg
    have hb : 0 ≤ (Q.rnDeriv μ x).toReal := ENNReal.toReal_nonneg
    rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb, mul_assoc, ← Real.sqrt_mul ha]
    ring
  simp_rw [hexp]
  have hadd : Integrable (fun x => (P.rnDeriv μ x).toReal + (Q.rnDeriv μ x).toReal) μ :=
    P.integrable_toReal_rnDeriv.add Q.integrable_toReal_rnDeriv
  rw [integral_sub hadd ((integrable_sqrt_rnDeriv_mul P Q μ).const_mul 2),
    integral_add P.integrable_toReal_rnDeriv Q.integrable_toReal_rnDeriv,
    integral_const_mul, Measure.integral_toReal_rnDeriv hP, Measure.integral_toReal_rnDeriv hQ,
    hellingerAffinity_eq_integral hP hQ]

/-- **Squared `L²` formula for `sqHellinger`.** For probability measures `P` and `Q` dominated by a
σ-finite measure `μ`, `sqHellinger P Q = ∫ (√(dP/dμ) - √(dQ/dμ))² dμ`. -/
theorem sqHellinger_eq_integral {P Q μ : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ) :
    sqHellinger P Q =
      ∫ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 ∂μ := by
  rw [integral_sq_sqrt_rnDeriv_sub hP hQ, sqHellinger_def, probReal_univ, probReal_univ]
  ring

private lemma memLp_sqrt_rnDeriv (P μ : Measure α) [IsFiniteMeasure P] :
    MemLp (fun x => √(P.rnDeriv μ x).toReal) 2 μ := by
  refine (memLp_two_iff_integrable_sq
    ((P.measurable_rnDeriv μ).ennreal_toReal.sqrt.aestronglyMeasurable)).2 ?_
  simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using P.integrable_toReal_rnDeriv

private lemma norm_toLp_sqrt_rnDeriv {P μ : Measure α} [IsFiniteMeasure P] [SigmaFinite μ]
    (hP : P ≪ μ) :
    ‖(memLp_sqrt_rnDeriv P μ).toLp (fun x => √(P.rnDeriv μ x).toReal)‖ = √(P.real Set.univ) := by
  set u := (memLp_sqrt_rnDeriv P μ).toLp (fun x => √(P.rnDeriv μ x).toReal)
  have hsq : ‖u‖ ^ 2 = P.real Set.univ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    calc
      ∫ x, inner ℝ (u x) (u x) ∂μ
        = ∫ x, (P.rnDeriv μ x).toReal ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_sqrt_rnDeriv P μ).coeFn_toLp] with x hx
          rw [hx, RCLike.inner_apply, conj_trivial, Real.mul_self_sqrt ENNReal.toReal_nonneg]
      _ = P.real Set.univ := Measure.integral_toReal_rnDeriv hP
  rw [← Real.sqrt_sq (norm_nonneg u), hsq]

/-- **Cauchy–Schwarz upper bound** for Hellinger affinity of finite measures. -/
theorem hellingerAffinity_le_sqrt_mul (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity P Q ≤ √(P.real Set.univ * Q.real Set.univ) := by
  set ν := P + Q
  set uP := (memLp_sqrt_rnDeriv P ν).toLp (fun x => √(P.rnDeriv ν x).toReal)
  set uQ := (memLp_sqrt_rnDeriv Q ν).toLp (fun x => √(Q.rnDeriv ν x).toReal)
  have hinner : hellingerAffinity P Q = inner ℝ uP uQ := by
    rw [hellingerAffinity_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_sqrt_rnDeriv P ν).coeFn_toLp,
      (memLp_sqrt_rnDeriv Q ν).coeFn_toLp] with x hx hy
    rw [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm,
      ← Real.sqrt_mul ENNReal.toReal_nonneg]
  calc
    hellingerAffinity P Q = inner ℝ uP uQ := hinner
    _ ≤ ‖uP‖ * ‖uQ‖ := real_inner_le_norm uP uQ
    _ = √(P.real Set.univ) * √(Q.real Set.univ) := by
      rw [norm_toLp_sqrt_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right Q),
        norm_toLp_sqrt_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right' P)]
    _ = √(P.real Set.univ * Q.real Set.univ) :=
      (Real.sqrt_mul measureReal_nonneg _).symm

theorem hellingerAffinity_le_one (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    hellingerAffinity P Q ≤ 1 := by
  simpa using hellingerAffinity_le_sqrt_mul P Q

theorem sqHellinger_nonneg (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    0 ≤ sqHellinger P Q := by
  rw [sqHellinger_def]
  linarith [hellingerAffinity_le_one P Q]

theorem sqHellinger_le_two (P Q : Measure α) :
    sqHellinger P Q ≤ 2 := by
  rw [sqHellinger_def]
  linarith [hellingerAffinity_nonneg P Q]

/-- Two finite measures have Hellinger affinity `0` if and only if they are mutually singular. -/
theorem hellingerAffinity_eq_zero_iff {P Q : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity P Q = 0 ↔ P ⟂ₘ Q := by
  constructor
  · intro h
    rw [hellingerAffinity_def, integral_eq_zero_iff_of_nonneg (fun _ => Real.sqrt_nonneg _)
      (integrable_sqrt_rnDeriv_mul P Q (P + Q))] at h
    have hae : ∀ᵐ x ∂(P + Q), P.rnDeriv (P + Q) x = 0 ∨ Q.rnDeriv (P + Q) x = 0 := by
      filter_upwards [h, P.rnDeriv_lt_top (P + Q), Q.rnDeriv_lt_top (P + Q)] with x hx hPt hQt
      have hmul : (P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal = 0 := by
        simpa [Real.sqrt_eq_zero (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)] using hx
      rcases mul_eq_zero.mp hmul with hP0 | hQ0
      · exact Or.inl ((ENNReal.toReal_eq_zero_iff _).mp hP0 |>.resolve_right hPt.ne)
      · exact Or.inr ((ENNReal.toReal_eq_zero_iff _).mp hQ0 |>.resolve_right hQt.ne)
    refine ⟨{x | P.rnDeriv (P + Q) x = 0},
      (P.measurable_rnDeriv (P + Q)) (measurableSet_singleton 0), ?_, ?_⟩
    · rw [← Measure.setLIntegral_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right Q)]
      exact setLIntegral_eq_zero (P.measurable_rnDeriv (P + Q) (measurableSet_singleton 0))
        fun x hx => hx
    · rw [← Measure.setLIntegral_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right' P)]
      refine (setLIntegral_eq_zero_iff'
        ((P.measurable_rnDeriv (P + Q) (measurableSet_singleton 0)).compl)
        (Q.measurable_rnDeriv (P + Q)).aemeasurable).mpr ?_
      filter_upwards [hae] with x hx hne
      exact hx.resolve_left hne
  · intro h
    rw [hellingerAffinity_def]
    have hPQ : ∀ᵐ x ∂Q, P.rnDeriv (P + Q) x = 0 :=
      Measure.rnDeriv_eq_zero_of_mutuallySingular h (Measure.AbsolutelyContinuous.rfl.add_right' P)
    have hQP : ∀ᵐ x ∂P, Q.rnDeriv (P + Q) x = 0 :=
      Measure.rnDeriv_eq_zero_of_mutuallySingular h.symm
        (Measure.AbsolutelyContinuous.rfl.add_right Q)
    have hae : ∀ᵐ x ∂(P + Q),
        √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) = 0 := by
      rw [ae_add_measure_iff]
      exact ⟨hQP.mono fun x hx => by simp [hx], hPQ.mono fun x hx => by simp [hx]⟩
    rw [integral_congr_ae hae, integral_zero]

theorem sqHellinger_eq_two_iff {P Q : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    sqHellinger P Q = 2 ↔ P ⟂ₘ Q := by
  rw [sqHellinger_def, ← hellingerAffinity_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-- Distinct Dirac probability measures have Hellinger affinity `0`. -/
theorem hellingerAffinity_dirac_of_ne [MeasurableSingletonClass α] {a b : α} (hab : a ≠ b) :
    hellingerAffinity (Measure.dirac a) (Measure.dirac b) = 0 := by
  rw [hellingerAffinity_eq_zero_iff]
  exact ⟨{a}ᶜ, (measurableSet_singleton a).compl, by simp, by simp [hab.symm]⟩

/-- Two probability measures have Hellinger affinity `1` if and only if they are equal. -/
theorem hellingerAffinity_eq_one_iff {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    hellingerAffinity P Q = 1 ↔ P = Q := by
  constructor
  · intro h
    have hPν : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
    have hQν : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
    have hint0 : ∫ x, (√(P.rnDeriv (P + Q) x).toReal - √(Q.rnDeriv (P + Q) x).toReal) ^ 2
        ∂(P + Q) = 0 := by
      rw [← sqHellinger_eq_integral hPν hQν, sqHellinger_def, h]
      ring
    have hint : Integrable
        (fun x => (√(P.rnDeriv (P + Q) x).toReal - √(Q.rnDeriv (P + Q) x).toReal) ^ 2)
        (P + Q) :=
      ((memLp_sqrt_rnDeriv P (P + Q)).sub (memLp_sqrt_rnDeriv Q (P + Q))).integrable_sq
    rw [integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint] at hint0
    have hrn : P.rnDeriv (P + Q) =ᵐ[P + Q] Q.rnDeriv (P + Q) := by
      filter_upwards [hint0, P.rnDeriv_lt_top (P + Q), Q.rnDeriv_lt_top (P + Q)]
        with x hx hPt hQt
      have hsub : √(P.rnDeriv (P + Q) x).toReal - √(Q.rnDeriv (P + Q) x).toReal = 0 :=
        sq_eq_zero_iff.mp hx
      have hsq : (P.rnDeriv (P + Q) x).toReal = (Q.rnDeriv (P + Q) x).toReal :=
        (Real.sqrt_inj ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mp (sub_eq_zero.mp hsub)
      exact (ENNReal.toReal_eq_toReal_iff' hPt.ne hQt.ne).mp hsq
    calc
      P = (P + Q).withDensity (P.rnDeriv (P + Q)) :=
        (Measure.withDensity_rnDeriv_eq P (P + Q) hPν).symm
      _ = (P + Q).withDensity (Q.rnDeriv (P + Q)) := withDensity_congr_ae hrn
      _ = Q := Measure.withDensity_rnDeriv_eq Q (P + Q) hQν
  · rintro rfl
    simp

theorem sqHellinger_eq_zero_iff {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    sqHellinger P Q = 0 ↔ P = Q := by
  rw [sqHellinger_def, ← hellingerAffinity_eq_one_iff]
  constructor <;> intro h <;> linarith

/-- **Triangle inequality for Hellinger distance.** For probability measures `P`, `Q`, `R`,
`√(sqHellinger P R) ≤ √(sqHellinger P Q) + √(sqHellinger Q R)`. -/
theorem sqrt_sqHellinger_triangle (P Q R : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    √(sqHellinger P R) ≤ √(sqHellinger P Q) + √(sqHellinger Q R) := by
  set μ := P + Q + R
  have hPμ : P ≪ μ :=
    (Measure.AbsolutelyContinuous.rfl.add_right Q).add_right R
  have hQμ : Q ≪ μ :=
    (Measure.AbsolutelyContinuous.rfl.add_right' P).add_right R
  have hRμ : R ≪ μ := Measure.AbsolutelyContinuous.rfl.add_right' (P + Q)
  have hnorm : ∀ (A B : Measure α) [IsProbabilityMeasure A] [IsProbabilityMeasure B],
      A ≪ μ → B ≪ μ →
      √(sqHellinger A B) =
        ‖(memLp_sqrt_rnDeriv A μ).toLp (fun x => √(A.rnDeriv μ x).toReal) -
          (memLp_sqrt_rnDeriv B μ).toLp (fun x => √(B.rnDeriv μ x).toReal)‖ := by
    intro A B _ _ hA hB
    set uA := (memLp_sqrt_rnDeriv A μ).toLp (fun x => √(A.rnDeriv μ x).toReal)
    set uB := (memLp_sqrt_rnDeriv B μ).toLp (fun x => √(B.rnDeriv μ x).toReal)
    have hsq : ‖uA - uB‖ ^ 2 = sqHellinger A B := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def, sqHellinger_eq_integral hA hB]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub uA uB, (memLp_sqrt_rnDeriv A μ).coeFn_toLp,
        (memLp_sqrt_rnDeriv B μ).coeFn_toLp] with x hsub hx hy
      rw [hsub, Pi.sub_apply, hx, hy, RCLike.inner_apply, conj_trivial, sq]
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm P R hPμ hRμ, hnorm P Q hPμ hQμ, hnorm Q R hQμ hRμ]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

end TauCeti
