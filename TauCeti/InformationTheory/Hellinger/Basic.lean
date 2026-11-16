/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.Probability.ProductMeasure

/-!
# Hellinger affinity and squared Hellinger distance

This file defines the Hellinger affinity and squared Hellinger distance between two measures on a
measurable space and establishes their foundational properties: independence of the dominating
measure, range and extreme-value characterizations, the metric triangle inequality for the
Hellinger distance `√(sqHellinger P Q)`, invariance under measurable embeddings, tensorization over
binary, finite, and finitely-differing infinite products, and the data processing inequality for
Markov kernels and almost-everywhere measurable maps.

## Conventions

Given two measures `P` and `Q` on a measurable space `X`, we define the **Hellinger affinity**

```text
hellingerAffinity P Q = ∫ x, √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) ∂(P + Q)
```

and the **squared Hellinger distance**

```text
sqHellinger P Q = 2 * (1 - hellingerAffinity P Q).
```

For probability measures `P` and `Q`, `hellingerAffinity P Q ∈ [0, 1]` and
`sqHellinger P Q ∈ [0, 2]`, matching the unhalved normalization of Tsybakov (*Introduction to
Nonparametric Estimation*, Springer, 2009, Definition 2.3, p. 83) and Samworth–Shah (*Modern
Statistical Methods and Theory*, Cambridge University Press, 2026, Lemma 8.10, p. 233).
With any σ-finite dominating measure `μ` (`P ≪ μ` and `Q ≪ μ`),

```text
sqHellinger P Q = ∫ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 ∂μ.
```

## Main statements

* `TauCeti.hellingerAffinity`, `TauCeti.sqHellinger`: the Hellinger affinity and squared Hellinger
  distance.
* `TauCeti.hellingerAffinity_eq_integral`, `TauCeti.sqHellinger_eq_integral`: independence of the
  σ-finite reference measure (requiring only `P ≪ μ ∨ Q ≪ μ` for the affinity).
* `TauCeti.memLp_two_sqrt_rnDeriv`, `TauCeti.integrable_sqrt_rnDeriv_mul`: `L²` membership of
  square-root densities and integrability of the Hellinger integrand for finite measures.
* `TauCeti.hellingerAffinity_le_sqrt_mul`, `TauCeti.hellingerAffinity_mem_Icc`,
  `TauCeti.sqHellinger_mem_Icc`: Cauchy–Schwarz upper bound and range for probability measures.
* `TauCeti.hellingerAffinity_eq_zero_iff`, `TauCeti.sqHellinger_eq_two_iff`: vanishing affinity
  (maximal squared Hellinger distance) characterizes mutual singularity.
* `TauCeti.hellingerAffinity_eq_one_iff`, `TauCeti.sqHellinger_eq_zero_iff`: unit affinity
  (vanishing squared Hellinger distance) characterizes equality of probability measures.
* `TauCeti.sqrt_sqHellinger_triangle`: the triangle inequality for the Hellinger distance
  `√(sqHellinger P Q)`.
* `TauCeti.hellingerAffinity_map_of_measurableEmbedding`, `TauCeti.hellingerAffinity_map_equiv`:
  invariance under measurable embeddings and measurable equivalences.
* `TauCeti.hellingerAffinity_prod`, `TauCeti.hellingerAffinity_pi`, `TauCeti.sqHellinger_pi_const`,
  `TauCeti.hellingerAffinity_infinitePi`: tensorization over binary, finite, and finitely-differing
  infinite product measures.
* `TauCeti.hellingerAffinity_le_comp`, `TauCeti.sqHellinger_comp_le`,
  `TauCeti.hellingerAffinity_le_map`, `TauCeti.sqHellinger_map_le`: data processing inequality
  under Markov kernels and almost-everywhere measurable maps.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The **Hellinger affinity** `∫ √(dP/d(P+Q) · dQ/d(P+Q)) d(P+Q)` of two measures `P` and `Q`.
For probability measures it takes values in `[0, 1]`. -/
def hellingerAffinity (P Q : Measure X) : ℝ :=
  ∫ x, √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) ∂(P + Q)

/-- Unfolding lemma for `TauCeti.hellingerAffinity`. -/
theorem hellingerAffinity_def (P Q : Measure X) :
    hellingerAffinity P Q =
      ∫ x, √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) ∂(P + Q) :=
  (rfl)

/-- The **squared Hellinger distance** `2 * (1 - hellingerAffinity P Q)`. For probability measures
it takes values in `[0, 2]` and equals `∫ (√(dP/dμ) - √(dQ/dμ))² dμ` for any σ-finite dominating
measure `μ`. -/
def sqHellinger (P Q : Measure X) : ℝ :=
  2 * (1 - hellingerAffinity P Q)

/-- Unfolding lemma for `TauCeti.sqHellinger`. -/
theorem sqHellinger_def (P Q : Measure X) :
    sqHellinger P Q = 2 * (1 - hellingerAffinity P Q) :=
  (rfl)

/-! ### Basic properties -/

/-- The Hellinger affinity is always nonnegative. -/
theorem hellingerAffinity_nonneg (P Q : Measure X) : 0 ≤ hellingerAffinity P Q :=
  integral_nonneg fun _ => Real.sqrt_nonneg _

/-- The squared Hellinger distance is at most `2`. -/
theorem sqHellinger_le_two (P Q : Measure X) : sqHellinger P Q ≤ 2 := by
  rw [sqHellinger_def]
  linarith [hellingerAffinity_nonneg P Q]

/-- The Hellinger affinity is symmetric in its two arguments. -/
theorem hellingerAffinity_comm (P Q : Measure X) :
    hellingerAffinity P Q = hellingerAffinity Q P := by
  simp only [hellingerAffinity_def, add_comm P Q, mul_comm]

/-- The squared Hellinger distance is symmetric in its two arguments. -/
theorem sqHellinger_comm (P Q : Measure X) : sqHellinger P Q = sqHellinger Q P := by
  rw [sqHellinger_def, sqHellinger_def, hellingerAffinity_comm]

/-- The Hellinger affinity of the zero measure with any measure is `0`. -/
@[simp]
theorem hellingerAffinity_zero_left (Q : Measure X) : hellingerAffinity 0 Q = 0 := by
  rw [hellingerAffinity_def, zero_add]
  have h : (fun x => √(((0 : Measure X).rnDeriv Q x).toReal * (Q.rnDeriv Q x).toReal)) =ᵐ[Q]
      fun _ => (0 : ℝ) := by
    filter_upwards [Measure.rnDeriv_zero Q] with x hx
    simp [hx]
  rw [integral_congr_ae h, integral_zero]

/-- The Hellinger affinity of any measure with the zero measure is `0`. -/
@[simp]
theorem hellingerAffinity_zero_right (P : Measure X) : hellingerAffinity P 0 = 0 := by
  rw [hellingerAffinity_comm, hellingerAffinity_zero_left]

/-! ### Independence of the dominating measure -/

private theorem hellingerAffinity_eq_integral_of_ac_both (P Q μ : Measure X) [SigmaFinite P]
    [SigmaFinite Q] [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ) :
    hellingerAffinity P Q = ∫ x, √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) ∂μ := by
  have hPν : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hνμ : P + Q ≪ μ := hP.add_left hQ
  have h1 := Measure.rnDeriv_mul_rnDeriv (κ := μ) hPν
  have h2 := Measure.rnDeriv_mul_rnDeriv (κ := μ) hQν
  rw [hellingerAffinity_def, ← integral_toReal_rnDeriv_mul hνμ]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx1 hx2
  rw [← hx1, ← hx2, Pi.mul_apply, Pi.mul_apply, ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hsq : ((P.rnDeriv (P + Q) x).toReal * ((P + Q).rnDeriv μ x).toReal) *
      ((Q.rnDeriv (P + Q) x).toReal * ((P + Q).rnDeriv μ x).toReal) =
      ((P + Q).rnDeriv μ x).toReal ^ 2 *
        ((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) := by
    ring
  rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ENNReal.toReal_nonneg]

private theorem hellingerAffinity_eq_integral_of_ac_left (P Q μ : Measure X) [SigmaFinite P]
    [SigmaFinite Q] [SigmaFinite μ] (hP : P ≪ μ) :
    hellingerAffinity P Q = ∫ x, √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) ∂μ := by
  let Qs := Q.singularPart μ
  let Qa := μ.withDensity (Q.rnDeriv μ)
  have hQeq : Q = Qs + Qa := Measure.haveLebesgueDecomposition_add Q μ
  have hQaμ : Qa ≪ μ := withDensity_absolutelyContinuous _ _
  obtain ⟨s, _, hQss, hμsc⟩ := Measure.mutuallySingular_singularPart Q μ
  have hPsc : P sᶜ = 0 := hP hμsc
  have hPs : P.restrict s = P := Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hPsc)
  have hQs : Q.restrict s = Qa := by
    rw [hQeq, Measure.restrict_add, Measure.restrict_eq_zero.2 hQss, zero_add,
      Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 (hQaμ hμsc))]
  have hrest : (P + Q).restrict s = P + Qa := by rw [Measure.restrict_add, hPs, hQs]
  have hrnP : P.rnDeriv (P + Q) =ᵐ[P + Qa] P.rnDeriv (P + Qa) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
      (Measure.measurable_rnDeriv _ _) fun t ht _ => ?_
    rw [Measure.setLIntegral_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right Qa),
      ← hrest, Measure.restrict_restrict ht,
      Measure.setLIntegral_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right Q),
      ← Measure.restrict_apply ht, hPs]
  have hrnQ : Q.rnDeriv (P + Q) =ᵐ[P + Qa] Qa.rnDeriv (P + Qa) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
      (Measure.measurable_rnDeriv _ _) fun t ht _ => ?_
    rw [Measure.setLIntegral_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right' P),
      ← hrest, Measure.restrict_restrict ht,
      Measure.setLIntegral_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right' P),
      ← Measure.restrict_apply ht, hQs]
  have hzero_sc : ∀ᵐ x ∂(P + Q), x ∉ s →
      √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) = 0 := by
    filter_upwards [Measure.ae_rnDeriv_eq_zero_of_measure_eq_zero (ν := P + Q) hPsc] with x hx hxs
    simp [hx hxs]
  have haff : hellingerAffinity P Q = hellingerAffinity P Qa := by
    rw [hellingerAffinity_def, ← setIntegral_eq_integral_of_ae_compl_eq_zero hzero_sc, hrest,
      hellingerAffinity_def]
    refine integral_congr_ae ?_
    filter_upwards [hrnP, hrnQ] with x hxP hxQ
    rw [hxP, hxQ]
  rw [haff, hellingerAffinity_eq_integral_of_ac_both P Qa μ hP hQaμ]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity μ (Measure.measurable_rnDeriv Q μ)] with x hx
  rw [hx]

/-- **Independence of the reference measure.** For any σ-finite measure `μ` dominating at least one
of two σ-finite measures `P` and `Q`, the Hellinger affinity is `∫ √(dP/dμ · dQ/dμ) dμ`. -/
theorem hellingerAffinity_eq_integral (P Q μ : Measure X) [SigmaFinite P] [SigmaFinite Q]
    [SigmaFinite μ] (h : P ≪ μ ∨ Q ≪ μ) :
    hellingerAffinity P Q = ∫ x, √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) ∂μ := by
  rcases h with hP | hQ
  · exact hellingerAffinity_eq_integral_of_ac_left P Q μ hP
  · rw [hellingerAffinity_comm, hellingerAffinity_eq_integral_of_ac_left Q P μ hQ]
    simp_rw [mul_comm]

/-- The Hellinger affinity of a σ-finite measure with itself is its total real mass. -/
@[simp]
theorem hellingerAffinity_self (P : Measure X) [SigmaFinite P] :
    hellingerAffinity P P = P.real Set.univ := by
  rw [hellingerAffinity_eq_integral P P P (.inl .rfl)]
  have h : (fun x => √((P.rnDeriv P x).toReal * (P.rnDeriv P x).toReal)) =ᵐ[P]
      fun _ => (1 : ℝ) := by
    filter_upwards [P.rnDeriv_self] with x hx
    simp [hx]
  rw [integral_congr_ae h, integral_const, smul_eq_mul, mul_one]

/-- The squared Hellinger distance from a probability measure to itself is `0`. -/
@[simp]
theorem sqHellinger_self (P : Measure X) [IsProbabilityMeasure P] : sqHellinger P P = 0 := by
  simp [sqHellinger_def]

/-- For a finite measure `P` and any reference measure `μ`, the square-root Radon–Nikodym
derivative `√(dP/dμ).toReal` belongs to `L²(μ)`. -/
theorem memLp_two_sqrt_rnDeriv (P μ : Measure X) [IsFiniteMeasure P] :
    MemLp (fun x => √(P.rnDeriv μ x).toReal) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => √(P.rnDeriv μ x).toReal) μ :=
    ((Measure.measurable_rnDeriv P μ).ennreal_toReal.sqrt).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  simp_rw [Real.sq_sqrt ENNReal.toReal_nonneg]
  exact integrableOn_univ.1 (Measure.integrableOn_toReal_rnDeriv (measure_ne_top P _))

/-- For finite measures `P` and `Q` and any reference measure `μ`, the Hellinger integrand
`√((dP/dμ).toReal * (dQ/dμ).toReal)` is `μ`-integrable. -/
theorem integrable_sqrt_rnDeriv_mul (P Q μ : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (fun x => √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal)) μ := by
  simp_rw [Real.sqrt_mul ENNReal.toReal_nonneg]
  exact (memLp_two_sqrt_rnDeriv P μ).integrable_mul (memLp_two_sqrt_rnDeriv Q μ)

/-- For finite measures `P` and `Q` dominated by a σ-finite measure `μ`, the `L²(μ)` squared
distance between `√(dP/dμ)` and `√(dQ/dμ)` is `P(univ) + Q(univ) - 2 * hellingerAffinity P Q`. -/
theorem integral_sq_sub_sqrt_rnDeriv (P Q μ : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ) :
    ∫ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 ∂μ =
      P.real Set.univ + Q.real Set.univ - 2 * hellingerAffinity P Q := by
  have hP_int : Integrable (fun x => (P.rnDeriv μ x).toReal) μ :=
    integrableOn_univ.1 (Measure.integrableOn_toReal_rnDeriv (measure_ne_top P _))
  have hQ_int : Integrable (fun x => (Q.rnDeriv μ x).toReal) μ :=
    integrableOn_univ.1 (Measure.integrableOn_toReal_rnDeriv (measure_ne_top Q _))
  have hsum : Integrable (fun x => (P.rnDeriv μ x).toReal + (Q.rnDeriv μ x).toReal) μ :=
    hP_int.add hQ_int
  have hPQ_int : Integrable (fun x => 2 * √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal)) μ :=
    (integrable_sqrt_rnDeriv_mul P Q μ).const_mul 2
  have hexpand : ∀ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 =
      ((P.rnDeriv μ x).toReal + (Q.rnDeriv μ x).toReal) -
        2 * √((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal) := fun x => by
    rw [sub_sq, Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg,
      Real.sqrt_mul ENNReal.toReal_nonneg]
    ring
  simp_rw [hexpand]
  rw [integral_sub hsum hPQ_int, integral_add hP_int hQ_int, integral_const_mul,
    Measure.integral_toReal_rnDeriv hP, Measure.integral_toReal_rnDeriv hQ,
    hellingerAffinity_eq_integral P Q μ (.inl hP)]

/-- **Independence of the dominating measure for squared Hellinger distance.** For probability
measures `P` and `Q` dominated by a σ-finite measure `μ`,
`sqHellinger P Q = ∫ (√(dP/dμ) - √(dQ/dμ))² dμ`. -/
theorem sqHellinger_eq_integral (P Q μ : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [SigmaFinite μ] (hP : P ≪ μ) (hQ : Q ≪ μ) :
    sqHellinger P Q =
      ∫ x, (√(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal) ^ 2 ∂μ := by
  rw [integral_sq_sub_sqrt_rnDeriv P Q μ hP hQ, probReal_univ, probReal_univ, sqHellinger_def]
  ring

/-! ### Range, extreme values, and metric triangle inequality -/

/-- Cauchy–Schwarz bound for the Hellinger affinity of finite measures:
`hellingerAffinity P Q ≤ √(P.real univ * Q.real univ)`. -/
theorem hellingerAffinity_le_sqrt_mul (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity P Q ≤ √(P.real Set.univ * Q.real Set.univ) := by
  have hP : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQ : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  rw [hellingerAffinity_def]
  simp_rw [Real.sqrt_mul ENNReal.toReal_nonneg]
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P + Q) Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => Real.sqrt_nonneg _) (ae_of_all _ fun _ => Real.sqrt_nonneg _)
    (h2.symm ▸ memLp_two_sqrt_rnDeriv P (P + Q))
    (h2.symm ▸ memLp_two_sqrt_rnDeriv Q (P + Q))
  have hpow (R : Measure X) [IsFiniteMeasure R] (hR : R ≪ P + Q) :
      (∫ x, √(R.rnDeriv (P + Q) x).toReal ^ (2 : ℝ) ∂(P + Q)) ^ (1 / (2 : ℝ)) =
        √(R.real Set.univ) := by
    have hsq : ∀ x, √(R.rnDeriv (P + Q) x).toReal ^ (2 : ℝ) = (R.rnDeriv (P + Q) x).toReal :=
      fun x => by rw [Real.rpow_two, Real.sq_sqrt ENNReal.toReal_nonneg]
    simp_rw [hsq, Measure.integral_toReal_rnDeriv hR, ← Real.sqrt_eq_rpow]
  rw [hpow P hP, hpow Q hQ, ← Real.sqrt_mul measureReal_nonneg] at hcs
  exact hcs

/-- The Hellinger affinity of two probability measures is at most `1`. -/
theorem hellingerAffinity_le_one (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : hellingerAffinity P Q ≤ 1 := by
  simpa using hellingerAffinity_le_sqrt_mul P Q

/-- The Hellinger affinity of two probability measures lies in `[0, 1]`. -/
theorem hellingerAffinity_mem_Icc (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : hellingerAffinity P Q ∈ Set.Icc 0 1 :=
  ⟨hellingerAffinity_nonneg P Q, hellingerAffinity_le_one P Q⟩

/-- The squared Hellinger distance of two probability measures is nonnegative. -/
theorem sqHellinger_nonneg (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    0 ≤ sqHellinger P Q := by
  rw [sqHellinger_def]
  linarith [hellingerAffinity_le_one P Q]

/-- The squared Hellinger distance of two probability measures lies in `[0, 2]`. -/
theorem sqHellinger_mem_Icc (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    sqHellinger P Q ∈ Set.Icc 0 2 :=
  ⟨sqHellinger_nonneg P Q, sqHellinger_le_two P Q⟩

/-- For finite measures `P` and `Q`, `hellingerAffinity P Q = 0` if and only if `P` and `Q` are
mutually singular. -/
theorem hellingerAffinity_eq_zero_iff (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    hellingerAffinity P Q = 0 ↔ P ⟂ₘ Q := by
  have hPν : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  rw [hellingerAffinity_def, integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ =>
    Real.sqrt_nonneg _) (integrable_sqrt_rnDeriv_mul P Q (P + Q))]
  constructor
  · intro h
    set s : Set X := {x | P.rnDeriv (P + Q) x = 0}
    have hs : MeasurableSet s :=
      (Measure.measurable_rnDeriv P (P + Q)) (measurableSet_singleton 0)
    refine ⟨s, hs, ?_, ?_⟩
    · nth_rw 1 [← Measure.withDensity_rnDeriv_eq P (P + Q) hPν]
      rw [withDensity_apply _ hs]
      exact setLIntegral_eq_zero hs fun _ hx => hx
    · nth_rw 1 [← Measure.withDensity_rnDeriv_eq Q (P + Q) hQν]
      rw [withDensity_apply _ hs.compl,
        lintegral_eq_zero_iff (Measure.measurable_rnDeriv Q (P + Q))]
      filter_upwards [ae_restrict_of_ae h, ae_restrict_of_ae (Measure.rnDeriv_lt_top P (P + Q)),
        ae_restrict_of_ae (Measure.rnDeriv_lt_top Q (P + Q)), ae_restrict_mem hs.compl] with
        x hx hPtop hQtop hxne
      have hx' : √((P.rnDeriv (P + Q) x).toReal * (Q.rnDeriv (P + Q) x).toReal) = 0 := hx
      rw [Real.sqrt_eq_zero (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)] at hx'
      rcases mul_eq_zero.1 hx' with hP0 | hQ0
      · exact False.elim (hxne ((ENNReal.toReal_eq_zero_iff _).1 hP0 |>.resolve_right hPtop.ne))
      · exact (ENNReal.toReal_eq_zero_iff _).1 hQ0 |>.resolve_right hQtop.ne
  · rintro ⟨s, _, hPs, hQsc⟩
    filter_upwards [Measure.ae_rnDeriv_eq_zero_of_measure_eq_zero (ν := P + Q) hPs,
      Measure.ae_rnDeriv_eq_zero_of_measure_eq_zero (ν := P + Q) hQsc] with x hxP hxQ
    by_cases hxs : x ∈ s
    · simp [hxP hxs]
    · simp [hxQ hxs]

/-- For finite measures `P` and `Q`, `sqHellinger P Q = 2` if and only if `P` and `Q` are mutually
singular. -/
theorem sqHellinger_eq_two_iff (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    sqHellinger P Q = 2 ↔ P ⟂ₘ Q := by
  rw [sqHellinger_def, ← hellingerAffinity_eq_zero_iff P Q]
  constructor <;> intro h <;> linarith

/-- For finite measures `P` and `Q`, the Hellinger affinity attains the arithmetic-mean upper
bound `(P(univ) + Q(univ)) / 2` if and only if `P = Q`. -/
theorem hellingerAffinity_eq_half_add_iff (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] :
    hellingerAffinity P Q = (P.real Set.univ + Q.real Set.univ) / 2 ↔ P = Q := by
  have hPν : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hint : Integrable (fun x => (√(P.rnDeriv (P + Q) x).toReal -
      √(Q.rnDeriv (P + Q) x).toReal) ^ 2) (P + Q) :=
    ((memLp_two_sqrt_rnDeriv P (P + Q)).sub (memLp_two_sqrt_rnDeriv Q (P + Q))).integrable_sq
  have hzero : hellingerAffinity P Q = (P.real Set.univ + Q.real Set.univ) / 2 ↔
      ∫ x, (√(P.rnDeriv (P + Q) x).toReal - √(Q.rnDeriv (P + Q) x).toReal) ^ 2 ∂(P + Q) = 0 := by
    rw [integral_sq_sub_sqrt_rnDeriv P Q (P + Q) hPν hQν]
    constructor <;> intro h <;> linarith
  rw [hzero, integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) hint]
  constructor
  · intro h
    have hrn : P.rnDeriv (P + Q) =ᵐ[P + Q] Q.rnDeriv (P + Q) := by
      filter_upwards [h, Measure.rnDeriv_lt_top P (P + Q), Measure.rnDeriv_lt_top Q (P + Q)] with
        x hx hPtop hQtop
      have hsq : √(P.rnDeriv (P + Q) x).toReal = √(Q.rnDeriv (P + Q) x).toReal :=
        sub_eq_zero.1 (sq_eq_zero_iff.1 hx)
      have htoReal : (P.rnDeriv (P + Q) x).toReal = (Q.rnDeriv (P + Q) x).toReal := by
        rw [← Real.sq_sqrt ENNReal.toReal_nonneg, hsq, Real.sq_sqrt ENNReal.toReal_nonneg]
      exact (ENNReal.toReal_eq_toReal_iff' hPtop.ne hQtop.ne).1 htoReal
    calc P = (P + Q).withDensity (P.rnDeriv (P + Q)) :=
          (Measure.withDensity_rnDeriv_eq P (P + Q) hPν).symm
      _ = (P + Q).withDensity (Q.rnDeriv (P + Q)) := withDensity_congr_ae hrn
      _ = Q := Measure.withDensity_rnDeriv_eq Q (P + Q) hQν
  · rintro rfl
    exact ae_of_all _ fun x => by simp

/-- For probability measures `P` and `Q`, `hellingerAffinity P Q = 1` if and only if `P = Q`. -/
theorem hellingerAffinity_eq_one_iff (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : hellingerAffinity P Q = 1 ↔ P = Q := by
  simpa using hellingerAffinity_eq_half_add_iff P Q

/-- For probability measures `P` and `Q`, `sqHellinger P Q = 0` if and only if `P = Q`. -/
theorem sqHellinger_eq_zero_iff (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : sqHellinger P Q = 0 ↔ P = Q := by
  rw [sqHellinger_def, ← hellingerAffinity_eq_one_iff P Q]
  constructor <;> intro h <;> linarith

/-- **Triangle inequality for the Hellinger distance.** For probability measures `P`, `Q`, and `R`,
`√(sqHellinger P R) ≤ √(sqHellinger P Q) + √(sqHellinger Q R)`. -/
theorem sqrt_sqHellinger_triangle (P Q R : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    √(sqHellinger P R) ≤ √(sqHellinger P Q) + √(sqHellinger Q R) := by
  set μ : Measure X := P + Q + R
  have hPμ : P ≪ μ := (Measure.AbsolutelyContinuous.rfl.add_right Q).add_right R
  have hQμ : Q ≪ μ := (Measure.AbsolutelyContinuous.rfl.add_right' P).add_right R
  have hRμ : R ≪ μ := Measure.AbsolutelyContinuous.rfl.add_right' (P + Q)
  set u : X → ℝ := fun x => √(P.rnDeriv μ x).toReal - √(Q.rnDeriv μ x).toReal
  set v : X → ℝ := fun x => √(Q.rnDeriv μ x).toReal - √(R.rnDeriv μ x).toReal
  have hu : MemLp u 2 μ := (memLp_two_sqrt_rnDeriv P μ).sub (memLp_two_sqrt_rnDeriv Q μ)
  have hv : MemLp v 2 μ := (memLp_two_sqrt_rnDeriv Q μ).sub (memLp_two_sqrt_rnDeriv R μ)
  have hcs : ∫ x, u x * v x ∂μ ≤ √(∫ x, u x ^ 2 ∂μ) * √(∫ x, v x ^ 2 ∂μ) := by
    have h2 : ENNReal.ofReal 2 = 2 := by norm_num
    have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (h2.symm ▸ hu) (h2.symm ▸ hv)
    have hle : ∫ x, u x * v x ∂μ ≤ ∫ x, ‖u x‖ * ‖v x‖ ∂μ := by
      refine integral_mono (hu.integrable_mul hv) (hu.norm.integrable_mul hv.norm) fun x => ?_
      simpa [Real.norm_eq_abs, abs_mul] using le_abs_self (u x * v x)
    refine hle.trans (hholder.trans_eq ?_)
    simp_rw [Real.rpow_two, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow]
  have hPR : sqHellinger P R = ∫ x, u x ^ 2 ∂μ + 2 * ∫ x, u x * v x ∂μ + ∫ x, v x ^ 2 ∂μ := by
    rw [sqHellinger_eq_integral P R μ hPμ hRμ]
    have hsplit : ∀ x, (√(P.rnDeriv μ x).toReal - √(R.rnDeriv μ x).toReal) ^ 2 =
        (u x ^ 2 + 2 * (u x * v x)) + v x ^ 2 := fun x => by simp only [u, v]; ring
    have hu2 : Integrable (fun x => u x ^ 2) μ := hu.integrable_sq
    have huv2 : Integrable (fun x => 2 * (u x * v x)) μ := (hu.integrable_mul hv).const_mul 2
    have hv2 : Integrable (fun x => v x ^ 2) μ := hv.integrable_sq
    have h12 : Integrable (fun x => u x ^ 2 + 2 * (u x * v x)) μ := hu2.add huv2
    simp_rw [hsplit]
    rw [integral_add h12 hv2, integral_add hu2 huv2, integral_const_mul]
  rw [← sqHellinger_eq_integral P Q μ hPμ hQμ, ← sqHellinger_eq_integral Q R μ hQμ hRμ] at hcs hPR
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt (sqHellinger_nonneg P Q), Real.sq_sqrt (sqHellinger_nonneg Q R)]

/-! ### Invariance under measurable embeddings and equivalences -/

/-- The Hellinger affinity is invariant under pushforward by a measurable embedding. -/
theorem hellingerAffinity_map_of_measurableEmbedding (P Q : Measure X) [SigmaFinite P]
    [SigmaFinite Q] {f : X → Y} (hf : MeasurableEmbedding f) :
    hellingerAffinity (P.map f) (Q.map f) = hellingerAffinity P Q := by
  have : SigmaFinite ((P + Q).map f) := hf.sigmaFinite_map
  rw [hellingerAffinity_def, hellingerAffinity_def, ← Measure.map_add _ _ hf.measurable,
    hf.integral_map]
  refine integral_congr_ae ?_
  filter_upwards [hf.rnDeriv_map P (P + Q), hf.rnDeriv_map Q (P + Q)] with x hxP hxQ
  rw [hxP, hxQ]

/-- The Hellinger affinity is invariant under pushforward by a measurable equivalence. -/
theorem hellingerAffinity_map_equiv (P Q : Measure X) [SigmaFinite P] [SigmaFinite Q]
    (e : X ≃ᵐ Y) : hellingerAffinity (P.map e) (Q.map e) = hellingerAffinity P Q :=
  hellingerAffinity_map_of_measurableEmbedding P Q e.measurableEmbedding

/-- The squared Hellinger distance is invariant under pushforward by a measurable equivalence. -/
theorem sqHellinger_map_equiv (P Q : Measure X) [SigmaFinite P] [SigmaFinite Q] (e : X ≃ᵐ Y) :
    sqHellinger (P.map e) (Q.map e) = sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def, hellingerAffinity_map_equiv]

/-! ### Tensorization over product measures -/

/-- **Binary product factorization.** The Hellinger affinity of two binary product measures is the
product of the Hellinger affinities of their factors. -/
theorem hellingerAffinity_prod (P Q : Measure X) (P' Q' : Measure Y) [SigmaFinite P]
    [SigmaFinite Q] [SigmaFinite P'] [SigmaFinite Q'] :
    hellingerAffinity (P.prod P') (Q.prod Q') =
      hellingerAffinity P Q * hellingerAffinity P' Q' := by
  set μ := P + Q
  set μ' := P' + Q'
  have hPμ : P ≪ μ := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQμ : Q ≪ μ := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hP'μ' : P' ≪ μ' := Measure.AbsolutelyContinuous.rfl.add_right Q'
  have hQ'μ' : Q' ≪ μ' := Measure.AbsolutelyContinuous.rfl.add_right' P'
  have hPP' : P.prod P' = (μ.prod μ').withDensity fun z => P.rnDeriv μ z.1 * P'.rnDeriv μ' z.2 := by
    rw [← prod_withDensity (Measure.measurable_rnDeriv P μ)
      (Measure.measurable_rnDeriv P' μ'), Measure.withDensity_rnDeriv_eq P μ hPμ,
      Measure.withDensity_rnDeriv_eq P' μ' hP'μ']
  have hQQ' : Q.prod Q' = (μ.prod μ').withDensity fun z => Q.rnDeriv μ z.1 * Q'.rnDeriv μ' z.2 := by
    rw [← prod_withDensity (Measure.measurable_rnDeriv Q μ)
      (Measure.measurable_rnDeriv Q' μ'), Measure.withDensity_rnDeriv_eq Q μ hQμ,
      Measure.withDensity_rnDeriv_eq Q' μ' hQ'μ']
  rw [hellingerAffinity_eq_integral (P.prod P') (Q.prod Q') (μ.prod μ')
      (.inl (hPP' ▸ withDensity_absolutelyContinuous _ _)),
    hellingerAffinity_def, hellingerAffinity_def, ← integral_prod_mul]
  refine integral_congr_ae ?_
  have hrnP : (P.prod P').rnDeriv (μ.prod μ') =ᵐ[μ.prod μ']
      fun z => P.rnDeriv μ z.1 * P'.rnDeriv μ' z.2 := by
    rw [hPP']
    exact Measure.rnDeriv_withDensity (μ.prod μ') (by fun_prop)
  have hrnQ : (Q.prod Q').rnDeriv (μ.prod μ') =ᵐ[μ.prod μ']
      fun z => Q.rnDeriv μ z.1 * Q'.rnDeriv μ' z.2 := by
    rw [hQQ']
    exact Measure.rnDeriv_withDensity (μ.prod μ') (by fun_prop)
  filter_upwards [hrnP, hrnQ] with z hzP hzQ
  rw [hzP, hzQ, ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hmul : (P.rnDeriv μ z.1).toReal * (P'.rnDeriv μ' z.2).toReal *
      ((Q.rnDeriv μ z.1).toReal * (Q'.rnDeriv μ' z.2).toReal) =
      ((P.rnDeriv μ z.1).toReal * (Q.rnDeriv μ z.1).toReal) *
        ((P'.rnDeriv μ' z.2).toReal * (Q'.rnDeriv μ' z.2).toReal) := by
    ring
  rw [hmul, Real.sqrt_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]

/-- **Finite product factorization.** The Hellinger affinity of two finite product measures is the
product of the coordinatewise Hellinger affinities. -/
theorem hellingerAffinity_pi {ι : Type*} [Fintype ι] {Z : ι → Type*}
    [∀ i, MeasurableSpace (Z i)] (P Q : ∀ i, Measure (Z i))
    [∀ i, SigmaFinite (P i)] [∀ i, SigmaFinite (Q i)] :
    hellingerAffinity (Measure.pi P) (Measure.pi Q) = ∏ i, hellingerAffinity (P i) (Q i) := by
  let μ : ∀ i, Measure (Z i) := fun i => P i + Q i
  have hPμ (i : ι) : P i ≪ μ i := Measure.AbsolutelyContinuous.rfl.add_right (Q i)
  have hQμ (i : ι) : Q i ≪ μ i := Measure.AbsolutelyContinuous.rfl.add_right' (P i)
  have hpiP : Measure.pi P =
      (Measure.pi μ).withDensity fun x => ∏ i, (P i).rnDeriv (μ i) (x i) := by
    have hwd (i : ι) : (μ i).withDensity ((P i).rnDeriv (μ i)) = P i :=
      Measure.withDensity_rnDeriv_eq (P i) (μ i) (hPμ i)
    let (i : ι) : SigmaFinite ((μ i).withDensity ((P i).rnDeriv (μ i))) := by
      rw [hwd]; infer_instance
    nth_rw 1 [← funext hwd]
    exact TauCeti.pi_withDensity μ fun i => Measure.measurable_rnDeriv (P i) (μ i)
  have hpiQ : Measure.pi Q =
      (Measure.pi μ).withDensity fun x => ∏ i, (Q i).rnDeriv (μ i) (x i) := by
    have hwd (i : ι) : (μ i).withDensity ((Q i).rnDeriv (μ i)) = Q i :=
      Measure.withDensity_rnDeriv_eq (Q i) (μ i) (hQμ i)
    let (i : ι) : SigmaFinite ((μ i).withDensity ((Q i).rnDeriv (μ i))) := by
      rw [hwd]; infer_instance
    nth_rw 1 [← funext hwd]
    exact TauCeti.pi_withDensity μ fun i => Measure.measurable_rnDeriv (Q i) (μ i)
  rw [hellingerAffinity_eq_integral (Measure.pi P) (Measure.pi Q) (Measure.pi μ)
      (.inl (Measure.AbsolutelyContinuous.pi hPμ))]
  simp_rw [hellingerAffinity_def]
  rw [← integral_fintype_prod_eq_prod]
  refine integral_congr_ae ?_
  have hrnP : (Measure.pi P).rnDeriv (Measure.pi μ) =ᵐ[Measure.pi μ]
      fun x => ∏ i, (P i).rnDeriv (μ i) (x i) := by
    rw [hpiP]
    exact Measure.rnDeriv_withDensity (Measure.pi μ) (by fun_prop)
  have hrnQ : (Measure.pi Q).rnDeriv (Measure.pi μ) =ᵐ[Measure.pi μ]
      fun x => ∏ i, (Q i).rnDeriv (μ i) (x i) := by
    rw [hpiQ]
    exact Measure.rnDeriv_withDensity (Measure.pi μ) (by fun_prop)
  filter_upwards [hrnP, hrnQ] with x hxP hxQ
  rw [hxP, hxQ, ENNReal.toReal_prod, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  refine (Real.sqrt_eq_iff_eq_sq (Finset.prod_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)).2 ?_
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.sq_sqrt (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]

/-- **Squared Hellinger distance of i.i.d. product measures.** For any finite index type `ι`,
`sqHellinger (Measure.pi fun _ : ι => P) (Measure.pi fun _ : ι => Q)` equals
`2 * (1 - (1 - sqHellinger P Q / 2) ^ Fintype.card ι)`. -/
theorem sqHellinger_pi_const {ι : Type*} [Fintype ι] (P Q : Measure X) [SigmaFinite P]
    [SigmaFinite Q] :
    sqHellinger (Measure.pi fun _ : ι => P) (Measure.pi fun _ : ι => Q) =
      2 * (1 - (1 - sqHellinger P Q / 2) ^ Fintype.card ι) := by
  rw [sqHellinger_def, hellingerAffinity_pi, Finset.prod_const, Finset.card_univ, sqHellinger_def]
  ring

/-- **Infinite product factorization for finitely differing coordinates.** If two families of
probability measures agree outside a finite set `s`, the Hellinger affinity of their infinite
products is the product of the Hellinger affinities over `s`. -/
theorem hellingerAffinity_infinitePi {ι : Type*} {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (P Q : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]
    {s : Finset ι} (hs : ∀ i ∉ s, P i = Q i) :
    hellingerAffinity (Measure.infinitePi P) (Measure.infinitePi Q) =
      ∏ i ∈ s, hellingerAffinity (P i) (Q i) := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd Z (· ∈ s)
  rw [← hellingerAffinity_map_equiv _ _ e,
    (measurePreserving_infinitePi_piEquivPiSubtypeProd P (· ∈ s)).map_eq,
    (measurePreserving_infinitePi_piEquivPiSubtypeProd Q (· ∈ s)).map_eq,
    hellingerAffinity_prod]
  have hcomp : (fun i : {i // i ∉ s} => P i) = fun i : {i // i ∉ s} => Q i :=
    funext fun i => hs i.1 i.2
  rw [hcomp, hellingerAffinity_self, probReal_univ, mul_one,
    Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi, hellingerAffinity_pi]
  exact Finset.prod_coe_sort s fun i => hellingerAffinity (P i) (Q i)

/-! ### Data processing inequality -/

private theorem ae_compProd_rnDeriv_eq_zero_of_rnDeriv_comp_eq_zero
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    ∀ᵐ z ∂((P + Q) ⊗ₘ κ),
      ((κ ∘ₘ P).rnDeriv (κ ∘ₘ (P + Q)) z.2).toReal = 0 → P.rnDeriv (P + Q) z.1 = 0 := by
  set ν := P + Q
  set μ := κ ∘ₘ ν
  set S : Set Y := {y | ((κ ∘ₘ P).rnDeriv μ y).toReal = 0}
  have hS : MeasurableSet S :=
    ((Measure.measurable_rnDeriv (κ ∘ₘ P) μ).ennreal_toReal) (measurableSet_singleton 0)
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hμ : μ = κ ∘ₘ P + κ ∘ₘ Q := Measure.comp_add
  have hκPμ : κ ∘ₘ P ≪ μ := hμ ▸ Measure.AbsolutelyContinuous.rfl.add_right _
  have hκPS : (κ ∘ₘ P) S = 0 := by
    rw [← Measure.withDensity_rnDeriv_eq (κ ∘ₘ P) μ hκPμ, withDensity_apply _ hS,
      lintegral_eq_zero_iff (Measure.measurable_rnDeriv (κ ∘ₘ P) μ)]
    filter_upwards [ae_restrict_of_ae (Measure.rnDeriv_lt_top (κ ∘ₘ P) μ),
      ae_restrict_mem hS] with y hytop hy0
    exact (ENNReal.toReal_eq_zero_iff _).1 hy0 |>.resolve_right hytop.ne
  have hm_ind : Measurable (fun z : X × Y => (Set.univ ×ˢ S).indicator
      (fun w : X × Y => P.rnDeriv ν w.1) z) :=
    ((Measure.measurable_rnDeriv P ν).comp measurable_fst).indicator (MeasurableSet.univ.prod hS)
  have hlint :
      ∫⁻ z, (Set.univ ×ˢ S).indicator (fun w : X × Y => P.rnDeriv ν w.1) z ∂(ν ⊗ₘ κ) = 0 := by
    rw [Measure.lintegral_compProd hm_ind]
    have hinner : ∀ x, ∫⁻ y, (Set.univ ×ˢ S).indicator (fun w : X × Y => P.rnDeriv ν w.1)
        (x, y) ∂κ x = P.rnDeriv ν x * κ x S := fun x => by
      have hind : (fun y => (Set.univ ×ˢ S).indicator (fun w : X × Y => P.rnDeriv ν w.1) (x, y)) =
          S.indicator (fun _ => P.rnDeriv ν x) := by
        ext y; by_cases hy : y ∈ S <;> simp [hy]
      rw [hind, lintegral_indicator hS, setLIntegral_const]
    simp_rw [hinner]
    rw [lintegral_rnDeriv_mul hPν (κ.measurable_coe hS).aemeasurable,
      ← Measure.bind_apply hS κ.aemeasurable]
    exact hκPS
  filter_upwards [(lintegral_eq_zero_iff hm_ind).1 hlint] with z hz hzS
  have hmem : z ∈ Set.univ ×ˢ S := ⟨trivial, hzS⟩
  simpa [Set.indicator_of_mem hmem] using hz

private theorem lintegral_compProd_mul_rnDeriv_eq (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (κ : Kernel X Y) [IsMarkovKernel κ] {f : Y → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z.2 * P.rnDeriv (P + Q) z.1 ∂((P + Q) ⊗ₘ κ) =
      ∫⁻ y, (κ ∘ₘ P).rnDeriv (κ ∘ₘ (P + Q)) y * f y ∂(κ ∘ₘ (P + Q)) := by
  have hPν : P ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hκPμ : κ ∘ₘ P ≪ κ ∘ₘ (P + Q) := by
    rw [Measure.comp_add]
    exact Measure.AbsolutelyContinuous.rfl.add_right _
  have hm : Measurable (fun z : X × Y => f z.2 * P.rnDeriv (P + Q) z.1) :=
    (hf.comp measurable_snd).mul ((Measure.measurable_rnDeriv P (P + Q)).comp measurable_fst)
  rw [Measure.lintegral_compProd hm]
  simp_rw [mul_comm (f _), lintegral_const_mul _ hf]
  rw [lintegral_rnDeriv_mul hPν hf.lintegral_kernel.aemeasurable,
    ← Measure.lintegral_bind κ.aemeasurable hf.aemeasurable,
    ← lintegral_rnDeriv_mul hκPμ hf.aemeasurable]

private theorem lintegral_weighted_rnDeriv_le (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (κ : Kernel X Y) [IsMarkovKernel κ] :
    let μ := κ ∘ₘ (P + Q)
    let p' : Y → ℝ := fun y => ((κ ∘ₘ P).rnDeriv μ y).toReal
    let q' : Y → ℝ := fun y => ((κ ∘ₘ Q).rnDeriv μ y).toReal
    let A : Set Y := {y | 0 < p' y ∧ 0 < q' y}
    ∫⁻ y, ((κ ∘ₘ P).rnDeriv μ y * A.indicator (fun y => ENNReal.ofReal (√(q' y / p' y) / 2)) y +
        (κ ∘ₘ Q).rnDeriv μ y * A.indicator (fun y => ENNReal.ofReal (√(p' y / q' y) / 2)) y) ∂μ ≤
      ENNReal.ofReal (hellingerAffinity (κ ∘ₘ P) (κ ∘ₘ Q)) := by
  intro μ p' q' A
  have hμ : μ = κ ∘ₘ P + κ ∘ₘ Q := Measure.comp_add
  rw [hellingerAffinity_def, ← hμ, ofReal_integral_eq_lintegral_ofReal
    (integrable_sqrt_rnDeriv_mul (κ ∘ₘ P) (κ ∘ₘ Q) μ) (ae_of_all _ fun _ => Real.sqrt_nonneg _)]
  refine lintegral_mono_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top (κ ∘ₘ P) μ, Measure.rnDeriv_lt_top (κ ∘ₘ Q) μ] with
    y hPtop hQtop
  by_cases hy : y ∈ A
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    nth_rw 1 [← ENNReal.ofReal_toReal hPtop.ne, ← ENNReal.ofReal_toReal hQtop.ne]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hsp : 0 < √(p' y) := Real.sqrt_pos.2 hy.1
    have hsq : 0 < √(q' y) := Real.sqrt_pos.2 hy.2
    rw [Real.sqrt_div hy.2.le, Real.sqrt_div hy.1.le, Real.sqrt_mul hy.1.le]
    field_simp [hsp.ne', hsq.ne']
    nlinarith [Real.sq_sqrt hy.1.le, Real.sq_sqrt hy.2.le]
  · simp [Set.indicator_of_notMem hy]

private theorem ae_compProd_ofReal_sqrt_le (P Q : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (κ : Kernel X Y) [IsMarkovKernel κ] :
    let ν := P + Q
    let μ := κ ∘ₘ ν
    let p' : Y → ℝ := fun y => ((κ ∘ₘ P).rnDeriv μ y).toReal
    let q' : Y → ℝ := fun y => ((κ ∘ₘ Q).rnDeriv μ y).toReal
    let A : Set Y := {y | 0 < p' y ∧ 0 < q' y}
    ∀ᵐ z ∂(ν ⊗ₘ κ),
      ENNReal.ofReal (√((P.rnDeriv ν z.1).toReal * (Q.rnDeriv ν z.1).toReal)) ≤
        A.indicator (fun y => ENNReal.ofReal (√(q' y / p' y) / 2)) z.2 * P.rnDeriv ν z.1 +
        A.indicator (fun y => ENNReal.ofReal (√(p' y / q' y) / 2)) z.2 * Q.rnDeriv ν z.1 := by
  intro ν μ p' q' A
  have hfst : (ν ⊗ₘ κ).map Prod.fst = ν := Measure.fst_compProd ν κ
  have htop (R : Measure X) [IsFiniteMeasure R] : ∀ᵐ z ∂(ν ⊗ₘ κ), R.rnDeriv ν z.1 ≠ ∞ :=
    ae_of_ae_map (f := (Prod.fst : X × Y → X)) measurable_fst.aemeasurable (by
      rw [hfst]; exact Measure.rnDeriv_ne_top R ν)
  have hQzero : ∀ᵐ z ∂(ν ⊗ₘ κ), q' z.2 = 0 → Q.rnDeriv ν z.1 = 0 := by
    simpa only [ν, μ, q', add_comm Q P] using
      ae_compProd_rnDeriv_eq_zero_of_rnDeriv_comp_eq_zero Q P κ
  filter_upwards [ae_compProd_rnDeriv_eq_zero_of_rnDeriv_comp_eq_zero P Q κ, hQzero,
    htop P, htop Q] with z hzP hzQ hPne hQne
  by_cases hzA : z.2 ∈ A
  · rw [Set.indicator_of_mem hzA, Set.indicator_of_mem hzA]
    nth_rw 2 [← ENNReal.ofReal_toReal hPne]
    nth_rw 2 [← ENNReal.ofReal_toReal hQne]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsp : 0 < √(p' z.2) := Real.sqrt_pos.2 hzA.1
    have hsq : 0 < √(q' z.2) := Real.sqrt_pos.2 hzA.2
    rw [Real.sqrt_div hzA.2.le, Real.sqrt_div hzA.1.le, Real.sqrt_mul ENNReal.toReal_nonneg]
    have h0 := sq_nonneg (√(q' z.2) * √(P.rnDeriv ν z.1).toReal -
      √(p' z.2) * √(Q.rnDeriv ν z.1).toReal)
    rw [sub_sq, mul_pow, mul_pow, Real.sq_sqrt hzA.2.le, Real.sq_sqrt hzA.1.le,
      Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg] at h0
    field_simp [hsp.ne', hsq.ne']
    rw [Real.sq_sqrt hzA.1.le, Real.sq_sqrt hzA.2.le]
    nlinarith [h0]
  · have h0 : p' z.2 = 0 ∨ q' z.2 = 0 := by
      by_contra h
      push Not at h
      exact hzA ⟨lt_of_le_of_ne ENNReal.toReal_nonneg h.1.symm,
        lt_of_le_of_ne ENNReal.toReal_nonneg h.2.symm⟩
    rcases h0 with hp0 | hq0
    · have hPz : P.rnDeriv ν z.1 = 0 := hzP hp0
      simp [hPz]
    · have hQz : Q.rnDeriv ν z.1 = 0 := hzQ hq0
      simp [hQz]

/-- **Data processing inequality for Hellinger affinity.** Pushing two finite measures forward
through a Markov kernel does not decrease their Hellinger affinity. -/
theorem hellingerAffinity_le_comp (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    hellingerAffinity P Q ≤ hellingerAffinity (κ ∘ₘ P) (κ ∘ₘ Q) := by
  set ν := P + Q
  set μ := κ ∘ₘ ν
  set p' : Y → ℝ := fun y => ((κ ∘ₘ P).rnDeriv μ y).toReal
  set q' : Y → ℝ := fun y => ((κ ∘ₘ Q).rnDeriv μ y).toReal
  set A : Set Y := {y | 0 < p' y ∧ 0 < q' y}
  have hA : MeasurableSet A :=
    ((Measure.measurable_rnDeriv (κ ∘ₘ P) μ).ennreal_toReal measurableSet_Ioi).inter
      ((Measure.measurable_rnDeriv (κ ∘ₘ Q) μ).ennreal_toReal measurableSet_Ioi)
  set f₁ : Y → ℝ≥0∞ := A.indicator fun y => ENNReal.ofReal (√(q' y / p' y) / 2)
  set f₂ : Y → ℝ≥0∞ := A.indicator fun y => ENNReal.ofReal (√(p' y / q' y) / 2)
  have hf₁ : Measurable f₁ := by fun_prop
  have hf₂ : Measurable f₂ := by fun_prop
  have hLHS : ENNReal.ofReal (hellingerAffinity P Q) =
      ∫⁻ z, ENNReal.ofReal (√((P.rnDeriv ν z.1).toReal * (Q.rnDeriv ν z.1).toReal)) ∂(ν ⊗ₘ κ) := by
    rw [Measure.lintegral_compProd (by fun_prop)]
    simp_rw [lintegral_const, measure_univ, mul_one]
    rw [hellingerAffinity_def, ofReal_integral_eq_lintegral_ofReal
      (integrable_sqrt_rnDeriv_mul P Q ν) (ae_of_all _ fun _ => Real.sqrt_nonneg _)]
  have hm1 : Measurable (fun z : X × Y => f₁ z.2 * P.rnDeriv ν z.1) :=
    (hf₁.comp measurable_snd).mul ((Measure.measurable_rnDeriv P ν).comp measurable_fst)
  have hm1' : Measurable (fun y : Y => (κ ∘ₘ P).rnDeriv μ y * f₁ y) :=
    (Measure.measurable_rnDeriv (κ ∘ₘ P) μ).mul hf₁
  have hQterm : ∫⁻ z, f₂ z.2 * Q.rnDeriv ν z.1 ∂(ν ⊗ₘ κ) =
      ∫⁻ y, (κ ∘ₘ Q).rnDeriv μ y * f₂ y ∂μ := by
    simpa only [ν, μ, add_comm Q P] using lintegral_compProd_mul_rnDeriv_eq Q P κ hf₂
  rw [← ENNReal.ofReal_le_ofReal_iff (hellingerAffinity_nonneg _ _), hLHS]
  calc ∫⁻ z, ENNReal.ofReal (√((P.rnDeriv ν z.1).toReal * (Q.rnDeriv ν z.1).toReal)) ∂(ν ⊗ₘ κ)
      ≤ ∫⁻ z, (f₁ z.2 * P.rnDeriv ν z.1 + f₂ z.2 * Q.rnDeriv ν z.1) ∂(ν ⊗ₘ κ) :=
        lintegral_mono_ae (ae_compProd_ofReal_sqrt_le P Q κ)
    _ = ∫⁻ y, ((κ ∘ₘ P).rnDeriv μ y * f₁ y + (κ ∘ₘ Q).rnDeriv μ y * f₂ y) ∂μ := by
        rw [lintegral_add_left hm1, lintegral_compProd_mul_rnDeriv_eq P Q κ hf₁, hQterm,
          ← lintegral_add_left hm1']
    _ ≤ ENNReal.ofReal (hellingerAffinity (κ ∘ₘ P) (κ ∘ₘ Q)) :=
        lintegral_weighted_rnDeriv_le P Q κ

/-- **Data processing inequality for squared Hellinger distance.** Pushing two finite measures
forward through a Markov kernel does not increase their squared Hellinger distance. -/
theorem sqHellinger_comp_le (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    sqHellinger (κ ∘ₘ P) (κ ∘ₘ Q) ≤ sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def]
  linarith [hellingerAffinity_le_comp P Q κ]

/-- **Data processing inequality for almost-everywhere measurable maps.** Pushing two finite
measures forward along a map that is almost everywhere measurable for each does not decrease their
Hellinger affinity. -/
theorem hellingerAffinity_le_map (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {f : X → Y} (hP : AEMeasurable f P) (hQ : AEMeasurable f Q) :
    hellingerAffinity P Q ≤ hellingerAffinity (P.map f) (Q.map f) := by
  have hf : AEMeasurable f (P + Q) := hP.add_measure hQ
  obtain ⟨hPg, hQg⟩ := ae_add_measure_iff.mp hf.ae_eq_mk
  rw [Measure.map_congr hPg, Measure.map_congr hQg]
  simpa [Measure.deterministic_comp_eq_map hf.measurable_mk] using
    hellingerAffinity_le_comp P Q (Kernel.deterministic (hf.mk f) hf.measurable_mk)

/-- **Data processing inequality for squared Hellinger distance under almost-everywhere measurable
maps.** Pushing two finite measures forward along a map that is almost everywhere measurable for
each does not increase their squared Hellinger distance. -/
theorem sqHellinger_map_le (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {f : X → Y} (hP : AEMeasurable f P) (hQ : AEMeasurable f Q) :
    sqHellinger (P.map f) (Q.map f) ≤ sqHellinger P Q := by
  rw [sqHellinger_def, sqHellinger_def]
  linarith [hellingerAffinity_le_map P Q hP hQ]

end TauCeti
