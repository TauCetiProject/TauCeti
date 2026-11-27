/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Probability.GeneratingFunction

/-!
# Elementary theory of the Bernoulli distribution

This file computes the elementary moments and transforms of the real-valued Bernoulli law
`Ber((1 : ℝ), 0, p)`, together with the probability-generating function of the native ℕ-valued law
`Ber((1 : ℕ), 0, p)`. It uses Mathlib's convention that the value `1` has mass `p` and the value
`0` has mass `1 - p`.

## Main results

* `bernoulliMeasure_eq_smul_add_smul`: the law `Ber(x, y, p)` is affine in its parameter `p`;
* `bernoulliMeasure_singleton_left_ne_zero` and `bernoulliMeasure_singleton_right_ne_zero`:
  `Ber(x, y, p)` charges `x` when `0 < p` and `y` when `p < 1`;
* `integral_id_bernoulliMeasure` and `variance_id_bernoulliMeasure` give the mean and variance;
* `integral_of_hasLaw_bernoulliMeasure` and `variance_of_hasLaw_bernoulliMeasure` give the
  corresponding random-variable statements;
* `hasLaw_natCast_bernoulliMeasure` and `hasLaw_cast_eval_bernoulliMeasure` relate native
  Bernoulli variables to their real casts;
* `pgf_bernoulliMeasure` computes the probability-generating function on the native carrier;
* `integrableExpSet_bernoulliMeasure` identifies the exact exponential-integrability domain;
* `mgf_id_bernoulliMeasure` and `cgf_id_bernoulliMeasure` compute the moment- and
  cumulant-generating functions;
* `charFun_bernoulliMeasure` computes the characteristic function.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

/-- A Bernoulli law with a nonzero success value and positive success probability has mass
strictly less than one at zero. -/
theorem bernoulliMeasure_singleton_zero_lt_one {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Zero α] {a : α} {p : unitInterval}
    (ha : a ≠ 0) (hp : 0 < (p : ℝ)) : bernoulliMeasure a 0 p {0} < 1 := by
  rw [bernoulliMeasure_apply_of_notMem_of_mem p (measurableSet_singleton 0)
    (by simpa using ha) rfl]
  exact_mod_cast sub_lt_self (1 : ℝ) hp

/-- The Bernoulli law is affine in its parameter: for weights `s + t = 1`, the law with
parameter `s p + t q` is the mixture `s • Ber(x, y, p) + t • Ber(x, y, q)`. -/
theorem bernoulliMeasure_eq_smul_add_smul {α : Type*} [MeasurableSpace α] (x y : α)
    {p q r : I} {s t : NNReal} (hst : s + t = 1) (hr : (r : ℝ) = s * p + t * q) :
    bernoulliMeasure x y r = s • bernoulliMeasure x y p + t • bernoulliMeasure x y q := by
  have hst' : (s : ℝ) + t = 1 := by exact_mod_cast hst
  have h₁ : unitInterval.toNNReal r = s * unitInterval.toNNReal p + t * unitInterval.toNNReal q :=
    by ext; simp [hr]
  have h₂ : unitInterval.toNNReal (σ r) =
      s * unitInterval.toNNReal (σ p) + t * unitInterval.toNNReal (σ q) := by
    ext
    simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq, hr, NNReal.coe_add,
      NNReal.coe_mul]
    linear_combination -hst'
  simp only [bernoulliMeasure_def, h₁, h₂, add_smul, mul_smul, smul_add]
  abel

/-- The Bernoulli law `Ber(x, y, p)` gives positive mass to `x` when `0 < p`. -/
theorem bernoulliMeasure_singleton_left_ne_zero {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {x y : α} {p : I} (hp : 0 < (p : ℝ)) :
    Ber(x, y, p) {x} ≠ 0 := by
  by_cases h : x = y
  · simp [h]
  · rw [bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton x) rfl
      (by simpa [eq_comm] using h)]
    simpa [← NNReal.coe_eq_zero] using hp.ne'

/-- The Bernoulli law `Ber(x, y, p)` gives positive mass to `y` when `p < 1`. -/
theorem bernoulliMeasure_singleton_right_ne_zero {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {x y : α} {p : I} (hp : (p : ℝ) < 1) :
    Ber(x, y, p) {y} ≠ 0 := by
  by_cases h : y = x
  · simp [h]
  · rw [bernoulliMeasure_apply_of_notMem_of_mem p (measurableSet_singleton y)
      (by simpa [eq_comm] using h) rfl]
    simpa [← NNReal.coe_eq_zero, sub_eq_zero] using hp.ne'

/-- The probability-generating function of a Bernoulli distribution. -/
@[simp]
theorem pgf_bernoulliMeasure (p : unitInterval) (t : ℝ) :
    pgf id Ber((1 : ℕ), 0, p) t = 1 - (p : ℝ) + (p : ℝ) * t := by
  rw [pgf_def, integral_bernoulliMeasure]
  simp only [id_eq, pow_one, smul_eq_mul, pow_zero, mul_one]
  ring

/-- The real cast of a native Bernoulli variable has the corresponding real Bernoulli law. -/
theorem hasLaw_natCast_bernoulliMeasure (p : unitInterval) :
    HasLaw (Nat.cast : ℕ → ℝ) Ber((1 : ℝ), 0, p) Ber((1 : ℕ), 0, p) :=
  ⟨Measurable.of_discrete.aemeasurable, by simp [map_bernoulliMeasure]⟩

/-- A real-cast coordinate under a product of native Bernoulli laws has the corresponding real
Bernoulli law. -/
theorem hasLaw_cast_eval_bernoulliMeasure {ι : Type*} [Fintype ι]
    (p : ι → unitInterval) (i : ι) :
    HasLaw (fun x : ι → ℕ ↦ (x i : ℝ)) Ber((1 : ℝ), 0, p i)
      (Measure.pi fun i : ι ↦ Ber((1 : ℕ), 0, p i)) := by
  simpa [Function.comp_def] using
    (hasLaw_natCast_bernoulliMeasure (p i)).comp
      (measurePreserving_eval (fun i : ι ↦ Ber((1 : ℕ), 0, p i)) i).hasLaw

/-- The mean of the real-valued Bernoulli law with success probability `p` is `p`. -/
@[simp]
theorem integral_id_bernoulliMeasure (p : I) :
    ∫ x, x ∂Ber((1 : ℝ), 0, p) = (p : ℝ) := by
  rw [integral_bernoulliMeasure]
  simp

/-- The variance of the real-valued Bernoulli law with success probability `p` is `p(1-p)`. -/
@[simp]
theorem variance_id_bernoulliMeasure (p : I) :
    Var[id; Ber((1 : ℝ), 0, p)] = (p : ℝ) * (1 - p) := by
  rw [variance_eq_integral (by fun_prop), integral_bernoulliMeasure]
  simp [integral_id_bernoulliMeasure]
  ring_nf

/-- A real-valued Bernoulli random variable with success probability `p` has mean `p`. -/
-- This cannot be a simp lemma because `p` does not occur on the left-hand side.
theorem integral_of_hasLaw_bernoulliMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p : I} (hX : HasLaw X Ber((1 : ℝ), 0, p) P) : P[X] = (p : ℝ) := by
  rw [hX.integral_eq, integral_id_bernoulliMeasure]

/-- A real-valued Bernoulli random variable with success probability `p` has variance `p(1-p)`. -/
-- This cannot be a simp lemma because `p` does not occur on the left-hand side.
theorem variance_of_hasLaw_bernoulliMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p : I} (hX : HasLaw X Ber((1 : ℝ), 0, p) P) :
    Var[X; P] = (p : ℝ) * (1 - p) := by
  rw [hX.variance_eq, variance_id_bernoulliMeasure]

/-- Every real observable of a Bernoulli law has full exponential-integrability domain. -/
@[simp]
theorem integrableExpSet_bernoulliMeasure {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (X : α → ℝ) (a b : α) (p : I) :
    integrableExpSet X Ber(a, b, p) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ integrable_bernoulliMeasure a b p _

/-- The moment-generating function of the real-valued Bernoulli law. -/
@[simp]
theorem mgf_id_bernoulliMeasure (p : I) (t : ℝ) :
    mgf id Ber((1 : ℝ), 0, p) t = 1 - (p : ℝ) + (p : ℝ) * Real.exp t := by
  rw [mgf, integral_bernoulliMeasure]
  simp
  ring_nf

/-- The moment-generating function of a real-valued Bernoulli law is strictly positive. -/
theorem mgf_id_bernoulliMeasure_pos (p : I) (t : ℝ) :
    0 < mgf id Ber((1 : ℝ), 0, p) t := by
  exact mgf_pos (integrable_bernoulliMeasure (1 : ℝ) 0 p fun x => Real.exp (t * id x))

/-- The cumulant-generating function of the real-valued Bernoulli law. -/
@[simp]
theorem cgf_id_bernoulliMeasure (p : I) (t : ℝ) :
    cgf id Ber((1 : ℝ), 0, p) t =
      Real.log (1 - (p : ℝ) + (p : ℝ) * Real.exp t) := by
  rw [cgf, mgf_id_bernoulliMeasure]

/-- The characteristic function of the real-valued Bernoulli law. -/
@[simp]
theorem charFun_bernoulliMeasure (p : I) (t : ℝ) :
    charFun Ber((1 : ℝ), 0, p) t =
      1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * t) := by
  rw [charFun_apply_real, integral_bernoulliMeasure]
  simp
  ring_nf

end Probability

end TauCeti
