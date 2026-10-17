/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Convolution powers and compound Poisson laws

For a measure `μ` on an additive monoid, the convolution power `μ.convolutionPower n` is the
`n`-fold convolution of `μ` with itself, with `μ.convolutionPower 0 = δ₀`. When `μ` is the law of
each of `n` independent random variables, it is the law of their sum.

For a rate `r : ℝ≥0` and a jump law `μ`, the compound Poisson law
`compoundPoissonMeasure r μ = (poissonMeasure r).bind μ.convolutionPower` is the law of
`X₁ + ⋯ + X_N` where `N` is Poisson of rate `r` and the `Xᵢ` have law `μ`, all independent. It is
the countable mixture `∑ₙ Po(r){n} • μ^{∗n}` of the convolution powers.

The main results are that compound Poisson laws with a common jump law convolve by adding their
rates, and that on a finite-dimensional real inner product space the characteristic function is
`exp (r * (φ_μ t - 1))`. The rate-additivity proof works on an arbitrary measurable additive
monoid: the convolution powers satisfy `μ^{∗(m + n)} = μ^{∗m} ∗ μ^{∗n}`, so mixing them commutes
with convolution of the mixing laws on `ℕ`, and the Poisson laws on `ℕ` add their rates.

## Main definitions

* `MeasureTheory.Measure.convolutionPower` — the convolution powers of a measure;
* `TauCeti.Probability.compoundPoissonMeasure` — the compound Poisson law of rate `r` and jump
  law `μ`.

## Main results

* `MeasureTheory.Measure.convolutionPower_add` — `μ^{∗(m + n)} = μ^{∗m} ∗ μ^{∗n}`;
* `ProbabilityTheory.iIndepFun.hasLaw_sum_range_convolutionPower` — a sum of `n` independent
  variables of law `μ` has law `μ^{∗n}`;
* `MeasureTheory.Measure.charFun_convolutionPower` — the characteristic function of `μ^{∗n}` is
  the `n`-th power of that of `μ`;
* `TauCeti.Probability.compoundPoissonMeasure_eq_sum` — the compound Poisson law as a
  Poisson-weighted sum of convolution powers;
* `TauCeti.Probability.compoundPoissonMeasure_zero_left`,
  `TauCeti.Probability.compoundPoissonMeasure_dirac_zero` — rate zero and zero jumps give `δ₀`;
* `TauCeti.Probability.compoundPoissonMeasure_conv_compoundPoissonMeasure` — rates add under
  convolution at a fixed jump law;
* `TauCeti.Probability.charFun_compoundPoissonMeasure` — the characteristic function
  `exp (r * (φ_μ t - 1))`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed.,
  Wiley, 1968, §XII.2.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

namespace MeasureTheory.Measure

variable {E : Type*} [AddMonoid E] [MeasurableSpace E] {μ : Measure E}

/-- The `n`-th convolution power of a measure `μ` on an additive monoid: the Dirac mass at `0`
for `n = 0`, and `μ.convolutionPower n ∗ μ` for `n + 1`. For a probability measure `μ` it is the
law of a sum of `n` independent random variables of law `μ`. -/
noncomputable def convolutionPower (μ : Measure E) : ℕ → Measure E
  | 0 => dirac 0
  | n + 1 => convolutionPower μ n ∗ μ

/-- The zeroth convolution power is the Dirac mass at `0`. -/
@[simp]
theorem convolutionPower_zero (μ : Measure E) : μ.convolutionPower 0 = dirac 0 := by
  rw [convolutionPower]

/-- The defining recursion of convolution powers: `μ^{∗(n + 1)} = μ^{∗n} ∗ μ`. -/
theorem convolutionPower_succ (μ : Measure E) (n : ℕ) :
    μ.convolutionPower (n + 1) = μ.convolutionPower n ∗ μ := by
  rw [convolutionPower]

instance [SFinite μ] (n : ℕ) : SFinite (μ.convolutionPower n) := by
  induction n with
  | zero => rw [convolutionPower_zero]; infer_instance
  | succ n ih => rw [convolutionPower_succ]; infer_instance

instance [IsFiniteMeasure μ] (n : ℕ) : IsFiniteMeasure (μ.convolutionPower n) := by
  induction n with
  | zero => rw [convolutionPower_zero]; infer_instance
  | succ n ih => rw [convolutionPower_succ]; infer_instance

instance [IsProbabilityMeasure μ] (n : ℕ) : IsProbabilityMeasure (μ.convolutionPower n) := by
  induction n with
  | zero => rw [convolutionPower_zero]; infer_instance
  | succ n ih => rw [convolutionPower_succ]; infer_instance

variable [MeasurableAdd₂ E]

/-- The first convolution power of an s-finite measure is the measure itself. -/
@[simp]
theorem convolutionPower_one (μ : Measure E) [SFinite μ] : μ.convolutionPower 1 = μ := by
  rw [convolutionPower_succ, convolutionPower_zero, dirac_zero_conv]

/-- Convolution powers add their exponents. -/
theorem convolutionPower_add (μ : Measure E) [SFinite μ] (m n : ℕ) :
    μ.convolutionPower (m + n) = μ.convolutionPower m ∗ μ.convolutionPower n := by
  induction n with
  | zero => rw [Nat.add_zero, convolutionPower_zero, conv_dirac_zero]
  | succ n ih => rw [← Nat.add_assoc, convolutionPower_succ, ih, convolutionPower_succ, conv_assoc]

/-- Convolution powers also satisfy the recursion `μ^{∗(n + 1)} = μ ∗ μ^{∗n}`. -/
theorem convolutionPower_succ' (μ : Measure E) [SFinite μ] (n : ℕ) :
    μ.convolutionPower (n + 1) = μ ∗ μ.convolutionPower n := by
  rw [Nat.add_comm, convolutionPower_add, convolutionPower_one]

/-- Every convolution power of the Dirac mass at `0` is the Dirac mass at `0`. -/
@[simp]
theorem convolutionPower_dirac_zero (n : ℕ) : (dirac (0 : E)).convolutionPower n = dirac 0 := by
  induction n with
  | zero => rw [convolutionPower_zero]
  | succ n ih => rw [convolutionPower_succ, ih, conv_dirac_zero]

/-- Pushing forward along a measurable additive monoid homomorphism commutes with convolution
powers. -/
theorem map_convolutionPower {F : Type*} [AddMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    (μ : Measure E) [SFinite μ] (f : E →+ F) (hf : Measurable f) (n : ℕ) :
    (μ.convolutionPower n).map f = (μ.map f).convolutionPower n := by
  induction n with
  | zero => rw [convolutionPower_zero, convolutionPower_zero, map_dirac' hf, map_zero]
  | succ n ih => rw [convolutionPower_succ, convolutionPower_succ, map_conv_addMonoidHom _ hf, ih]

/-- Mixing a family of measures indexed by `ℕ` that turns addition into convolution commutes
with convolution: `(ρ.bind K) ∗ (σ.bind K) = (ρ ∗ σ).bind K` when
`K (m + n) = K m ∗ K n`. -/
theorem bind_conv_bind {K : ℕ → Measure E} [∀ n, SFinite (K n)]
    (hK : ∀ m n, K (m + n) = K m ∗ K n) (ρ σ : Measure ℕ) [SFinite σ] [SFinite (σ.bind K)] :
    ρ.bind K ∗ σ.bind K = (ρ ∗ σ).bind K := by
  have hKm : Measurable K := measurable_of_countable K
  refine ext_of_lintegral _ fun f hf => ?_
  have hfx (x : E) : Measurable fun y => f (x + y) := hf.comp (measurable_const_add x)
  have hint : Measurable fun x => ∫⁻ y, f (x + y) ∂σ.bind K :=
    (hf.comp measurable_add).lintegral_prod_right'
  rw [lintegral_conv hf, lintegral_bind hKm.aemeasurable hint.aemeasurable,
    lintegral_bind hKm.aemeasurable hf.aemeasurable, lintegral_conv (by fun_prop)]
  refine lintegral_congr fun m => ?_
  calc ∫⁻ x, ∫⁻ y, f (x + y) ∂σ.bind K ∂K m
      = ∫⁻ x, ∫⁻ n, ∫⁻ y, f (x + y) ∂K n ∂σ ∂K m := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_bind hKm.aemeasurable (hfx x).aemeasurable]
    _ = ∫⁻ n, ∫⁻ x, ∫⁻ y, f (x + y) ∂K n ∂K m ∂σ := by
        refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
        exact measurable_from_prod_countable_left fun n =>
          (hf.comp measurable_add).lintegral_prod_right' (ν := K n)
    _ = ∫⁻ n, ∫⁻ z, f z ∂K (m + n) ∂σ := by
        refine lintegral_congr fun n => ?_
        rw [hK, lintegral_conv hf]

end MeasureTheory.Measure

namespace ProbabilityTheory.iIndepFun

variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- A sum of `n` independent random variables, each with law `μ`, has law `μ^{∗n}`. -/
theorem hasLaw_sum_range_convolutionPower {μ : Measure E} {X : ℕ → Ω → E}
    (hX : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P) (n : ℕ) :
    HasLaw (∑ i ∈ Finset.range n, X i) (μ.convolutionPower n) P := by
  have : IsProbabilityMeasure μ := (hlaw 0).isProbabilityMeasure_iff.mp inferInstance
  induction n with
  | zero =>
    refine ⟨aemeasurable_const, ?_⟩
    rw [Finset.sum_range_zero, Measure.convolutionPower_zero, Pi.zero_def, Measure.map_const,
      measure_univ, one_smul]
  | succ n ih =>
    rw [Finset.sum_range_succ, Measure.convolutionPower_succ]
    exact IndepFun.hasLaw_add ih (hlaw n) <|
      hX.indepFun_finsetSum_of_notMem₀ (fun i => (hlaw i).aemeasurable) Finset.notMem_range_self

end ProbabilityTheory.iIndepFun

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The characteristic function of the `n`-th convolution power of a finite measure is the
`n`-th power of its characteristic function. -/
@[simp]
theorem charFun_convolutionPower (μ : Measure E) [IsFiniteMeasure μ] (n : ℕ) (t : E) :
    charFun (μ.convolutionPower n) t = charFun μ t ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [convolutionPower_succ, charFun_conv, ih, pow_succ]

end MeasureTheory.Measure

namespace TauCeti.Probability

section AddMonoid

variable {E : Type*} [AddMonoid E] [MeasurableSpace E]

/-- The compound Poisson law with rate `r` and jump law `μ`: the law of `X₁ + ⋯ + X_N` for `N`
Poisson of rate `r` and `Xᵢ` of law `μ`, all independent, defined as the mixture of the
convolution powers `μ^{∗n}` by the Poisson law of rate `r`. -/
noncomputable def compoundPoissonMeasure (r : ℝ≥0) (μ : Measure E) : Measure E :=
  (poissonMeasure r).bind μ.convolutionPower

/-- The compound Poisson law is the Poisson-weighted sum `∑ₙ Po(r){n} • μ^{∗n}` of the
convolution powers of its jump law. -/
theorem compoundPoissonMeasure_eq_sum (r : ℝ≥0) (μ : Measure E) :
    compoundPoissonMeasure r μ =
      Measure.sum fun n => poissonMeasure r {n} • μ.convolutionPower n := by
  have hK : Measurable μ.convolutionPower := measurable_of_countable _
  rw [compoundPoissonMeasure]
  conv_lhs => rw [← Measure.sum_smul_dirac (poissonMeasure r)]
  rw [Measure.bind_sum _ _ hK.aemeasurable]
  refine congrArg Measure.sum (funext fun n => ?_)
  rw [Measure.bind_smul _ _ hK.aemeasurable, Measure.dirac_bind hK]

/-- The mass of a measurable set under a compound Poisson law is the Poisson-weighted series of
its masses under the convolution powers of the jump law. -/
theorem compoundPoissonMeasure_apply (r : ℝ≥0) (μ : Measure E) {s : Set E}
    (hs : MeasurableSet s) :
    compoundPoissonMeasure r μ s = ∑' n, poissonMeasure r {n} * μ.convolutionPower n s := by
  simp [compoundPoissonMeasure_eq_sum, Measure.sum_apply _ hs]

instance (r : ℝ≥0) (μ : Measure E) [SFinite μ] : SFinite (compoundPoissonMeasure r μ) := by
  rw [compoundPoissonMeasure_eq_sum]
  infer_instance

instance (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (compoundPoissonMeasure r μ) :=
  isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable (ae_of_all _ inferInstance)

/-- The compound Poisson law of rate zero is the Dirac mass at `0`. -/
@[simp]
theorem compoundPoissonMeasure_zero_left (μ : Measure E) :
    compoundPoissonMeasure 0 μ = Measure.dirac 0 := by
  rw [compoundPoissonMeasure, poissonMeasure_zero, Measure.dirac_bind (measurable_of_countable _),
    Measure.convolutionPower_zero]

variable [MeasurableAdd₂ E]

/-- The compound Poisson law with jumps equal to `0` is the Dirac mass at `0`. -/
@[simp]
theorem compoundPoissonMeasure_dirac_zero (r : ℝ≥0) :
    compoundPoissonMeasure r (Measure.dirac (0 : E)) = Measure.dirac 0 := by
  rw [compoundPoissonMeasure, funext (Measure.convolutionPower_dirac_zero (E := E)),
    Measure.bind_const, measure_univ, one_smul]

/-- Compound Poisson laws with the same jump law convolve by adding their rates. -/
theorem compoundPoissonMeasure_conv_compoundPoissonMeasure (r s : ℝ≥0) (μ : Measure E)
    [SFinite μ] :
    compoundPoissonMeasure r μ ∗ compoundPoissonMeasure s μ = compoundPoissonMeasure (r + s) μ := by
  have : SFinite ((poissonMeasure s).bind μ.convolutionPower) :=
    inferInstanceAs (SFinite (compoundPoissonMeasure s μ))
  simp only [compoundPoissonMeasure]
  rw [Measure.bind_conv_bind (Measure.convolutionPower_add μ), poissonMeasure_conv_poissonMeasure]

/-- Pushing a compound Poisson law forward along a measurable additive monoid homomorphism
pushes its jump law forward and keeps its rate. -/
theorem map_compoundPoissonMeasure {F : Type*} [AddMonoid F] [MeasurableSpace F]
    [MeasurableAdd₂ F] (r : ℝ≥0) (μ : Measure E) [SFinite μ] (f : E →+ F) (hf : Measurable f) :
    (compoundPoissonMeasure r μ).map f = compoundPoissonMeasure r (μ.map f) := by
  rw [compoundPoissonMeasure, compoundPoissonMeasure,
    Measure.map_bind (measurable_of_countable _).aemeasurable hf.aemeasurable]
  exact congrArg _ (funext (Measure.map_convolutionPower μ f hf))

end AddMonoid

/-- The sum of two independent random variables with compound Poisson laws of rates `r` and `s`
and a common jump law `μ` is compound Poisson with rate `r + s` and jump law `μ`. -/
theorem _root_.ProbabilityTheory.IndepFun.hasLaw_add_compoundPoissonMeasure {Ω E : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] [AddMonoid E] [MeasurableSpace E]
    [MeasurableAdd₂ E] {r s : ℝ≥0} {μ : Measure E} [SFinite μ] {X Y : Ω → E}
    (hXY : IndepFun X Y P) (hX : HasLaw X (compoundPoissonMeasure r μ) P)
    (hY : HasLaw Y (compoundPoissonMeasure s μ) P) :
    HasLaw (X + Y) (compoundPoissonMeasure (r + s) μ) P := by
  have := hX.isFiniteMeasure_iff.mp inferInstance
  have := hY.isFiniteMeasure_iff.mp inferInstance
  rw [← compoundPoissonMeasure_conv_compoundPoissonMeasure]
  exact hXY.hasLaw_add hX hY

/-- The characteristic function of the compound Poisson law with rate `r` and jump law `μ` is
`t ↦ exp (r * (φ_μ t - 1))`, where `φ_μ` is the characteristic function of `μ`. -/
theorem charFun_compoundPoissonMeasure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (r : ℝ≥0) (μ : Measure E)
    [IsProbabilityMeasure μ] (t : E) :
    charFun (compoundPoissonMeasure r μ) t = Complex.exp (r * (charFun μ t - 1)) := by
  have hint : Integrable (fun x => Complex.exp (inner ℝ x t * Complex.I))
      (compoundPoissonMeasure r μ) :=
    (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp)
  rw [charFun_apply]
  rw [compoundPoissonMeasure_eq_sum] at hint ⊢
  rw [integral_sum_measure hint]
  simp_rw [integral_smul_measure, ← charFun_apply, Measure.charFun_convolutionPower,
    ← measureReal_def, poissonMeasure_real_singleton]
  calc ∑' n, (Real.exp (-r) * r ^ n / n ! : ℝ) • charFun μ t ^ n
  _ = ∑' n, (Real.exp (-r) : ℂ) * ((r * charFun μ t) ^ n / n !) := by
      congr with n
      rw [Complex.real_smul]
      push_cast
      ring
  _ = (Real.exp (-r) : ℂ) * Complex.exp (r * charFun μ t) := by
      rw [tsum_mul_left, (NormedSpace.expSeries_div_hasSum_exp (r * charFun μ t)).tsum_eq,
        Complex.exp_eq_exp_ℂ]
  _ = Complex.exp (r * (charFun μ t - 1)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      push_cast
      ring_nf

end TauCeti.Probability
