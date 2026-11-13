/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.Pi
public import TauCeti.Probability.Density
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The finite beta gas

For a potential `V : ℝ → ℝ`, the weight is
`exp (-(β n / 2) ∑ V(xᵢ)) ∏_{i<j} |xᵢ - xⱼ|^β`. The Gaussian beta gas is the specialization
`V x = x² / 2`, giving the convention `exp (-(β n / 4) ∑ xᵢ²) ∏_{i<j} |xᵢ - xⱼ|^β`.

The partition function is the integral of the weight over `Fin n → ℝ`; the real density divides
the weight by this integral, and the measure is volume with this density. If the weight is not
integrable, the Bochner integral is zero, so both the density and measure are zero.
The factor `β n / 2` corresponds to the `1 / √n` eigenvalue scaling for invariant ensembles
and to the `n²` speed of empirical-measure large deviations.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), (2.6.1)–(2.6.2). Their potential is `β V / 2` in this
  convention; the Gaussian case takes `V x = x² / 2`.
-/

public section
noncomputable section

open MeasureTheory Real

namespace TauCeti.Probability

/-- Distinct particle indices represented in increasing order. -/
def betaGasPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- Membership in the ordered-pair index set. -/
@[simp] theorem mem_betaGasPairs (n : ℕ) (p : Fin n × Fin n) :
    p ∈ betaGasPairs n ↔ p.1 < p.2 := by
  simp [betaGasPairs]

/-- The unnormalized beta-gas weight for a potential `V`. -/
def betaGasWeight (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  exp (-(β * (n : ℝ) / 2) * ∑ i, V (x i)) *
    ∏ p ∈ betaGasPairs n, |x p.1 - x p.2| ^ β

/-- The defining formula for the beta-gas weight. -/
theorem betaGasWeight_def (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (x : Fin n → ℝ) :
    betaGasWeight n β V x =
      exp (-(β * (n : ℝ) / 2) * ∑ i, V (x i)) *
        ∏ p ∈ betaGasPairs n,
          |x p.1 - x p.2| ^ β := (rfl)

/-- The beta-gas weight is nonnegative. -/
theorem betaGasWeight_nonneg (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (x : Fin n → ℝ) : 0 ≤ betaGasWeight n β V x := by
  unfold betaGasWeight
  positivity

/-- The beta-gas weight is positive at configurations with distinct coordinates. -/
theorem betaGasWeight_pos (n : ℕ) (β : ℝ) (V : ℝ → ℝ) {x : Fin n → ℝ}
    (hx : Function.Injective x) : 0 < betaGasWeight n β V x := by
  rw [betaGasWeight_def]
  apply mul_pos (exp_pos _)
  apply Finset.prod_pos
  intro z hz
  have hne : z.1 ≠ z.2 := ne_of_lt ((mem_betaGasPairs n z).mp hz)
  exact Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr (fun h => hne (hx h)))) β

/-- A continuous potential gives a continuous weight when `β` is nonnegative. -/
@[fun_prop]
theorem continuous_betaGasWeight (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) {V : ℝ → ℝ}
    (hV : Continuous V) : Continuous (betaGasWeight n β V) := by
  unfold betaGasWeight
  fun_prop

/-- A measurable potential gives a measurable weight for every inverse temperature. -/
@[fun_prop]
theorem measurable_betaGasWeight (n : ℕ) (β : ℝ) {V : ℝ → ℝ}
    (hV : Measurable V) : Measurable (betaGasWeight n β V) := by
  unfold betaGasWeight
  fun_prop

/-- The beta-gas partition function; the Bochner integral is zero when not integrable. -/
def betaGasPartitionFunction (n : ℕ) (β : ℝ) (V : ℝ → ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, betaGasWeight n β V x
    ∂(volume : Measure (Fin n → ℝ))

/-- The defining integral for the beta-gas partition function. -/
theorem betaGasPartitionFunction_def (n : ℕ) (β : ℝ) (V : ℝ → ℝ) :
    betaGasPartitionFunction n β V =
      ∫ x : Fin n → ℝ, betaGasWeight n β V x
        ∂(volume : Measure (Fin n → ℝ)) := (rfl)

/-- The beta-gas partition function is nonnegative. -/
theorem betaGasPartitionFunction_nonneg (n : ℕ) (β : ℝ) (V : ℝ → ℝ) :
    0 ≤ betaGasPartitionFunction n β V :=
  integral_nonneg (betaGasWeight_nonneg n β V)

/-- Every integrable beta-gas weight has positive partition function. -/
theorem betaGasPartitionFunction_pos_of_integrable (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hint : Integrable (betaGasWeight n β V)
      (volume : Measure (Fin n → ℝ))) :
    0 < betaGasPartitionFunction n β V := by
  let x₀ : Fin n → ℝ := fun i => (i : ℝ)
  have hball : Metric.ball x₀ (1 / 2 : ℝ) ⊆ Function.support (betaGasWeight n β V) := by
    intro x hx
    have hdist : ∀ i, |x i - (i.val : ℝ)| < 1 / 2 := by
      have h := (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp hx
      intro i
      simpa [Real.dist_eq, x₀] using h i
    change betaGasWeight n β V x ≠ 0
    apply (betaGasWeight_pos n β V ?_).ne'
    intro i j hij
    apply Fin.ext
    by_contra hne
    have hi := abs_lt.mp (hdist i)
    have hj := abs_lt.mp (hdist j)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hcast : (i.val : ℝ) + 1 ≤ j.val := by
        exact_mod_cast (show i.val + 1 ≤ j.val by omega)
      linarith
    · have hcast : (j.val : ℝ) + 1 ≤ i.val := by
        exact_mod_cast (show j.val + 1 ≤ i.val by omega)
      linarith
  rw [betaGasPartitionFunction_def]
  apply (integral_pos_iff_support_of_nonneg (betaGasWeight_nonneg n β V) hint).mpr
  exact lt_of_lt_of_le
    ((volume : Measure (Fin n → ℝ)).measure_pos_of_mem_nhds
      (Metric.ball_mem_nhds x₀ (by norm_num))) (measure_mono hball)

/-- The beta-gas weight divided by its partition function. It integrates to one when the weight
is integrable and the partition function is positive. -/
def betaGasPDFReal (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  betaGasWeight n β V x / betaGasPartitionFunction n β V

/-- The defining formula for the beta-gas density. -/
theorem betaGasPDFReal_def (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (x : Fin n → ℝ) :
    betaGasPDFReal n β V x = betaGasWeight n β V x / betaGasPartitionFunction n β V := (rfl)

/-- A measurable potential gives a measurable normalized density. -/
@[fun_prop]
theorem measurable_betaGasPDFReal (n : ℕ) (β : ℝ) {V : ℝ → ℝ}
    (hV : Measurable V) : Measurable (betaGasPDFReal n β V) := by
  have hdens : betaGasPDFReal n β V =
      fun x => betaGasWeight n β V x / betaGasPartitionFunction n β V := by
    funext x
    exact betaGasPDFReal_def n β V x
  rw [hdens]
  exact (measurable_betaGasWeight n β hV).div_const _

/-- A continuous potential gives a continuous density when `β` is nonnegative. -/
@[fun_prop]
theorem continuous_betaGasPDFReal (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) {V : ℝ → ℝ}
    (hV : Continuous V) : Continuous (betaGasPDFReal n β V) := by
  have hdens : betaGasPDFReal n β V =
      fun x => betaGasWeight n β V x / betaGasPartitionFunction n β V := by
    funext x
    exact betaGasPDFReal_def n β V x
  rw [hdens]
  exact (continuous_betaGasWeight n hβ hV).div_const _

/-- The beta-gas density is nonnegative. -/
theorem betaGasPDFReal_nonneg (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (x : Fin n → ℝ) : 0 ≤ betaGasPDFReal n β V x :=
  div_nonneg (betaGasWeight_nonneg n β V x) (betaGasPartitionFunction_nonneg n β V)

/-- The normalized density is integrable, including when a nonintegrable
weight makes its partition function and density zero. -/
theorem integrable_betaGasPDFReal (n : ℕ) (β : ℝ) (V : ℝ → ℝ) :
    Integrable (betaGasPDFReal n β V)
      (volume : Measure (Fin n → ℝ)) := by
  by_cases hint : Integrable (betaGasWeight n β V)
      (volume : Measure (Fin n → ℝ))
  · exact hint.div_const _
  · have hzero : betaGasPartitionFunction n β V = 0 := by
      rw [betaGasPartitionFunction_def, integral_undef hint]
    have hdensity : betaGasPDFReal n β V = 0 := by
      funext x
      simp [betaGasPDFReal_def, hzero]
    rw [hdensity]
    exact integrable_zero _ _ _

/-- A positive partition function normalizes the integral of the density. -/
theorem integral_betaGasPDFReal_eq_one (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hpos : 0 < betaGasPartitionFunction n β V) :
    (∫ x, betaGasPDFReal n β V x
      ∂(volume : Measure (Fin n → ℝ))) = 1 := by
  simp only [betaGasPDFReal, integral_div, ← betaGasPartitionFunction_def]
  exact div_self hpos.ne'

/-- The beta-gas measure with the nonnegative density. It is a probability measure when the weight
is integrable and the partition function is positive. -/
def betaGasMeasure (n : ℕ) (β : ℝ) (V : ℝ → ℝ) : Measure (Fin n → ℝ) :=
  (volume : Measure (Fin n → ℝ)).withDensity fun x =>
    ENNReal.ofReal (betaGasPDFReal n β V x)

/-- The beta-gas measure as a with-density measure. -/
theorem betaGasMeasure_def (n : ℕ) (β : ℝ) (V : ℝ → ℝ) :
    betaGasMeasure n β V =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (betaGasPDFReal n β V x)) := (rfl)

/-- The mass of a set is the integral of the beta-gas density over it. -/
theorem betaGasMeasure_apply (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (s : Set (Fin n → ℝ)) :
    betaGasMeasure n β V s =
      ENNReal.ofReal (∫ x in s, betaGasPDFReal n β V x
        ∂(volume : Measure (Fin n → ℝ))) := by
  have hdens := integrable_betaGasPDFReal n β V
  rw [betaGasMeasure, withDensity_apply']
  exact (ofReal_integral_eq_lintegral_ofReal hdens.restrict
    (ae_of_all _ (betaGasPDFReal_nonneg n β V))).symm

/-- Integrals against the beta-gas measure are weighted integrals against product volume. -/
theorem integral_betaGasMeasure_eq_integral_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (f : (Fin n → ℝ) → E) :
    ∫ x, f x ∂betaGasMeasure n β V =
      ∫ x, betaGasPDFReal n β V x • f x
        ∂(volume : Measure (Fin n → ℝ)) := by
  rw [betaGasMeasure]
  exact integral_withDensity_ofReal (integrable_betaGasPDFReal n β V).1.aemeasurable
    (ae_of_all _ (betaGasPDFReal_nonneg n β V)) f

/-- The beta-gas measure is finite, including for nonintegrable weights. -/
instance (n : ℕ) (β : ℝ) (V : ℝ → ℝ) :
    IsFiniteMeasure (betaGasMeasure n β V) := by
  constructor
  rw [betaGasMeasure_apply n β V Set.univ]
  exact ENNReal.ofReal_lt_top

/-- An integrable weight makes the beta-gas measure a probability. -/
theorem isProbabilityMeasure_betaGasMeasure (n : ℕ) (β : ℝ) (V : ℝ → ℝ)
    (hint : Integrable (betaGasWeight n β V) (volume : Measure (Fin n → ℝ))) :
    IsProbabilityMeasure (betaGasMeasure n β V) := by
  refine ⟨?_⟩
  rw [betaGasMeasure_apply n β V Set.univ, Measure.restrict_univ,
    integral_betaGasPDFReal_eq_one n β V
      (betaGasPartitionFunction_pos_of_integrable n β V hint), ENNReal.ofReal_one]

/-- Integrability against the beta-gas measure is integrability of the
density-weighted function against volume. -/
theorem integrable_betaGasMeasure_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (β : ℝ) (V : ℝ → ℝ) (f : (Fin n → ℝ) → E) :
    Integrable f (betaGasMeasure n β V) ↔
      Integrable (fun x => betaGasPDFReal n β V x • f x)
        (volume : Measure (Fin n → ℝ)) := by
  rw [betaGasMeasure]
  exact integrable_withDensity_ofReal_iff (integrable_betaGasPDFReal n β V).1.aemeasurable
    (ae_of_all _ (betaGasPDFReal_nonneg n β V))

/-- The unnormalized Gaussian beta-gas weight with quadratic potential `V x = x² / 2`. -/
def gaussianBetaGasWeight (n : ℕ) (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  betaGasWeight n β (fun t => t ^ 2 / 2) x

/-- The Gaussian weight is the beta-gas weight for the quadratic potential. -/
theorem gaussianBetaGasWeight_eq_betaGasWeight (n : ℕ) (β : ℝ) :
    gaussianBetaGasWeight n β = betaGasWeight n β (fun t => t ^ 2 / 2) := (rfl)

/-- The Gaussian beta-gas weight as an exponential times a product of pairwise distances. -/
theorem gaussianBetaGasWeight_eq_exp_mul_prod (n : ℕ) (β : ℝ) (x : Fin n → ℝ) :
    gaussianBetaGasWeight n β x =
      exp (-(β * (n : ℝ) / 4) * ∑ i, x i ^ 2) *
        ∏ p ∈ betaGasPairs n,
          |x p.1 - x p.2| ^ β := by
  unfold gaussianBetaGasWeight betaGasWeight
  rw [← Finset.sum_div]
  congr 2
  ring

/-- The weight is continuous for nonnegative inverse temperature. -/
@[fun_prop]
theorem continuous_gaussianBetaGasWeight (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    Continuous (gaussianBetaGasWeight n β) := by
  exact continuous_betaGasWeight n hβ (V := fun t => t ^ 2 / 2) (by fun_prop)

/-- The Gaussian weight is measurable for every inverse temperature. -/
@[fun_prop]
theorem measurable_gaussianBetaGasWeight (n : ℕ) (β : ℝ) :
    Measurable (gaussianBetaGasWeight n β) :=
  measurable_betaGasWeight n β (V := fun t => t ^ 2 / 2) (by fun_prop)

/-- The Gaussian beta-gas weight is nonnegative. -/
theorem gaussianBetaGasWeight_nonneg (n : ℕ) (β : ℝ)
    (x : Fin n → ℝ) : 0 ≤ gaussianBetaGasWeight n β x := by
  exact betaGasWeight_nonneg n β _ x

/-- The Gaussian beta-gas weight is positive at configurations with distinct coordinates. -/
theorem gaussianBetaGasWeight_pos (n : ℕ) (β : ℝ) {x : Fin n → ℝ}
    (hx : Function.Injective x) : 0 < gaussianBetaGasWeight n β x :=
  betaGasWeight_pos n β _ hx

/-- The partition function, finite and strictly positive for `0 < β`. Outside the integrable
case, the Bochner integral is defined to be zero. -/
def gaussianBetaGasPartitionFunction (n : ℕ) (β : ℝ) : ℝ :=
  betaGasPartitionFunction n β (fun t => t ^ 2 / 2)

/-- The Gaussian partition function is the quadratic-potential specialization. -/
theorem gaussianBetaGasPartitionFunction_eq_betaGasPartitionFunction (n : ℕ) (β : ℝ) :
    gaussianBetaGasPartitionFunction n β =
      betaGasPartitionFunction n β (fun t => t ^ 2 / 2) := (rfl)

/-- The defining integral for the Gaussian beta-gas partition function. -/
theorem gaussianBetaGasPartitionFunction_def (n : ℕ) (β : ℝ) :
    gaussianBetaGasPartitionFunction n β =
      ∫ x : Fin n → ℝ, gaussianBetaGasWeight n β x
        ∂(volume : Measure (Fin n → ℝ)) := (rfl)

/-- The partition function is nonnegative, including when the weight is not integrable. -/
theorem gaussianBetaGasPartitionFunction_nonneg (n : ℕ) (β : ℝ) :
    0 ≤ gaussianBetaGasPartitionFunction n β :=
  betaGasPartitionFunction_nonneg n β _

/-- The Gaussian beta-gas density; it integrates to one for `0 < β`. -/
def gaussianBetaGasPDFReal (n : ℕ) (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  betaGasPDFReal n β (fun t => t ^ 2 / 2) x

/-- The Gaussian density is the quadratic-potential specialization. -/
theorem gaussianBetaGasPDFReal_eq_betaGasPDFReal (n : ℕ) (β : ℝ) :
    gaussianBetaGasPDFReal n β = betaGasPDFReal n β (fun t => t ^ 2 / 2) := (rfl)

/-- The Gaussian density is measurable for every inverse temperature. -/
@[fun_prop]
theorem measurable_gaussianBetaGasPDFReal (n : ℕ) (β : ℝ) :
    Measurable (gaussianBetaGasPDFReal n β) :=
  measurable_betaGasPDFReal n β (V := fun t => t ^ 2 / 2) (by fun_prop)

/-- The Gaussian density is continuous for nonnegative inverse temperature. -/
@[fun_prop]
theorem continuous_gaussianBetaGasPDFReal (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    Continuous (gaussianBetaGasPDFReal n β) :=
  continuous_betaGasPDFReal n hβ (V := fun t => t ^ 2 / 2) (by fun_prop)

/-- The Gaussian beta-gas density is integrable at every inverse temperature. -/
theorem integrable_gaussianBetaGasPDFReal (n : ℕ) (β : ℝ) :
    Integrable (gaussianBetaGasPDFReal n β)
      (volume : Measure (Fin n → ℝ)) := by
  rw [gaussianBetaGasPDFReal_eq_betaGasPDFReal]
  exact integrable_betaGasPDFReal n β _

/-- The defining formula for the Gaussian beta-gas density. -/
theorem gaussianBetaGasPDFReal_def (n : ℕ) (β : ℝ) (x : Fin n → ℝ) :
    gaussianBetaGasPDFReal n β x =
      gaussianBetaGasWeight n β x / gaussianBetaGasPartitionFunction n β := (rfl)

/-- The Gaussian beta-gas density is nonnegative for every inverse temperature. -/
theorem gaussianBetaGasPDFReal_nonneg (n : ℕ) (β : ℝ)
    (x : Fin n → ℝ) : 0 ≤ gaussianBetaGasPDFReal n β x :=
  betaGasPDFReal_nonneg n β _ x

/-- The Gaussian beta-gas measure; it is a probability measure for `0 < β`. -/
def gaussianBetaGasMeasure (n : ℕ) (β : ℝ) : Measure (Fin n → ℝ) :=
  betaGasMeasure n β (fun t => t ^ 2 / 2)

/-- The Gaussian measure is the quadratic-potential specialization. -/
theorem gaussianBetaGasMeasure_eq_betaGasMeasure (n : ℕ) (β : ℝ) :
    gaussianBetaGasMeasure n β = betaGasMeasure n β (fun t => t ^ 2 / 2) := (rfl)

/-- The Gaussian beta-gas measure as a with-density measure. -/
theorem gaussianBetaGasMeasure_def (n : ℕ) (β : ℝ) :
    gaussianBetaGasMeasure n β =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (gaussianBetaGasPDFReal n β x)) := (rfl)

/-- Evaluate the Gaussian beta-gas measure on a set. -/
theorem gaussianBetaGasMeasure_apply (n : ℕ) (β : ℝ) (s : Set (Fin n → ℝ)) :
    gaussianBetaGasMeasure n β s =
      ENNReal.ofReal (∫ x in s, gaussianBetaGasPDFReal n β x
        ∂(volume : Measure (Fin n → ℝ))) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure, gaussianBetaGasPDFReal_eq_betaGasPDFReal]
  exact betaGasMeasure_apply n β _ s

instance (n : ℕ) (β : ℝ) : IsFiniteMeasure (gaussianBetaGasMeasure n β) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure]
  infer_instance

/-- Integrability against the Gaussian beta-gas measure is equivalent to
integrability of the density-weighted function against volume. -/
theorem integrable_gaussianBetaGasMeasure_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (β : ℝ) (f : (Fin n → ℝ) → E) :
    Integrable f (gaussianBetaGasMeasure n β) ↔
      Integrable (fun x => gaussianBetaGasPDFReal n β x • f x)
        (volume : Measure (Fin n → ℝ)) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure, gaussianBetaGasPDFReal_eq_betaGasPDFReal]
  exact integrable_betaGasMeasure_iff n β _ f

/-- Integrate a function against the Gaussian beta-gas measure. -/
theorem integral_gaussianBetaGasMeasure_eq_integral_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (β : ℝ) (f : (Fin n → ℝ) → E) :
    ∫ x, f x ∂gaussianBetaGasMeasure n β =
      ∫ x, gaussianBetaGasPDFReal n β x • f x
        ∂(volume : Measure (Fin n → ℝ)) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure, gaussianBetaGasPDFReal_eq_betaGasPDFReal]
  exact integral_betaGasMeasure_eq_integral_smul n β _ f

end TauCeti.Probability
