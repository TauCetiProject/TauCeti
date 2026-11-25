/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Statistics.Estimation.Equivariance
public import TauCeti.Statistics.Experiments.Density
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Average.WeightedMean
import TauCeti.Statistics.Experiments.Location

/-!
# The Pitman estimator of location

Let `x = (xᵢ)_{i ∈ ι}` be a sample, indexed by a finite type `ι`, from the location family with
density `f(· - θ)`. An estimator `δ : ℝ^ι → ℝ` is *location equivariant*
(`TauCeti.IsLocationEquivariant`) if `δ (x + a·1) = δ x + a` for every shift `a`. The
**Pitman estimator** is

`pitmanEstimator f x = ∫ u ∏ f(xᵢ - u) du / ∫ ∏ f(xᵢ - u) du`.

The samples at which both integrals exist and the denominator is positive form the
translation-invariant set `pitmanGoodSet f`, which is measurable when `f` is a.e. measurable.
For a density `f`, at a sample in the good set the
Pitman estimator is the posterior mean of `θ` under the improper uniform prior, and on the good
set it is equivariant. Outside the good set the posterior mean does not exist and the definition
still returns a real number (the junk value of a division or of a non-integrable integral).

The main theorem compares squared-error risks at `θ = 0`, where the sample has law `Pⁿ` for the
law `P` with density `f`: the risk of the Pitman estimator is at most that of every
square-integrable location-equivariant estimator, and the Pitman estimator is square integrable
as soon as one such competitor exists. This comparison is proved only at `θ = 0`. The Pitman
estimator itself need not be equivariant: it is equivariant on the good set. When the good set
has full `Pⁿ`-measure, it has full measure under every shifted law as well (it is invariant under
diagonal translations), so the Pitman estimator is almost surely equivariant, its risk does not
depend on `θ`, and the comparison then holds at every `θ`, since the risks of the equivariant
competitors do not depend on `θ` either. The proof decomposes Lebesgue measure on `ℝ^ι` along
the diagonal lines `u ↦ z - u·1`. On each line an equivariant estimator is
`u ↦ c - u` for a constant `c`, and its contribution to the risk is the weighted quadratic
`∫⁻ (c - u)² ∏ f(zᵢ - u) du`. On a line through a sample of the good set, this is minimal at the
weighted mean, which is the value of the Pitman estimator; on the other lines the Pitman
estimator vanishes, so its contribution at `θ = 0` is zero.

## Main definitions

* `TauCeti.pitmanEstimator f`: the Pitman estimator for the density `f`.
* `TauCeti.pitmanGoodSet f`: the samples at which the Pitman estimator is well defined.

## Main results

* `TauCeti.measurableSet_pitmanGoodSet`, `TauCeti.measurable_pitmanEstimator`: for an a.e.
  measurable `f`, the good set is measurable and the Pitman estimator is measurable on all of
  `ℝ^ι`.
* `TauCeti.add_const_mem_pitmanGoodSet_iff`, `TauCeti.pitmanEstimator_add_const`: with no
  measurability hypothesis, the good set is invariant under diagonal translations and the Pitman
  estimator is equivariant on it; `TauCeti.sub_const_mem_pitmanGoodSet_iff` and
  `TauCeti.pitmanEstimator_sub_const` are the subtraction forms.
* `TauCeti.ae_pitmanEstimator_add_const`: when the good set has full measure, the Pitman
  estimator is almost surely equivariant.
* `TauCeti.pitmanEstimator_congr_ae`, `TauCeti.pitmanGoodSet_congr_ae`: both depend on the
  density only up to a Lebesgue-null set.
* `TauCeti.pitmanEstimator_risk_zero_le_of_equivariant`: given a square-integrable
  location-equivariant estimator `δ`, the Pitman estimator is square integrable and its
  squared-error risk at `θ = 0` is at most that of `δ`.

## Implementation notes

The density is nonnegative only almost everywhere, so its likelihood on each diagonal line is
nonnegative at almost every location (`TauCeti.prod_apply_sub_ae_nonneg`), which is all that the
comparison on one line uses.

The optimality theorem does not assume that the good set has full measure. Off the good set of an
a.e. nonnegative density the Pitman estimator takes the value `0`
(`TauCeti.pitmanEstimator_eq_zero_of_notMem`): either the numerator is the junk value `0` of a
non-integrable integral, or the denominator is `0`, as the junk value of a non-integrable integral
or as a vanishing integral. Since `0` is the true location, such samples add nothing to the risk
at `θ = 0`.

The proofs are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), file
`CKSD/Inference/Families.lean`.

## References

* M. J. Schervish, *Theory of Statistics*, Springer (1995), Theorem 6.10.
* T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press
  (1967), Section 4.7.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {ι : Type*}

variable [Fintype ι]

/-- The **Pitman estimator** of location for the density `f`: the ratio
`(∫ u ∏ i, f (x i - u) du) / ∫ ∏ i, f (x i - u) du`. On `TauCeti.pitmanGoodSet f` it is the mean
of `u` weighted by the likelihood `∏ i, f (x i - u)`, that is, the posterior mean under the
improper uniform prior; off that set it is still a real number, given by Lean's conventions for
non-integrable integrals and division by zero, but not a posterior mean. -/
def pitmanEstimator (f : ℝ → ℝ) (x : ι → ℝ) : ℝ :=
  (∫ u, u * ∏ i, f (x i - u)) / ∫ u, ∏ i, f (x i - u)

/-- Unfolding `TauCeti.pitmanEstimator`. -/
theorem pitmanEstimator_def (f : ℝ → ℝ) (x : ι → ℝ) :
    pitmanEstimator f x = (∫ u, u * ∏ i, f (x i - u)) / ∫ u, ∏ i, f (x i - u) := by
  rw [pitmanEstimator]

/-- The samples at which the Pitman estimator is well defined: the likelihood
`u ↦ ∏ i, f (x i - u)` and the first-moment integrand `u ↦ u * ∏ i, f (x i - u)` are
integrable, and the integral of the likelihood is positive. -/
def pitmanGoodSet (f : ℝ → ℝ) : Set (ι → ℝ) :=
  {x | Integrable (fun u ↦ u * ∏ i, f (x i - u)) ∧ Integrable (fun u ↦ ∏ i, f (x i - u)) ∧
    0 < ∫ u, ∏ i, f (x i - u)}

/-- Membership in `TauCeti.pitmanGoodSet`. -/
theorem mem_pitmanGoodSet {f : ℝ → ℝ} {x : ι → ℝ} :
    x ∈ pitmanGoodSet f ↔ Integrable (fun u ↦ u * ∏ i, f (x i - u)) ∧
      Integrable (fun u ↦ ∏ i, f (x i - u)) ∧ 0 < ∫ u, ∏ i, f (x i - u) :=
  Iff.rfl

variable {f : ℝ → ℝ}

/-- The Pitman estimator depends on the density only up to a Lebesgue-null set. -/
theorem pitmanEstimator_congr_ae {g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    pitmanEstimator (ι := ι) f = pitmanEstimator g := by
  funext x
  have hl := prod_apply_sub_ae_eq hfg x
  rw [pitmanEstimator_def, pitmanEstimator_def, integral_congr_ae hl,
    integral_congr_ae (hl.mono fun u hu ↦ congrArg (u * ·) hu)]

/-- The Pitman good set depends on the density only up to a Lebesgue-null set. -/
theorem pitmanGoodSet_congr_ae {g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    pitmanGoodSet (ι := ι) f = pitmanGoodSet g := by
  ext x
  have hl := prod_apply_sub_ae_eq hfg x
  simp only [mem_pitmanGoodSet, integrable_congr hl, integral_congr_ae hl,
    integrable_congr (hl.mono fun u hu ↦ congrArg (u * ·) hu)]

/-- The Pitman estimator of an a.e. measurable density is measurable. -/
theorem measurable_pitmanEstimator (hf : AEMeasurable f volume) :
    Measurable (pitmanEstimator (ι := ι) f) := by
  rw [pitmanEstimator_congr_ae hf.ae_eq_mk]
  have h0 := measurable_prod_apply_sub (ι := ι) hf.measurable_mk
  exact ((measurable_snd.mul h0).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
    |>.div (h0.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- The Pitman good set of an a.e. measurable density is measurable. -/
theorem measurableSet_pitmanGoodSet (hf : AEMeasurable f volume) :
    MeasurableSet (pitmanGoodSet (ι := ι) f) := by
  rw [pitmanGoodSet_congr_ae hf.ae_eq_mk]
  have h0 := measurable_prod_apply_sub (ι := ι) hf.measurable_mk
  exact (measurableSet_integrable (measurable_snd.mul h0).stronglyMeasurable).inter
    ((measurableSet_integrable h0.stronglyMeasurable).inter (measurableSet_lt measurable_const
      (h0.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable))

/-- The Pitman good set is invariant under diagonal translations. -/
@[simp]
theorem add_const_mem_pitmanGoodSet_iff {x : ι → ℝ} {a : ℝ} :
    (fun i ↦ x i + a) ∈ pitmanGoodSet f ↔ x ∈ pitmanGoodSet f := by
  have key (y : ι → ℝ) (b : ℝ) (hy : y ∈ pitmanGoodSet f) :
      (fun i ↦ y i + b) ∈ pitmanGoodSet f := by
    obtain ⟨hm, hl, hpos⟩ := mem_pitmanGoodSet.mp hy
    refine mem_pitmanGoodSet.mpr ⟨?_, ?_, ?_⟩
    · simp_rw [mul_prod_apply_add_sub]
      exact (hm.comp_sub_right b).add ((hl.comp_sub_right b).const_mul b)
    · simp_rw [prod_apply_add_sub]
      exact hl.comp_sub_right b
    · simp_rw [prod_apply_add_sub]
      rwa [integral_sub_right_eq_self (fun u ↦ ∏ i, f (y i - u)) b]
  refine ⟨fun h ↦ ?_, key x a⟩
  simpa using key _ (-a) h

/-- The Pitman good set is invariant under subtracting a constant from every observation. -/
@[simp]
theorem sub_const_mem_pitmanGoodSet_iff {x : ι → ℝ} {a : ℝ} :
    (fun i ↦ x i - a) ∈ pitmanGoodSet f ↔ x ∈ pitmanGoodSet f := by
  simpa only [← sub_eq_add_neg] using add_const_mem_pitmanGoodSet_iff (f := f) (x := x) (a := -a)

/-- On the good set, the Pitman estimator is location equivariant. -/
@[simp]
theorem pitmanEstimator_add_const {x : ι → ℝ} (hx : x ∈ pitmanGoodSet f) (a : ℝ) :
    pitmanEstimator f (fun i ↦ x i + a) = pitmanEstimator f x + a := by
  obtain ⟨hm, hl, hpos⟩ := mem_pitmanGoodSet.mp hx
  have hW : ∫ u, ∏ i, f (x i + a - u) = ∫ u, ∏ i, f (x i - u) := by
    simp_rw [prod_apply_add_sub]
    exact integral_sub_right_eq_self (fun u ↦ ∏ i, f (x i - u)) a
  have hM : ∫ u, u * ∏ i, f (x i + a - u) =
      (∫ u, u * ∏ i, f (x i - u)) + a * ∫ u, ∏ i, f (x i - u) := by
    simp_rw [mul_prod_apply_add_sub]
    rw [integral_add (hm.comp_sub_right a) ((hl.comp_sub_right a).const_mul a),
      integral_sub_right_eq_self (fun u ↦ u * ∏ i, f (x i - u)) a, integral_const_mul,
      integral_sub_right_eq_self (fun u ↦ ∏ i, f (x i - u)) a]
  rw [pitmanEstimator_def, pitmanEstimator_def, hW, hM, add_div, mul_div_cancel_right₀ _ hpos.ne']

/-- On the good set the Pitman estimator commutes with subtracting a constant from every
observation. -/
@[simp]
theorem pitmanEstimator_sub_const {x : ι → ℝ} (hx : x ∈ pitmanGoodSet f) (a : ℝ) :
    pitmanEstimator f (fun i ↦ x i - a) = pitmanEstimator f x - a := by
  simpa only [← sub_eq_add_neg] using pitmanEstimator_add_const hx (-a)

/-- If almost every sample lies in the good set, the Pitman estimator is almost surely location
equivariant: almost every sample `x` satisfies `δ (x + a·1) = δ x + a` for every shift `a`. -/
theorem ae_pitmanEstimator_add_const {μ : Measure (ι → ℝ)}
    (h : ∀ᵐ x ∂μ, x ∈ pitmanGoodSet f) :
    ∀ᵐ x ∂μ, ∀ a, pitmanEstimator f (fun i ↦ x i + a) = pitmanEstimator f x + a :=
  h.mono fun _ hx ↦ pitmanEstimator_add_const hx

/-- Off the good set of an a.e. nonnegative `f` the Pitman estimator takes the junk value `0`:
one of its two integrals is the junk value `0` of a non-integrable function, or the denominator
is `0`. -/
@[simp]
theorem pitmanEstimator_eq_zero_of_notMem (hf0 : 0 ≤ᵐ[volume] f) {x : ι → ℝ}
    (hx : x ∉ pitmanGoodSet f) : pitmanEstimator f x = 0 := by
  simp only [mem_pitmanGoodSet, not_and_or, not_lt] at hx
  rw [pitmanEstimator_def]
  rcases hx with hm | hl | hpos
  · rw [integral_undef hm, zero_div]
  · rw [integral_undef hl, div_zero]
  · rw [le_antisymm hpos (integral_nonneg_of_ae (prod_apply_sub_ae_nonneg hf0 x)), div_zero]

/-- For a density `f` of `P`, the lower integral of `g²` against `Pⁿ` is the integral of the
likelihood-weighted `g²`, decomposed along the diagonal lines: the squared-loss case of
`TauCeti.HasDensity.lintegral_pi_eq_lintegral_indicator_mul_lintegral_sub_const`. -/
private theorem lintegral_ofReal_sq_pi_eq {P : Measure ℝ} (i₀ : ι)
    (hf : HasDensity P volume f) {g : (ι → ℝ) → ℝ}
    (hg : AEMeasurable g (Measure.pi fun _ : ι ↦ P)) :
    ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(Measure.pi fun _ : ι ↦ P) =
      ∫⁻ z : ι → ℝ, (Icc (0 : ℝ) 1).indicator 1 (z i₀) *
        ∫⁻ u : ℝ, ENNReal.ofReal (g (fun i ↦ z i - u) ^ 2 * ∏ i, f (z i - u)) := by
  rw [hf.lintegral_pi_eq_lintegral_indicator_mul_lintegral_sub_const i₀
    (hg.pow_const 2).ennreal_ofReal]
  refine lintegral_congr fun z ↦ ?_
  congr 1
  refine lintegral_congr fun u ↦ ?_
  rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm]

/-- On each diagonal line, the likelihood-weighted squared error of the Pitman estimator of an
a.e. nonnegative `f` is at most that of any location-equivariant `δ`. -/
private theorem lintegral_ofReal_pitmanEstimator_sq_mul_le (hf0 : 0 ≤ᵐ[volume] f)
    {δ : (ι → ℝ) → ℝ} (heq : IsLocationEquivariant δ) (z : ι → ℝ) :
    ∫⁻ u : ℝ, ENNReal.ofReal (pitmanEstimator f (fun i ↦ z i - u) ^ 2 * ∏ i, f (z i - u)) ≤
      ∫⁻ u : ℝ, ENNReal.ofReal (δ (fun i ↦ z i - u) ^ 2 * ∏ i, f (z i - u)) := by
  by_cases hz : z ∈ pitmanGoodSet f
  · simp only [pitmanEstimator_sub_const hz, heq.apply_sub_const]
    exact lintegral_ofReal_sub_sq_mul_le aestronglyMeasurable_id
      (prod_apply_sub_ae_nonneg hf0 z) (mem_pitmanGoodSet.mp hz).2.1 (δ z)
  · have hpit (u : ℝ) : pitmanEstimator f (fun i ↦ z i - u) = 0 :=
      pitmanEstimator_eq_zero_of_notMem hf0 (by simpa using hz)
    simp [hpit]

/-- The lower integral of the squared error of the Pitman estimator under `Pⁿ` is at most that of
every a.e. measurable location-equivariant estimator. -/
private theorem lintegral_ofReal_pitmanEstimator_sq_le {P : Measure ℝ}
    (hf : HasDensity P volume f) {δ : (ι → ℝ) → ℝ}
    (hδ : AEMeasurable δ (Measure.pi fun _ : ι ↦ P)) (heq : IsLocationEquivariant δ) :
    ∫⁻ x, ENNReal.ofReal (pitmanEstimator f x ^ 2) ∂(Measure.pi fun _ : ι ↦ P) ≤
      ∫⁻ x, ENNReal.ofReal (δ x ^ 2) ∂(Measure.pi fun _ : ι ↦ P) := by
  obtain ⟨i₀⟩ := heq.nonempty
  rw [lintegral_ofReal_sq_pi_eq i₀ hf
      (measurable_pitmanEstimator hf.measurable.aemeasurable).aemeasurable,
    lintegral_ofReal_sq_pi_eq i₀ hf hδ]
  exact lintegral_mono fun z ↦
    mul_le_mul_right (lintegral_ofReal_pitmanEstimator_sq_mul_le hf.ae_nonneg heq z) _

/-- **Optimality of the Pitman estimator.** Let `f` be a density of `P`. If `δ` is a
square-integrable location-equivariant estimator under `Pⁿ`, then the Pitman estimator is square
integrable under `Pⁿ`, and its squared-error risk at `θ = 0` is at most that of `δ`. -/
theorem pitmanEstimator_risk_zero_le_of_equivariant (P : Measure ℝ) (f : ℝ → ℝ)
    (hf : HasDensity P volume f) (δ : (ι → ℝ) → ℝ) (heq : IsLocationEquivariant δ)
    (h2 : MemLp δ 2 (Measure.pi fun _ : ι ↦ P)) :
    MemLp (pitmanEstimator f) 2 (Measure.pi fun _ : ι ↦ P) ∧
      ∫ x, pitmanEstimator f x ^ 2 ∂(Measure.pi fun _ : ι ↦ P) ≤
        ∫ x, δ x ^ 2 ∂(Measure.pi fun _ : ι ↦ P) := by
  have hle := lintegral_ofReal_pitmanEstimator_sq_le hf h2.aestronglyMeasurable.aemeasurable heq
  have hpm : AEStronglyMeasurable (pitmanEstimator f) (Measure.pi fun _ : ι ↦ P) :=
    (measurable_pitmanEstimator hf.measurable.aemeasurable).aestronglyMeasurable
  -- Squared-error risks as lower integrals of squared extended norms.
  have hlint {h : (ι → ℝ) → ℝ} (hh : AEStronglyMeasurable h (Measure.pi fun _ : ι ↦ P)) :
      ∫ x, h x ^ 2 ∂(Measure.pi fun _ : ι ↦ P) =
        (∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂(Measure.pi fun _ : ι ↦ P)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg (h x)) (hh.pow 2)
  simp only [← Real.enorm_sq_eq_ofReal_sq] at hle hlint
  have hfin := h2.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.1 h2
  rw [hlint hpm, hlint h2.aestronglyMeasurable]
  exact ⟨hpm.memLp_two_iff_lintegral_enorm_sq_lt_top.2 (hle.trans_lt hfin),
    ENNReal.toReal_mono hfin.ne hle⟩

end TauCeti
