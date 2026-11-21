/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Statistics.Experiments.Density
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.Statistics.Experiments.Location

/-!
# The Pitman estimator of location

Let `x = (xᵢ)_{i ∈ ι}` be a sample, indexed by a finite type `ι`, from the location family with
density `f(· - θ)`. An estimator `δ : ℝ^ι → ℝ` is *location equivariant* if
`δ (x + a·1) = δ x + a` for every shift `a`. The
**Pitman estimator** is

`pitmanEstimator f x = ∫ u ∏ f(xᵢ - u) du / ∫ ∏ f(xᵢ - u) du`.

The samples at which both integrals exist and the denominator is positive form the measurable,
translation-invariant set `pitmanGoodSet f`. For a density `f`, at a sample in the good set the
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

* `TauCeti.IsLocationEquivariant δ`: `δ (x + a·1) = δ x + a` for all `x` and `a`.
* `TauCeti.pitmanEstimator f`: the Pitman estimator for the density `f`.
* `TauCeti.pitmanGoodSet f`: the samples at which the Pitman estimator is well defined.

## Main results

* `TauCeti.measurableSet_pitmanGoodSet`, `TauCeti.add_const_mem_pitmanGoodSet_iff`: the good
  set is measurable and invariant under diagonal translations.
* `TauCeti.measurable_pitmanEstimator`, `TauCeti.pitmanEstimator_add_const`: the Pitman
  estimator is measurable and equivariant on the good set.
* `TauCeti.pitmanEstimator_congr_ae`, `TauCeti.pitmanGoodSet_congr_ae`: both depend on the
  density only up to a Lebesgue-null set.
* `TauCeti.IsLocationEquivariant.nonempty`: location-equivariant estimators exist only for
  nonempty samples.
* `TauCeti.pitmanEstimator_risk_zero_le_of_equivariant`: given a square-integrable
  location-equivariant estimator `δ`, the Pitman estimator is square integrable and its
  squared-error risk at `θ = 0` is at most that of `δ`.

## Implementation notes

The density is not assumed nonnegative everywhere: it is replaced by its positive part, which is
another density of the same law. For each fixed sample the two likelihoods agree at
Lebesgue-almost every location, so the two estimators agree at every sample.

The optimality theorem does not assume that the good set has full measure. Off the good set of an
a.e. nonnegative density the Pitman estimator takes the value `0` of a division by the junk value
`0` of a non-integrable or vanishing integral (`TauCeti.pitmanEstimator_eq_zero_of_notMem`). Since
`0` is the true location, such samples add nothing to the risk at `θ = 0`.

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

/-- An estimator `δ` on samples indexed by `ι` is **location equivariant** if shifting every
observation by `a` shifts the estimate by `a`. -/
def IsLocationEquivariant (δ : (ι → ℝ) → ℝ) : Prop :=
  ∀ x a, δ (fun i ↦ x i + a) = δ x + a

/-- Unfolding `TauCeti.IsLocationEquivariant`. -/
theorem isLocationEquivariant_iff {δ : (ι → ℝ) → ℝ} :
    IsLocationEquivariant δ ↔ ∀ x a, δ (fun i ↦ x i + a) = δ x + a :=
  Iff.rfl

/-- A location-equivariant estimator exists only for a nonempty sample: on the empty sample the
shift by `1` changes nothing. -/
theorem IsLocationEquivariant.nonempty {δ : (ι → ℝ) → ℝ} (h : IsLocationEquivariant δ) :
    Nonempty ι := by
  by_contra hι
  have : IsEmpty ι := not_nonempty_iff.1 hι
  have h1 := h 0 1
  rw [Subsingleton.elim (fun i ↦ (0 : ι → ℝ) i + 1) 0] at h1
  linarith

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

/-- For a nonnegative density `f`, the law `Pⁿ` is Lebesgue measure weighted by the product
`∏ i, f (x i)`, so the lower integral of `g²` against it is the integral of the likelihood
weighted `g²`, decomposed along the diagonal lines. -/
private theorem lintegral_ofReal_sq_pi_eq {P : Measure ℝ} (i₀ : ι)
    (hf : HasDensity P volume f) (hf0 : ∀ t, 0 ≤ f t) {g : (ι → ℝ) → ℝ}
    (hg : AEMeasurable g (Measure.pi fun _ : ι ↦ P)) :
    ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(Measure.pi fun _ : ι ↦ P) =
      ∫⁻ z : ι → ℝ, (Icc (0 : ℝ) 1).indicator 1 (z i₀) *
        ∫⁻ u : ℝ, ENNReal.ofReal (g (fun i ↦ z i - u) ^ 2 * ∏ i, f (z i - u)) := by
  set d : (ι → ℝ) → NNReal := fun x ↦ (∏ i, f (x i)).toNNReal
  have hd : Measurable d := (Finset.measurable_prod _ fun i _ ↦
    hf.measurable.comp (measurable_pi_apply i)).real_toNNReal
  -- `Pⁿ` is Lebesgue measure with the density `ofReal (∏ i, f (x i))`, the coercion of `d`.
  have hPn : Measure.pi (fun _ : ι ↦ P) = volume.withDensity fun x ↦ d x := by
    rw [hf.eq_withDensity, pi_withDensity (fun _ ↦ volume) fun _ ↦ hf.measurable.ennreal_ofReal,
      volume_pi]
    congr 1
    funext x
    exact (ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hf0 _).symm
  rw [hPn, lintegral_withDensity_eq_lintegral_indicator_mul_lintegral_sub_const i₀ hd
    (hPn ▸ (hg.pow_const 2).ennreal_ofReal)]
  refine lintegral_congr fun z ↦ ?_
  congr 1
  refine lintegral_congr fun u ↦ ?_
  rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  -- `ENNReal.ofReal r` is by definition the coercion of `r.toNNReal`.
  rfl

/-- On each diagonal line, the likelihood-weighted squared error of the Pitman estimator of a
nonnegative `f` is at most that of any location-equivariant `δ`. -/
private theorem lintegral_ofReal_pitmanEstimator_sq_mul_le (hf0 : ∀ t, 0 ≤ f t)
    {δ : (ι → ℝ) → ℝ} (heq : IsLocationEquivariant δ) (z : ι → ℝ) :
    ∫⁻ u : ℝ, ENNReal.ofReal (pitmanEstimator f (fun i ↦ z i - u) ^ 2 * ∏ i, f (z i - u)) ≤
      ∫⁻ u : ℝ, ENNReal.ofReal (δ (fun i ↦ z i - u) ^ 2 * ∏ i, f (z i - u)) := by
  simp only [sub_eq_add_neg, heq z]
  by_cases hz : z ∈ pitmanGoodSet f
  · obtain ⟨-, hl, -⟩ := mem_pitmanGoodSet.mp hz
    simp only [pitmanEstimator_add_const hz]
    simp only [← sub_eq_add_neg]
    exact lintegral_ofReal_sub_sq_mul_le aestronglyMeasurable_id
      (ae_of_all _ fun u ↦ Finset.prod_nonneg fun i _ ↦ hf0 _) hl (δ z)
  · simp [pitmanEstimator_eq_zero_of_notMem (ae_of_all _ hf0), hz]

/-- The lower integral of the squared error of the Pitman estimator of an everywhere nonnegative
density, under `Pⁿ`, is at most that of every a.e. measurable location-equivariant estimator. -/
private theorem lintegral_ofReal_pitmanEstimator_sq_le {P : Measure ℝ}
    (hf : HasDensity P volume f) (hf0 : ∀ t, 0 ≤ f t) {δ : (ι → ℝ) → ℝ}
    (hδ : AEMeasurable δ (Measure.pi fun _ : ι ↦ P)) (heq : IsLocationEquivariant δ) :
    ∫⁻ x, ENNReal.ofReal (pitmanEstimator f x ^ 2) ∂(Measure.pi fun _ : ι ↦ P) ≤
      ∫⁻ x, ENNReal.ofReal (δ x ^ 2) ∂(Measure.pi fun _ : ι ↦ P) := by
  obtain ⟨i₀⟩ := heq.nonempty
  rw [lintegral_ofReal_sq_pi_eq i₀ hf hf0
      (measurable_pitmanEstimator hf.measurable.aemeasurable).aemeasurable,
    lintegral_ofReal_sq_pi_eq i₀ hf hf0 hδ]
  exact lintegral_mono fun z ↦
    mul_le_mul_right (lintegral_ofReal_pitmanEstimator_sq_mul_le hf0 heq z) _

/-- **Optimality of the Pitman estimator.** Let `f` be a density of `P`. If `δ` is a
square-integrable location-equivariant estimator under `Pⁿ`, then the Pitman estimator is square
integrable under `Pⁿ`, and its squared-error risk at `θ = 0` is at most that of `δ`. -/
theorem pitmanEstimator_risk_zero_le_of_equivariant (P : Measure ℝ) (f : ℝ → ℝ)
    (hf : HasDensity P volume f) (δ : (ι → ℝ) → ℝ) (heq : IsLocationEquivariant δ)
    (h2 : MemLp δ 2 (Measure.pi fun _ : ι ↦ P)) :
    MemLp (pitmanEstimator f) 2 (Measure.pi fun _ : ι ↦ P) ∧
      ∫ x, pitmanEstimator f x ^ 2 ∂(Measure.pi fun _ : ι ↦ P) ≤
        ∫ x, δ x ^ 2 ∂(Measure.pi fun _ : ι ↦ P) := by
  -- Replace `f` by its positive part `g`, another density of `P`. For each fixed sample the
  -- likelihoods agree at Lebesgue-a.e. location, so the two estimators agree at every sample.
  set g : ℝ → ℝ := fun t ↦ max (f t) 0
  have hg : HasDensity P volume g := hf.congr_ae (hf.measurable.max measurable_const)
    (hf.ae_nonneg.mono fun t ht ↦ (max_eq_left ht).symm)
  have hpit : pitmanEstimator (ι := ι) f = pitmanEstimator g :=
    pitmanEstimator_congr_ae (hf.ae_nonneg.mono fun t ht ↦ (max_eq_left ht).symm)
  have hle := lintegral_ofReal_pitmanEstimator_sq_le hg (fun t ↦ le_max_right _ _)
    h2.aestronglyMeasurable.aemeasurable heq
  have hpm : AEStronglyMeasurable (pitmanEstimator g) (Measure.pi fun _ : ι ↦ P) :=
    (measurable_pitmanEstimator hg.measurable.aemeasurable).aestronglyMeasurable
  have hsq (x : ι → ℝ) : 0 ≤ (pitmanEstimator g x ^ 2 : ℝ) := sq_nonneg _
  have hfin := (lintegral_ofReal_ne_top_iff_integrable (h2.aestronglyMeasurable.pow 2)
    (ae_of_all _ fun x ↦ sq_nonneg (δ x))).2 h2.integrable_sq
  have hpi : Integrable (fun x ↦ pitmanEstimator g x ^ 2) (Measure.pi fun _ : ι ↦ P) :=
    (lintegral_ofReal_ne_top_iff_integrable (hpm.pow 2) (ae_of_all _ hsq)).1
      (ne_top_of_le_ne_top hfin hle)
  rw [hpit]
  refine ⟨(memLp_two_iff_integrable_sq hpm).2 hpi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hsq) (hpm.pow 2),
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
      (h2.aestronglyMeasurable.pow 2)]
  exact ENNReal.toReal_mono hfin hle

end TauCeti
