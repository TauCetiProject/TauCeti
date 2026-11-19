/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Statistics.Experiments.Density
import TauCeti.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Integral.Pi
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# The Pitman estimator of location

Let `x = (x₁, …, xₙ)` be a sample from the location family with density `f(· - θ)`. An estimator
`δ : ℝⁿ → ℝ` is *location equivariant* if `δ (x + a·1) = δ x + a` for every shift `a`. The
**Pitman estimator** is the posterior mean of `θ` under the improper uniform prior,

`pitmanEstimator f x = ∫ u ∏ f(xᵢ - u) du / ∫ ∏ f(xᵢ - u) du`.

The samples at which both integrals exist and the denominator is positive form the measurable,
translation-invariant set `pitmanGoodSet f`, and on it the Pitman estimator is equivariant.

The main theorem says that the Pitman estimator has the smallest squared-error risk among
square-integrable location-equivariant estimators. An equivariant estimator has a risk that does
not depend on `θ`, so the statement is at `θ = 0`, where the sample has law `Pⁿ` for the law `P`
with density `f`. When the good set has full `Pⁿ`-measure, the Pitman estimator is itself
equivariant almost surely. The proof decomposes Lebesgue measure on `ℝⁿ` along the diagonal lines
`u ↦ z - u·1`. On each line an equivariant estimator is `u ↦ c - u` for a constant `c`, its
contribution to the risk is the weighted quadratic `∫ (c - u)² ∏ f(zᵢ - u) du`, and this is
minimal at the weighted mean, which is the value of the Pitman estimator.

## Main definitions

* `TauCeti.IsLocationEquivariant δ`: `δ (x + a·1) = δ x + a` for all `x` and `a`.
* `TauCeti.pitmanEstimator f`: the Pitman estimator for the density `f`.
* `TauCeti.pitmanGoodSet f`: the samples at which the Pitman estimator is well defined.

## Main results

* `TauCeti.measurableSet_pitmanGoodSet`, `TauCeti.add_const_mem_pitmanGoodSet_iff`: the good
  set is measurable and invariant under diagonal translations.
* `TauCeti.measurable_pitmanEstimator`, `TauCeti.pitmanEstimator_add_const`: the Pitman
  estimator is measurable and equivariant on the good set.
* `TauCeti.pitmanEstimator_minimum_equivariant_risk`: the Pitman estimator is square integrable
  and its squared-error risk is at most that of every square-integrable measurable
  location-equivariant estimator.

## Implementation notes

The density is not assumed nonnegative everywhere: it is replaced by its positive part, which is
another density of the same law and gives the same estimator.

The optimality theorem does not assume that the good set has full measure. Off the good set of a
nonnegative density the Pitman estimator takes the value `0` of a division by the junk value `0`
of a non-integrable or vanishing integral (`TauCeti.pitmanEstimator_eq_zero_of_notMem`). Since
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

variable {n : ℕ}

/-- An estimator `δ` on samples of size `n` is **location equivariant** if shifting every
observation by `a` shifts the estimate by `a`. -/
def IsLocationEquivariant (δ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x a, δ (fun i ↦ x i + a) = δ x + a

/-- Unfolding `TauCeti.IsLocationEquivariant`. -/
theorem isLocationEquivariant_iff {δ : (Fin n → ℝ) → ℝ} :
    IsLocationEquivariant δ ↔ ∀ x a, δ (fun i ↦ x i + a) = δ x + a :=
  Iff.rfl

/-- The **Pitman estimator** of location for the density `f`: the mean of `u` weighted by the
likelihood `∏ i, f (x i - u)`, that is, the posterior mean under the improper uniform prior. -/
def pitmanEstimator (f : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∫ u, u * ∏ i, f (x i - u)) / ∫ u, ∏ i, f (x i - u)

/-- Unfolding `TauCeti.pitmanEstimator`. -/
theorem pitmanEstimator_def (f : ℝ → ℝ) (x : Fin n → ℝ) :
    pitmanEstimator f x = (∫ u, u * ∏ i, f (x i - u)) / ∫ u, ∏ i, f (x i - u) := by
  rw [pitmanEstimator]

/-- The samples at which the Pitman estimator is well defined: the likelihood
`u ↦ ∏ i, f (x i - u)` and its first moment are integrable, and its integral is positive. -/
def pitmanGoodSet (f : ℝ → ℝ) : Set (Fin n → ℝ) :=
  {x | Integrable (fun u ↦ u * ∏ i, f (x i - u)) ∧ Integrable (fun u ↦ ∏ i, f (x i - u)) ∧
    0 < ∫ u, ∏ i, f (x i - u)}

/-- Membership in `TauCeti.pitmanGoodSet`. -/
theorem mem_pitmanGoodSet {f : ℝ → ℝ} {x : Fin n → ℝ} :
    x ∈ pitmanGoodSet f ↔ Integrable (fun u ↦ u * ∏ i, f (x i - u)) ∧
      Integrable (fun u ↦ ∏ i, f (x i - u)) ∧ 0 < ∫ u, ∏ i, f (x i - u) :=
  Iff.rfl

variable {f : ℝ → ℝ}

/-- The location likelihood `(x, u) ↦ ∏ i, f (x i - u)` is jointly measurable. -/
private theorem measurable_prod_apply_sub (hf : Measurable f) :
    Measurable fun p : (Fin n → ℝ) × ℝ ↦ ∏ i, f (p.1 i - p.2) :=
  Finset.measurable_prod _ fun i _ ↦
    hf.comp (((measurable_pi_apply i).comp measurable_fst).sub measurable_snd)

/-- The Pitman estimator of a measurable density is measurable. -/
theorem measurable_pitmanEstimator (hf : Measurable f) :
    Measurable (pitmanEstimator (n := n) f) := by
  have h0 := measurable_prod_apply_sub (n := n) hf
  exact ((measurable_snd.mul h0).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
    |>.div (h0.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- The Pitman good set of a measurable density is measurable. -/
theorem measurableSet_pitmanGoodSet (hf : Measurable f) :
    MeasurableSet (pitmanGoodSet (n := n) f) := by
  have h0 := measurable_prod_apply_sub (n := n) hf
  have hI : ∀ {F : (Fin n → ℝ) × ℝ → ℝ}, Measurable F →
      MeasurableSet {x | Integrable (fun u ↦ F (x, u))} := fun {F} hF ↦ by
    have : {x | Integrable (fun u ↦ F (x, u))} = {x | ∫⁻ u, ‖F (x, u)‖ₑ < ∞} := by
      ext x
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨(hF.comp measurable_prodMk_left).aestronglyMeasurable, h⟩⟩
    rw [this]
    exact hF.eNorm.lintegral_prod_right' measurableSet_Iio
  exact (hI (measurable_snd.mul h0)).inter ((hI h0).inter (measurableSet_lt measurable_const
    (h0.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable))

/-- Shifting the sample by `a` shifts the likelihood by `a`. -/
private theorem prod_apply_add_sub (x : Fin n → ℝ) (a u : ℝ) :
    ∏ i, f (x i + a - u) = ∏ i, f (x i - (u - a)) :=
  Finset.prod_congr rfl fun i _ ↦ by rw [sub_sub_eq_add_sub]

/-- The Pitman good set is invariant under diagonal translations. -/
theorem add_const_mem_pitmanGoodSet_iff {x : Fin n → ℝ} {a : ℝ} :
    (fun i ↦ x i + a) ∈ pitmanGoodSet f ↔ x ∈ pitmanGoodSet f := by
  have key (y : Fin n → ℝ) (b : ℝ) (hy : y ∈ pitmanGoodSet f) :
      (fun i ↦ y i + b) ∈ pitmanGoodSet f := by
    obtain ⟨hm, hl, hpos⟩ := hy
    simp only [mem_pitmanGoodSet, prod_apply_add_sub]
    refine ⟨?_, hl.comp_sub_right b, ?_⟩
    · refine ((hm.comp_sub_right b).add (hl.comp_sub_right b |>.const_mul b)).congr
        (ae_of_all _ fun u ↦ ?_)
      simp only [Pi.add_apply]
      ring
    · rwa [integral_sub_right_eq_self (fun u ↦ ∏ i, f (y i - u)) b]
  refine ⟨fun h ↦ ?_, key x a⟩
  simpa using key _ (-a) h

/-- On the good set, the Pitman estimator is location equivariant. -/
theorem pitmanEstimator_add_const {x : Fin n → ℝ} (hx : x ∈ pitmanGoodSet f) (a : ℝ) :
    pitmanEstimator f (fun i ↦ x i + a) = pitmanEstimator f x + a := by
  obtain ⟨hm, hl, hpos⟩ := hx
  have hW : ∫ u, ∏ i, f (x i + a - u) = ∫ u, ∏ i, f (x i - u) := by
    simp only [prod_apply_add_sub]
    exact integral_sub_right_eq_self (fun u ↦ ∏ i, f (x i - u)) a
  have hM : ∫ u, u * ∏ i, f (x i + a - u) =
      (∫ u, u * ∏ i, f (x i - u)) + a * ∫ u, ∏ i, f (x i - u) := by
    simp only [prod_apply_add_sub]
    rw [← integral_const_mul, ← integral_add hm (hl.const_mul a),
      ← integral_sub_right_eq_self (fun u ↦ u * ∏ i, f (x i - u) + a * ∏ i, f (x i - u)) a]
    exact integral_congr_ae (ae_of_all _ fun u ↦ by simp only; ring)
  rw [pitmanEstimator_def, pitmanEstimator_def, hW, hM, add_div, mul_div_cancel_right₀ _ hpos.ne']


/-- The Pitman estimator depends on the density only up to a Lebesgue-null set. -/
theorem pitmanEstimator_congr_ae {g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    pitmanEstimator (n := n) f = pitmanEstimator g := by
  have hl (x : Fin n → ℝ) : (fun u ↦ ∏ i, f (x i - u)) =ᵐ[volume] fun u ↦ ∏ i, g (x i - u) := by
    filter_upwards [ae_all_iff.2 fun i ↦ (quasiMeasurePreserving_sub_left volume (x i)).ae hfg]
      with u hu using Finset.prod_congr rfl fun i _ ↦ hu i
  funext x
  rw [pitmanEstimator_def, pitmanEstimator_def, integral_congr_ae (hl x),
    integral_congr_ae ((hl x).mono fun u hu ↦ congrArg (u * ·) hu)]

/-- Off the good set of a nonnegative `f` the Pitman estimator takes the junk value `0`: one of
its two integrals is the junk value `0` of a non-integrable function, or the denominator is `0`. -/
theorem pitmanEstimator_eq_zero_of_notMem (hf0 : ∀ t, 0 ≤ f t) {x : Fin n → ℝ}
    (hx : x ∉ pitmanGoodSet f) : pitmanEstimator f x = 0 := by
  simp only [mem_pitmanGoodSet, not_and_or, not_lt] at hx
  rw [pitmanEstimator_def]
  rcases hx with hm | hl | hpos
  · rw [integral_undef hm, zero_div]
  · rw [integral_undef hl, div_zero]
  · rw [le_antisymm hpos (integral_nonneg fun u ↦ Finset.prod_nonneg fun i _ ↦ hf0 _), div_zero]

/-- For a nonnegative density `f`, the law `Pⁿ` is Lebesgue measure weighted by the product
`∏ i, f (x i)`, so the lower integral of `g²` against it is the integral of the likelihood
weighted `g²`, decomposed along the diagonal lines. -/
private theorem lintegral_ofReal_sq_pi_eq {P : Measure ℝ} (i₀ : Fin n)
    (hf : HasDensity P volume f) (hf0 : ∀ t, 0 ≤ f t) {g : (Fin n → ℝ) → ℝ} (hg : Measurable g) :
    ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(Measure.pi fun _ : Fin n ↦ P) =
      ∫⁻ z : Fin n → ℝ, (Icc (0 : ℝ) 1).indicator 1 (z i₀) *
        ∫⁻ u : ℝ, ENNReal.ofReal (g (fun i ↦ z i - u) ^ 2 * ∏ i, f (z i - u)) := by
  have hD : Measurable fun x : Fin n → ℝ ↦ ∏ i, ENNReal.ofReal (f (x i)) :=
    Finset.measurable_prod _ fun i _ ↦ (hf.measurable.comp (measurable_pi_apply i)).ennreal_ofReal
  have hPn : Measure.pi (fun _ : Fin n ↦ P) =
      volume.withDensity fun x ↦ ∏ i, ENNReal.ofReal (f (x i)) := by
    rw [hf.eq_withDensity, pi_withDensity (fun _ ↦ volume) fun _ ↦ hf.measurable.ennreal_ofReal,
      volume_pi]
  have hH : Measurable fun y : Fin n → ℝ ↦ ENNReal.ofReal (g y ^ 2 * ∏ i, f (y i)) :=
    ((hg.pow_const 2).mul (Finset.measurable_prod _ fun i _ ↦
      hf.measurable.comp (measurable_pi_apply i))).ennreal_ofReal
  rw [← lintegral_eq_lintegral_indicator_mul_lintegral_sub_const i₀ hH, hPn,
    lintegral_withDensity_eq_lintegral_mul _ hD (hg.pow_const 2).ennreal_ofReal]
  refine lintegral_congr fun x ↦ ?_
  rw [Pi.mul_apply, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hf0 _, mul_comm]

/-- On each diagonal line, the likelihood-weighted squared error of the Pitman estimator of a
nonnegative `f` is at most that of any location-equivariant `δ`. -/
private theorem lintegral_ofReal_pitmanEstimator_sq_mul_le (hf0 : ∀ t, 0 ≤ f t)
    {δ : (Fin n → ℝ) → ℝ} (heq : IsLocationEquivariant δ) (z : Fin n → ℝ) :
    ∫⁻ u : ℝ, ENNReal.ofReal (pitmanEstimator f (fun i ↦ z i - u) ^ 2 * ∏ i, f (z i - u)) ≤
      ∫⁻ u : ℝ, ENNReal.ofReal (δ (fun i ↦ z i - u) ^ 2 * ∏ i, f (z i - u)) := by
  simp only [sub_eq_add_neg, heq z]
  by_cases hz : z ∈ pitmanGoodSet f
  · obtain ⟨hm, hl, -⟩ := id hz
    simp only [pitmanEstimator_add_const hz]
    simp only [← sub_eq_add_neg]
    exact lintegral_ofReal_sq_sub_mul_le
      (ae_of_all _ fun u ↦ Finset.prod_nonneg fun i _ ↦ hf0 _) hl hm (δ z)
  · simp [pitmanEstimator_eq_zero_of_notMem hf0, add_const_mem_pitmanGoodSet_iff, hz]

/-- The Pitman estimator of an everywhere nonnegative density has the smallest lower integral of
the squared error among measurable location-equivariant estimators. -/
private theorem lintegral_ofReal_pitmanEstimator_sq_le {P : Measure ℝ}
    (hf : HasDensity P volume f) (hf0 : ∀ t, 0 ≤ f t)
    {δ : (Fin n → ℝ) → ℝ} (hδ : Measurable δ) (heq : IsLocationEquivariant δ) :
    ∫⁻ x, ENNReal.ofReal (pitmanEstimator f x ^ 2) ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ∫⁻ x, ENNReal.ofReal (δ x ^ 2) ∂(Measure.pi fun _ : Fin n ↦ P) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- For `n = 0` the likelihood is the constant `1`, which is not integrable.
    have h0 (x : Fin 0 → ℝ) : pitmanEstimator f x = 0 := by
      refine pitmanEstimator_eq_zero_of_notMem hf0 fun hx ↦ ?_
      obtain ⟨-, hl, -⟩ := hx
      simp only [Finset.univ_eq_empty, Finset.prod_empty, integrable_const_iff, one_ne_zero,
        false_or] at hl
      exact absurd (@measure_lt_top _ _ volume hl univ) (by simp)
    simp [h0]
  rw [lintegral_ofReal_sq_pi_eq ⟨0, hn⟩ hf hf0 (measurable_pitmanEstimator hf.measurable),
    lintegral_ofReal_sq_pi_eq ⟨0, hn⟩ hf hf0 hδ]
  exact lintegral_mono fun z ↦
    mul_le_mul_right (lintegral_ofReal_pitmanEstimator_sq_mul_le hf0 heq z) _

/-- **Optimality of the Pitman estimator.** For a density `f` of `P`, the Pitman estimator is
square integrable under `Pⁿ`, and its squared-error risk at `θ = 0` is at most that of every
measurable, square-integrable, location-equivariant estimator `δ`. -/
theorem pitmanEstimator_minimum_equivariant_risk (P : Measure ℝ) (f : ℝ → ℝ)
    (hf : HasDensity P volume f)
    (δ : (Fin n → ℝ) → ℝ) (hδ : Measurable δ) (heq : IsLocationEquivariant δ)
    (h2 : MemLp δ 2 (Measure.pi fun _ : Fin n ↦ P)) :
    MemLp (pitmanEstimator f) 2 (Measure.pi fun _ : Fin n ↦ P) ∧
      ∫ x, pitmanEstimator f x ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P) ≤
        ∫ x, δ x ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P) := by
  -- Replace `f` by its positive part `g`, another density of `P` with the same likelihoods.
  set g : ℝ → ℝ := fun t ↦ max (f t) 0
  have hg : HasDensity P volume g := hf.congr_ae (hf.measurable.max measurable_const)
    (hf.ae_nonneg.mono fun t ht ↦ (max_eq_left ht).symm)
  have hpit : pitmanEstimator (n := n) f = pitmanEstimator g :=
    pitmanEstimator_congr_ae (hf.ae_nonneg.mono fun t ht ↦ (max_eq_left ht).symm)
  have hle := lintegral_ofReal_pitmanEstimator_sq_le hg (fun t ↦ le_max_right _ _) hδ heq
  have hpm := measurable_pitmanEstimator (n := n) hg.measurable
  have hfin := (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ sq_nonneg (δ x))).1
    h2.integrable_sq.2
  rw [hpit]
  refine ⟨(memLp_two_iff_integrable_sq hpm.aestronglyMeasurable).2
    ⟨(hpm.pow_const 2).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun x ↦ sq_nonneg _)).2 (hle.trans_lt hfin)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
      (hpm.pow_const 2).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
      (hδ.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_mono hfin.ne hle

end TauCeti
