/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Statistics.Experiments.Density
import TauCeti.MeasureTheory.Measure.Lebesgue.DiagonalSlices

/-!
# The likelihood of a location family

For a density `f` on `ℝ`, the location family has the densities `f (· - θ)`, and a sample
`x : ι → ℝ` indexed by a finite type has the likelihood `L(x, u) = ∏ i, f (x i - u)` at the
location `u`. This file records the elementary facts about this likelihood used by
location-equivariant estimation: for measurable `f` it is jointly measurable in the sample and
the location; shifting the sample by `a` shifts the likelihood by `a`, and the first-moment
integrand `u * L(x, u)` correspondingly (pointwise identities, not identities between integrals);
it changes only on a Lebesgue-null set of locations when `f` is changed on a null set; and it is
almost everywhere nonnegative when `f` is. For a density `f` of `P`, the lower integral of any loss
against the i.i.d. law `Pⁿ` decomposes along the diagonal lines `u ↦ z - u·1`, as the integral of
the likelihood-weighted loss on each line.

## Main results

* `TauCeti.measurable_prod_apply_sub`: for measurable `f`, `(x, u) ↦ ∏ i, f (x i - u)` is
  measurable.
* `TauCeti.prod_apply_add_sub`, `TauCeti.mul_prod_apply_add_sub`: the likelihood and the
  first-moment integrand `u * L(x, u)` at a shifted sample, pointwise in `u`.
* `TauCeti.prod_apply_sub_ae_eq`, `TauCeti.prod_apply_sub_ae_nonneg`: the likelihood of a.e.
  equal, resp. a.e. nonnegative, densities.
* `TauCeti.HasDensity.lintegral_pi_eq_lintegral_indicator_mul_lintegral_sub_const`: the lower
  integral of an a.e. measurable `ℝ≥0∞`-valued loss against `Pⁿ`, decomposed along the diagonal
  lines and weighted by the likelihood.

The joint measurability is adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), file `CKSD/Inference/Families.lean`
(`measurable_prod_sub`, for samples indexed by `Fin n`); the other proofs are new.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι] {f : ℝ → ℝ}

/-- The location likelihood `(x, u) ↦ ∏ i, f (x i - u)` of a measurable `f` is jointly
measurable. -/
@[fun_prop]
theorem measurable_prod_apply_sub (hf : Measurable f) :
    Measurable fun p : (ι → ℝ) × ℝ ↦ ∏ i, f (p.1 i - p.2) :=
  Finset.measurable_prod _ fun i _ ↦
    hf.comp (((measurable_pi_apply i).comp measurable_fst).sub measurable_snd)

/-- The likelihood of the sample shifted by `a`, at the location `u`, is the likelihood of the
sample at `u - a`. -/
theorem prod_apply_add_sub (x : ι → ℝ) (a u : ℝ) :
    ∏ i, f (x i + a - u) = ∏ i, f (x i - (u - a)) :=
  Finset.prod_congr rfl fun i _ ↦ by rw [sub_sub_eq_add_sub]

/-- The first-moment integrand `u * L(x + a·1, u)` of the likelihood of the sample shifted by `a`,
at the location `u`: pointwise, it is the first-moment integrand of the likelihood of the sample
at `u - a` plus `a` times that likelihood. -/
theorem mul_prod_apply_add_sub (x : ι → ℝ) (a u : ℝ) :
    u * ∏ i, f (x i + a - u) =
      (u - a) * ∏ i, f (x i - (u - a)) + a * ∏ i, f (x i - (u - a)) := by
  rw [prod_apply_add_sub]
  ring

/-- Densities that agree Lebesgue-a.e. give likelihoods that agree at Lebesgue-a.e. location. -/
theorem prod_apply_sub_ae_eq {g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) (x : ι → ℝ) :
    (fun u ↦ ∏ i, f (x i - u)) =ᵐ[volume] fun u ↦ ∏ i, g (x i - u) := by
  filter_upwards [ae_all_iff.2 fun i ↦ (quasiMeasurePreserving_sub_left volume (x i)).ae hfg]
    with u hu using Finset.prod_congr rfl fun i _ ↦ hu i

/-- The likelihood of a Lebesgue-a.e. nonnegative density is nonnegative at Lebesgue-a.e.
location. -/
theorem prod_apply_sub_ae_nonneg (hf0 : 0 ≤ᵐ[volume] f) (x : ι → ℝ) :
    0 ≤ᵐ[volume] fun u ↦ ∏ i, f (x i - u) := by
  filter_upwards [ae_all_iff.2 fun i ↦ (quasiMeasurePreserving_sub_left volume (x i)).ae hf0]
    with u hu using Finset.prod_nonneg fun i _ ↦ hu i

/-- **The i.i.d. law of a density, sliced along the diagonal lines.** For a density `f` of `P` and
an a.e. measurable loss `L : (ι → ℝ) → ℝ≥0∞`, the lower integral of `L` against `Pⁿ` is the
integral, against the indicator of `z i₀ ∈ [0, 1]`, of the likelihood-weighted integrals
`∫⁻ u, ofReal (∏ i, f (z i - u)) * L (z - u·1)` along the lines `u ↦ z - u·1`. -/
theorem HasDensity.lintegral_pi_eq_lintegral_indicator_mul_lintegral_sub_const {P : Measure ℝ}
    (hf : HasDensity P volume f) (i₀ : ι) {L : (ι → ℝ) → ℝ≥0∞}
    (hL : AEMeasurable L (Measure.pi fun _ : ι ↦ P)) :
    ∫⁻ x, L x ∂(Measure.pi fun _ : ι ↦ P) =
      ∫⁻ z : ι → ℝ, (Icc (0 : ℝ) 1).indicator 1 (z i₀) *
        ∫⁻ u : ℝ, ENNReal.ofReal (∏ i, f (z i - u)) * L fun i ↦ z i - u := by
  have hprod := HasDensity.pi fun _ : ι ↦ hf
  rw [hprod.eq_withDensity] at hL ⊢
  exact lintegral_withDensity_eq_lintegral_indicator_mul_lintegral_sub_const i₀
    hprod.measurable.ennreal_ofReal.aemeasurable hL

end TauCeti
