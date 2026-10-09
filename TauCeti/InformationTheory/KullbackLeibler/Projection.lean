/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue
public import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Relative-entropy projection onto a prescribed law

Let `π` be a finite measure on `Ω`, let `f : Ω → X` be measurable and let `μ` be a finite measure
on `X`. Reweighting `π` along the fibres of `f` gives
`π.fitLaw f μ = π.withDensity (fun ω ↦ dμ/d(f₊π) (f ω))`. When `μ ≪ π.map f`, `f` has law `μ`
under this measure, and among the measures `σ` on `Ω` with `σ.map f = μ` it is the one closest to
`π` in relative entropy: the relative-entropy projection (Csiszár's I-projection) onto the linear
family `{σ | σ.map f = μ}`. Without that hypothesis the law of `f` under `π.fitLaw f μ` is only
the part of `μ` absolutely continuous with respect to `π.map f`, and the family contains no
measure of finite relative entropy with respect to `π`. With `f` a coordinate projection of a
product it fits one marginal of a measure on a product, which is the half-step of iterative
proportional fitting.

The measure `π.fitLaw f μ` satisfies a Pythagorean identity: for every finite measure `σ` with
`σ.map f = μ`,
`klDiv σ π = klDiv μ (π.map f) + klDiv σ (π.fitLaw f μ)`.
It holds in `ℝ≥0∞` with no absolute-continuity or integrability hypothesis, and, when
`μ ≪ π.map f`, contains both the minimality of the projection and its uniqueness as a minimiser.
The first summand is the error of the law of `f` under `π`; the second measures how far `σ` still
is from `π.fitLaw f μ`.

## Main definitions

* `MeasureTheory.Measure.fitLaw π f μ`: the measure `π` reweighted along `f` so that, when
  `μ ≪ π.map f`, the law of `f` becomes `μ`.

## Main statements

* `MeasureTheory.Measure.map_fitLaw_of_absolutelyContinuous`: if `μ ≪ π.map f`, then `f` has
  law `μ` under `π.fitLaw f μ`.
* `MeasureTheory.Measure.fitLaw_eq_self`: a measure under which `f` already has law `μ` is its
  own projection.
* `MeasureTheory.Measure.fitLaw_apply_singleton`: on spaces with measurable singletons, the
  projection multiplies the mass of each point `ω` by `μ {f ω} / π.map f {f ω}`;
  `MeasureTheory.Measure.fitLaw_real_singleton` is the same for real masses.
* `TauCeti.klDiv_eq_klDiv_map_add_klDiv_fitLaw`: the Pythagorean identity above.
* `TauCeti.klDiv_fitLaw`: if `μ ≪ π.map f`, the projection lies at relative entropy
  `klDiv μ (π.map f)` from `π`.
* `TauCeti.klDiv_fitLaw_le`: `klDiv (π.fitLaw f μ) π ≤ klDiv σ π` whenever `σ.map f = μ`. When
  `μ ≪ π.map f` the projection itself has law `μ`, so it minimises `klDiv · π` over the measures
  under which `f` has law `μ`.
* `TauCeti.eq_fitLaw_of_klDiv_le`: a measure under which `f` has law `μ`, of finite relative
  entropy no larger than that of the projection, is the projection; so the projection is the only
  minimiser of finite relative entropy.

## References

* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probability 3 (1975), 146–158, for I-projections onto linear families and their
  Pythagorean identity.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  for the marginal projections of iterative proportional fitting.
-/

public section

noncomputable section

open MeasureTheory InformationTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {π σ : Measure Ω} {f : Ω → X}
  {μ : Measure X}

/-- The measure `π` reweighted along `f` by the density `dμ/d(f₊π)` of `μ` against the law of `f`
under `π`. When `μ ≪ π.map f`, the law of `f` under `π.fitLaw f μ` is `μ`
(`MeasureTheory.Measure.map_fitLaw_of_absolutelyContinuous`), and among all measures with this
property it is the closest to `π` in relative entropy (`TauCeti.klDiv_fitLaw_le`). -/
def fitLaw (π : Measure Ω) (f : Ω → X) (μ : Measure X) : Measure Ω :=
  π.withDensity fun ω ↦ μ.rnDeriv (π.map f) (f ω)

theorem fitLaw_def (π : Measure Ω) (f : Ω → X) (μ : Measure X) :
    π.fitLaw f μ = π.withDensity fun ω ↦ μ.rnDeriv (π.map f) (f ω) :=
  (rfl)

/-- The projection only reweights `π`, so it is absolutely continuous with respect to `π`. -/
theorem fitLaw_absolutelyContinuous : π.fitLaw f μ ≪ π :=
  withDensity_absolutelyContinuous _ _

/-- The law of `f` under `π.fitLaw f μ` is the law of `f` under `π` reweighted by `dμ/d(f₊π)`,
which is the part of `μ` absolutely continuous with respect to `π.map f`. -/
theorem map_fitLaw (hf : Measurable f) :
    (π.fitLaw f μ).map f = (π.map f).withDensity (μ.rnDeriv (π.map f)) := by
  rw [fitLaw_def]
  exact map_withDensity_eq_withDensity (jac := 1) hf measurable_const (measurable_rnDeriv _ _)
    (by simp) (by simp)

/-- If `μ ≪ π.map f`, then `f` has law `μ` under `π.fitLaw f μ`. -/
@[simp]
theorem map_fitLaw_of_absolutelyContinuous [SigmaFinite μ] [SigmaFinite (π.map f)]
    (hf : Measurable f) (hμ : μ ≪ π.map f) : (π.fitLaw f μ).map f = μ := by
  rw [map_fitLaw hf, withDensity_rnDeriv_eq _ _ hμ]

/-- The projection of any measure onto a finite law is finite: its total mass is that of the part
of `μ` absolutely continuous with respect to `π.map f`. -/
theorem isFiniteMeasure_fitLaw [IsFiniteMeasure μ] (hf : Measurable f) :
    IsFiniteMeasure (π.fitLaw f μ) where
  measure_univ_lt_top := by
    rw [← preimage_univ (f := f), ← map_apply hf MeasurableSet.univ, map_fitLaw hf,
      withDensity_apply _ MeasurableSet.univ, restrict_univ]
    exact lintegral_rnDeriv_le.trans_lt (measure_lt_top μ univ)

/-- A measure under which `f` already has law `μ` is its own projection. -/
@[simp]
theorem fitLaw_eq_self [SigmaFinite μ] (hf : Measurable f) (h : π.map f = μ) :
    π.fitLaw f μ = π := by
  subst h
  rw [fitLaw_def]
  conv_rhs => rw [← withDensity_one (μ := π)]
  exact withDensity_congr_ae (ae_of_ae_map hf.aemeasurable (rnDeriv_self _))

/-- On spaces with measurable singletons, the projection reweights the mass of each point `ω` by
the ratio of the masses that `μ` and the law of `f` under `π` give to `f ω`. -/
theorem fitLaw_apply_singleton [MeasurableSingletonClass Ω] [MeasurableSingletonClass X]
    [IsFiniteMeasure π] [SigmaFinite μ] (hf : Measurable f) (ω : Ω) :
    π.fitLaw f μ {ω} = μ {f ω} / π.map f {f ω} * π {ω} := by
  rw [fitLaw_def, withDensity_apply _ (measurableSet_singleton ω), lintegral_singleton]
  rcases eq_or_ne (π {ω}) 0 with h | h
  · rw [h, mul_zero, mul_zero]
  have hle : π {ω} ≤ π.map f {f ω} := by
    rw [map_apply hf (measurableSet_singleton _)]
    exact measure_mono (Set.singleton_subset_iff.2 rfl)
  rw [rnDeriv_eq_measure_singleton_div (ne_bot_of_le_ne_bot h hle) (measure_ne_top _ _)]

/-- The real-mass form of `MeasureTheory.Measure.fitLaw_apply_singleton`: the projection reweights
the real mass of each point `ω` by `μ.real {f ω} / (π.map f).real {f ω}`. -/
theorem fitLaw_real_singleton [MeasurableSingletonClass Ω] [MeasurableSingletonClass X]
    [IsFiniteMeasure π] [SigmaFinite μ] (hf : Measurable f) (ω : Ω) :
    (π.fitLaw f μ).real {ω} = μ.real {f ω} / (π.map f).real {f ω} * π.real {ω} := by
  rw [measureReal_def, fitLaw_apply_singleton hf, ENNReal.toReal_mul, ENNReal.toReal_div]
  rfl

/-- A measure `σ ≪ π` under which `f` has law `μ` is absolutely continuous with respect to the
projection `π.fitLaw f μ`: the reweighting only removes mass on which `dμ/d(f₊π) ∘ f` vanishes,
which `σ` does not charge. -/
theorem absolutelyContinuous_fitLaw [SigmaFinite μ] [SigmaFinite (π.map f)]
    (hf : Measurable f) (hσ : σ.map f = μ) (hμ : μ ≪ π.map f) (h : σ ≪ π) :
    σ ≪ π.fitLaw f μ := by
  refine AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  rw [fitLaw_def, withDensity_apply _ hs,
    setLIntegral_eq_zero_iff hs (f := fun ω ↦ μ.rnDeriv (π.map f) (f ω))
      ((measurable_rnDeriv _ _).comp hf)] at hs0
  have hpos : ∀ᵐ x ∂(σ.map f), 0 < μ.rnDeriv (π.map f) x := by
    rw [hσ]
    exact rnDeriv_pos hμ
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [h.ae_le hs0, ae_of_ae_map hf.aemeasurable hpos] with ω h0 hω hωs
  exact hω.ne' (h0 hωs)

end MeasureTheory.Measure

namespace TauCeti

open Measure

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {π σ : Measure Ω} {f : Ω → X}
  {μ : Measure X}

/-- Along the projection, the log-likelihood ratio of `σ` against `π` splits as that of the law
`μ` of `f` against `f₊π`, evaluated at `f`, plus that of `σ` against the projection. -/
private theorem llr_ae_eq_llr_comp_add [IsFiniteMeasure π] [IsFiniteMeasure σ]
    [IsFiniteMeasure μ] (hf : Measurable f) (hσ : σ.map f = μ) (hμ : μ ≪ π.map f)
    (h : σ ≪ π.fitLaw f μ) :
    llr σ π =ᵐ[σ] fun ω ↦ llr μ (π.map f) (f ω) + llr σ (π.fitLaw f μ) ω := by
  have := isFiniteMeasure_fitLaw (π := π) (μ := μ) hf
  have hσπ : σ ≪ π := h.trans fitLaw_absolutelyContinuous
  have hdens : (π.fitLaw f μ).rnDeriv π =ᵐ[π] fun ω ↦ μ.rnDeriv (π.map f) (f ω) := by
    rw [fitLaw_def]
    exact rnDeriv_withDensity _ ((measurable_rnDeriv _ _).comp hf)
  have hlaw : ∀ᵐ ω ∂σ, 0 < μ.rnDeriv (π.map f) (f ω) ∧ μ.rnDeriv (π.map f) (f ω) < ∞ := by
    refine ae_of_ae_map (p := fun x ↦ 0 < μ.rnDeriv (π.map f) x ∧ μ.rnDeriv (π.map f) x < ∞)
      hf.aemeasurable ?_
    rw [hσ]
    exact (rnDeriv_pos hμ).and (hμ.ae_le (rnDeriv_lt_top μ (π.map f)))
  filter_upwards [hσπ.ae_le (rnDeriv_mul_rnDeriv h), hσπ.ae_le hdens, hlaw, rnDeriv_pos h,
    h.ae_le (rnDeriv_lt_top σ (π.fitLaw f μ))] with ω hmul hd ⟨hg0, hgt⟩ hr0 hrt
  simp only [llr_def]
  rw [← hmul, Pi.mul_apply, hd, ENNReal.toReal_mul,
    Real.log_mul (ENNReal.toReal_pos hr0.ne' hrt.ne).ne' (ENNReal.toReal_pos hg0.ne' hgt.ne).ne',
    add_comm]

/-- **Pythagorean identity for the relative-entropy projection onto a prescribed law.** If `f` has
law `μ` under a finite measure `σ`, then
`klDiv σ π = klDiv μ (π.map f) + klDiv σ (π.fitLaw f μ)`.
The identity holds in `ℝ≥0∞` with no absolute-continuity or integrability hypothesis: each side is
infinite exactly when the other is. -/
theorem klDiv_eq_klDiv_map_add_klDiv_fitLaw [IsFiniteMeasure π] [IsFiniteMeasure σ]
    (hf : Measurable f) (hσ : σ.map f = μ) :
    klDiv σ π = klDiv μ (π.map f) + klDiv σ (π.fitLaw f μ) := by
  have : IsFiniteMeasure μ := hσ ▸ isFiniteMeasure_map σ f
  have := isFiniteMeasure_fitLaw (π := π) (μ := μ) hf
  -- If the law of `f` already has infinite relative entropy, so does `σ`, by data processing.
  by_cases hμ : klDiv μ (π.map f) = ∞
  · rw [hμ, _root_.top_add, ← top_le_iff, ← hμ, ← hσ]
    exact klDiv_map_le σ π hf
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.1 hμ
  -- Otherwise `σ ≪ π` and `σ ≪ π.fitLaw f μ` are equivalent.
  by_cases hσπ : σ ≪ π
  swap
  · rw [klDiv_of_not_ac hσπ, klDiv_of_not_ac fun h ↦ hσπ (h.trans fitLaw_absolutelyContinuous),
      _root_.add_top]
  have hσπ' := absolutelyContinuous_fitLaw hf hσ hac hσπ
  have hllr := llr_ae_eq_llr_comp_add hf hσ hac hσπ'
  have hint_comp : Integrable (fun ω ↦ llr μ (π.map f) (f ω)) σ :=
    (integrable_map_measure (measurable_llr _ _).aestronglyMeasurable hf.aemeasurable).1
      (hσ ▸ hint)
  -- And the two log-likelihood ratios differ by an integrable function.
  by_cases hint' : Integrable (llr σ (π.fitLaw f μ)) σ
  swap
  · refine (klDiv_of_not_integrable fun h ↦ hint' ?_).trans (by rw [klDiv_of_not_integrable hint',
      _root_.add_top])
    refine (h.sub hint_comp).congr ?_
    filter_upwards [hllr] with ω hω
    simp [hω]
  have hint_σπ : Integrable (llr σ π) σ := (hint_comp.add hint').congr hllr.symm
  rw [klDiv_of_ac_of_integrable hσπ hint_σπ, klDiv_of_ac_of_integrable hac hint,
    klDiv_of_ac_of_integrable hσπ' hint',
    ← ENNReal.ofReal_add (integral_llr_add_sub_measure_univ_nonneg hac hint)
      (integral_llr_add_sub_measure_univ_nonneg hσπ' hint')]
  congr 1
  have hmass : (π.fitLaw f μ).real univ = μ.real univ := by
    conv_rhs => rw [← map_fitLaw_of_absolutelyContinuous hf hac]
    rw [map_measureReal_apply hf MeasurableSet.univ, preimage_univ]
  rw [integral_congr_ae hllr, integral_add hint_comp hint', hmass,
    ← integral_map hf.aemeasurable (measurable_llr _ _).aestronglyMeasurable, hσ,
    map_measureReal_apply hf MeasurableSet.univ, preimage_univ, ← hσ,
    map_measureReal_apply hf MeasurableSet.univ, preimage_univ]
  ring

/-- The projection `π.fitLaw f μ` lies at relative entropy `klDiv μ (π.map f)` from `π`: fitting
the law of `f` costs exactly the relative entropy of the target law against the current one. -/
theorem klDiv_fitLaw [IsFiniteMeasure π] [IsFiniteMeasure μ] (hf : Measurable f)
    (hμ : μ ≪ π.map f) : klDiv (π.fitLaw f μ) π = klDiv μ (π.map f) := by
  have := isFiniteMeasure_fitLaw (π := π) (μ := μ) hf
  rw [klDiv_eq_klDiv_map_add_klDiv_fitLaw hf (map_fitLaw_of_absolutelyContinuous hf hμ),
    klDiv_self, add_zero]

/-- **Minimality of the relative-entropy projection.** The relative entropy of `π.fitLaw f μ` to
`π` is at most that of any finite measure under which `f` has law `μ`. When `μ ≪ π.map f` the
reweighted measure has law `μ` itself (`map_fitLaw_of_absolutelyContinuous`), so it is a minimiser
over that family; otherwise every such measure has infinite relative entropy to `π`. -/
theorem klDiv_fitLaw_le [IsFiniteMeasure π] [IsFiniteMeasure σ] (hf : Measurable f)
    (hσ : σ.map f = μ) : klDiv (π.fitLaw f μ) π ≤ klDiv σ π := by
  have : IsFiniteMeasure μ := hσ ▸ isFiniteMeasure_map σ f
  rw [klDiv_eq_klDiv_map_add_klDiv_fitLaw hf hσ]
  by_cases hμ : μ ≪ π.map f
  · exact (klDiv_fitLaw hf hμ).trans_le le_self_add
  · simp [hμ]

/-- **Uniqueness of the relative-entropy projection.** A finite measure under which `f` has law
`μ`, at finite relative entropy from `π` no larger than that of the projection, is the projection.
-/
theorem eq_fitLaw_of_klDiv_le [IsFiniteMeasure π] [IsFiniteMeasure σ] (hf : Measurable f)
    (hσ : σ.map f = μ) (h : klDiv σ π ≤ klDiv (π.fitLaw f μ) π) (hne : klDiv σ π ≠ ∞) :
    σ = π.fitLaw f μ := by
  have : IsFiniteMeasure μ := hσ ▸ isFiniteMeasure_map σ f
  have := isFiniteMeasure_fitLaw (π := π) (μ := μ) hf
  have hdecomp := klDiv_eq_klDiv_map_add_klDiv_fitLaw (π := π) hf hσ
  have hμ : μ ≪ π.map f := by
    by_contra hμ
    simp [hdecomp, hμ] at hne
  rw [klDiv_fitLaw hf hμ] at h
  have hfin : klDiv μ (π.map f) ≠ ∞ := ne_top_of_le_ne_top hne (hdecomp ▸ le_self_add)
  refine (klDiv_eq_zero_iff (μ := σ) (ν := π.fitLaw f μ)).1 ?_
  rw [hdecomp] at h
  exact nonpos_iff_eq_zero.1 (ENNReal.le_of_add_le_add_left hfin (h.trans_eq (add_zero _).symm))

end TauCeti
