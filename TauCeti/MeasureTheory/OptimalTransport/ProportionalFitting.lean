/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.Projection
public import TauCeti.MeasureTheory.OptimalTransport.Entropic

/-!
# Iterative proportional fitting

Iterative proportional fitting (IPF), the measure-theoretic form of the Sinkhorn iteration,
approaches the static Schrödinger problem `inf {klDiv π R | π couples μ and ν}` by alternately
enforcing the two marginal constraints. Starting from the reference measure `R` on `X × Y`, each
sweep first reweights the current measure along the first coordinate towards first marginal `μ`,
and then along the second coordinate towards second marginal `ν`. Each half-step is
`MeasureTheory.Measure.fitLaw`; it makes the corresponding marginal equal to its target exactly
when that target is absolutely continuous with respect to the current marginal, and is then the
relative-entropy projection onto the measures with that prescribed marginal.

For every coupling `σ` of `μ` and `ν`, the Pythagorean identity of these projections telescopes:
after `n` sweeps,
`klDiv σ R = ∑_{k < n} (klDiv μ (π_k).fst + klDiv ν (π_k').snd) + klDiv σ π_n`,
where `π_k` is the `k`-th iterate and `π_k'` the measure halfway through the next sweep. The terms
of the sum are the marginal errors of the iteration, measured in relative entropy. Minimising over
`σ`, their total is at most the Schrödinger value. So, as soon as some coupling has finite relative
entropy with respect to `R`, the marginal errors are summable and tend to `0`. Such a coupling also
has finite relative entropy against every iterate and every half-step, so each target marginal is
absolutely continuous with respect to the current one, and every half-step enforces its marginal
exactly. Nothing beyond the measurable structure of `X` and `Y` is used.

## Main definitions

* `MeasureTheory.Measure.proportionalFittingStep π μ ν`: one sweep, fitting the first marginal
  to `μ` and then the second marginal to `ν`.
* `MeasureTheory.Measure.proportionalFitting R μ ν n`: the `n`-th iterate of the sweep, started
  at `R`.

## Main statements

* `TauCeti.klDiv_eq_add_klDiv_proportionalFittingStep`: the Pythagorean identity of one sweep.
* `TauCeti.klDiv_eq_sum_add_klDiv_proportionalFitting`: its telescoped form after `n` sweeps.
* `TauCeti.tsum_klDiv_le_schroedingerValue`: the total marginal error is at most the Schrödinger
  value.
* `TauCeti.tendsto_klDiv_fst_proportionalFitting` and
  `TauCeti.tendsto_klDiv_snd_fitLaw_proportionalFitting`: under finite-entropy feasibility, the
  marginal errors tend to `0`.
* `TauCeti.fst_fitLaw_proportionalFitting` and `TauCeti.snd_proportionalFitting_succ`: under
  finite-entropy feasibility, each half-step enforces its marginal exactly.

## References

* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probability 3 (1975), 146–158, for iterated I-projections onto linear families.
* L. Rüschendorf, *Convergence of the iterative proportional fitting procedure*, Ann. Statist. 23
  (1995), 1160–1174, for the procedure on general measurable spaces.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  for the telescoping identity and the convergence of the marginal errors.
-/

public section

noncomputable section

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace MeasureTheory.Measure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {R π : Measure (X × Y)}
  {μ : Measure X} {ν : Measure Y}

/-- One sweep of iterative proportional fitting: the measure `π` is reweighted along the first
coordinate towards first marginal `μ`, and then along the second coordinate towards second
marginal `ν`. Each reweighting makes its marginal equal to the target when the target is
absolutely continuous with respect to the current marginal
(`MeasureTheory.Measure.map_fitLaw_of_absolutelyContinuous`); under finite-entropy feasibility this
holds along the whole iteration (`TauCeti.fst_fitLaw_proportionalFitting`,
`TauCeti.snd_proportionalFitting_succ`). -/
def proportionalFittingStep (π : Measure (X × Y)) (μ : Measure X) (ν : Measure Y) :
    Measure (X × Y) :=
  (π.fitLaw Prod.fst μ).fitLaw Prod.snd ν

theorem proportionalFittingStep_def (π : Measure (X × Y)) (μ : Measure X) (ν : Measure Y) :
    π.proportionalFittingStep μ ν = (π.fitLaw Prod.fst μ).fitLaw Prod.snd ν :=
  (rfl)

/-- The iterates of iterative proportional fitting started at the reference measure `R`: the
`n`-th one is obtained from `R` by `n` sweeps `MeasureTheory.Measure.proportionalFittingStep`
towards `μ` and `ν`. -/
def proportionalFitting (R : Measure (X × Y)) (μ : Measure X) (ν : Measure Y) (n : ℕ) :
    Measure (X × Y) :=
  (fun π ↦ π.proportionalFittingStep μ ν)^[n] R

@[simp]
theorem proportionalFitting_zero : R.proportionalFitting μ ν 0 = R :=
  (rfl)

@[simp]
theorem proportionalFitting_succ (n : ℕ) :
    R.proportionalFitting μ ν (n + 1) = (R.proportionalFitting μ ν n).proportionalFittingStep μ ν :=
  Function.iterate_succ_apply' _ _ _

/-- A sweep is finite as soon as `ν` is: it ends by fitting the second marginal to `ν`, and the
total mass after that fit is at most the mass of `ν`, whatever measure it is applied to. -/
instance [IsFiniteMeasure ν] : IsFiniteMeasure (π.proportionalFittingStep μ ν) :=
  isFiniteMeasure_fitLaw measurable_snd

/-- Every iterate is finite when `R` and `ν` are: the zeroth iterate is `R`, and every later one is
a sweep, which is finite because `ν` is. -/
instance [IsFiniteMeasure R] [IsFiniteMeasure ν] (n : ℕ) :
    IsFiniteMeasure (R.proportionalFitting μ ν n) := by
  cases n with
  | zero => rwa [proportionalFitting_zero]
  | succ n => rw [proportionalFitting_succ]; infer_instance

end MeasureTheory.Measure

namespace TauCeti

open Measure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {R π σ : Measure (X × Y)}
  {μ : Measure X} {ν : Measure Y}

/-- **Pythagorean identity of one sweep.** For a coupling `σ` of `μ` and `ν`, the relative entropy
of `σ` against `π` splits into the relative-entropy errors of the first marginal of `π` and of the
second marginal of the half-step `π.fitLaw Prod.fst μ`, plus the relative entropy of `σ` against
the sweep `π.proportionalFittingStep μ ν`. -/
theorem klDiv_eq_add_klDiv_proportionalFittingStep [IsFiniteMeasure π] [IsFiniteMeasure σ]
    (hσ : IsCoupling σ μ ν) :
    klDiv σ π = klDiv μ π.fst + klDiv ν (π.fitLaw Prod.fst μ).snd +
      klDiv σ (π.proportionalFittingStep μ ν) := by
  have : IsFiniteMeasure μ := hσ.fst_eq ▸ inferInstance
  have := Measure.isFiniteMeasure_fitLaw (π := π) (μ := μ) measurable_fst
  rw [klDiv_eq_klDiv_map_add_klDiv_fitLaw measurable_fst hσ.measurePreserving_fst.map_eq,
    klDiv_eq_klDiv_map_add_klDiv_fitLaw (π := π.fitLaw Prod.fst μ) measurable_snd
      hσ.measurePreserving_snd.map_eq, add_assoc, proportionalFittingStep_def, Measure.fst,
    Measure.snd]

/-- **Telescoping identity of iterative proportional fitting.** For a coupling `σ` of `μ` and `ν`,
after `n` sweeps the relative entropy of `σ` against the reference `R` is the sum of the
relative-entropy marginal errors met along the way plus the relative entropy of `σ` against the
`n`-th iterate. -/
theorem klDiv_eq_sum_add_klDiv_proportionalFitting [IsFiniteMeasure R] [IsFiniteMeasure σ]
    (hσ : IsCoupling σ μ ν) (n : ℕ) :
    klDiv σ R = ∑ k ∈ Finset.range n, (klDiv μ (proportionalFitting R μ ν k).fst +
      klDiv ν ((proportionalFitting R μ ν k).fitLaw Prod.fst μ).snd) +
      klDiv σ (proportionalFitting R μ ν n) := by
  have : IsFiniteMeasure ν := hσ.snd_eq ▸ inferInstance
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, klDiv_eq_add_klDiv_proportionalFittingStep hσ, ← proportionalFitting_succ,
      Finset.sum_range_succ]
    ring

/-- Along the iteration, the relative entropy of every coupling of `μ` and `ν` to the iterates
decreases. -/
theorem klDiv_proportionalFitting_antitone [IsFiniteMeasure R] [IsFiniteMeasure σ]
    (hσ : IsCoupling σ μ ν) : Antitone fun n ↦ klDiv σ (proportionalFitting R μ ν n) := by
  have : IsFiniteMeasure ν := hσ.snd_eq ▸ inferInstance
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [klDiv_eq_add_klDiv_proportionalFittingStep (π := proportionalFitting R μ ν n) hσ,
    ← proportionalFitting_succ]
  exact le_add_self

/-- **The marginal errors are bounded by the Schrödinger value.** The relative-entropy errors of
the two marginals, summed over all sweeps of iterative proportional fitting started at `R`, are at
most the value of the static Schrödinger problem with reference `R`. -/
theorem tsum_klDiv_le_schroedingerValue [IsFiniteMeasure R] [IsFiniteMeasure μ] :
    ∑' k, (klDiv μ (proportionalFitting R μ ν k).fst +
      klDiv ν ((proportionalFitting R μ ν k).fitLaw Prod.fst μ).snd) ≤
      schroedingerValue R μ ν := by
  refine le_schroedingerValue fun σ hσ ↦ ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  have := hσ.isFiniteMeasure
  rw [klDiv_eq_sum_add_klDiv_proportionalFitting hσ n]
  exact le_self_add

/-- Under finite-entropy feasibility, the relative-entropy error of the first marginal of the
iterates of iterative proportional fitting tends to `0`. -/
theorem tendsto_klDiv_fst_proportionalFitting [IsFiniteMeasure R] [IsFiniteMeasure μ]
    (h : schroedingerValue R μ ν ≠ ∞) :
    Tendsto (fun n ↦ klDiv μ (proportionalFitting R μ ν n).fst) atTop (𝓝 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top <| ne_top_of_le_ne_top h <|
    (ENNReal.tsum_le_tsum fun _ ↦ le_self_add).trans tsum_klDiv_le_schroedingerValue

/-- Under finite-entropy feasibility, the relative-entropy error of the second marginal halfway
through each sweep of iterative proportional fitting tends to `0`. -/
theorem tendsto_klDiv_snd_fitLaw_proportionalFitting [IsFiniteMeasure R] [IsFiniteMeasure μ]
    (h : schroedingerValue R μ ν ≠ ∞) :
    Tendsto (fun n ↦ klDiv ν ((proportionalFitting R μ ν n).fitLaw Prod.fst μ).snd) atTop
      (𝓝 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top <| ne_top_of_le_ne_top h <|
    (ENNReal.tsum_le_tsum fun _ ↦ le_add_self).trans tsum_klDiv_le_schroedingerValue

/-- A coupling of finite relative entropy against the reference has finite relative entropy
against every iterate, and against the measure halfway through every sweep. -/
private theorem klDiv_ne_top_proportionalFitting [IsFiniteMeasure R] [IsFiniteMeasure σ]
    (hσ : IsCoupling σ μ ν) (h : klDiv σ R ≠ ∞) (n : ℕ) :
    klDiv σ (proportionalFitting R μ ν n) ≠ ∞ ∧
      klDiv σ ((proportionalFitting R μ ν n).fitLaw Prod.fst μ) ≠ ∞ := by
  have : IsFiniteMeasure ν := hσ.snd_eq ▸ inferInstance
  have hn : klDiv σ (proportionalFitting R μ ν n) ≠ ∞ := by
    refine ne_top_of_le_ne_top h ?_
    rw [klDiv_eq_sum_add_klDiv_proportionalFitting (R := R) hσ n]
    exact le_add_self
  refine ⟨hn, ne_top_of_le_ne_top hn ?_⟩
  rw [klDiv_eq_klDiv_map_add_klDiv_fitLaw (π := proportionalFitting R μ ν n) measurable_fst
    hσ.measurePreserving_fst.map_eq]
  exact le_add_self

/-- Under finite-entropy feasibility, the first half of every sweep of iterative proportional
fitting gives first marginal exactly `μ`. -/
@[simp]
theorem fst_fitLaw_proportionalFitting [IsFiniteMeasure R] [IsFiniteMeasure μ]
    (h : schroedingerValue R μ ν ≠ ∞) (n : ℕ) :
    ((proportionalFitting R μ ν n).fitLaw Prod.fst μ).fst = μ := by
  obtain ⟨σ, hσ, hσR⟩ := schroedingerValue_lt_iff.1 h.lt_top
  have := hσ.isFiniteMeasure
  have : IsFiniteMeasure ν := hσ.snd_eq ▸ inferInstance
  have hac : σ ≪ proportionalFitting R μ ν n :=
    (klDiv_ne_top_iff.1 (klDiv_ne_top_proportionalFitting hσ hσR.ne n).1).1
  rw [Measure.fst]
  refine Measure.map_fitLaw_of_absolutelyContinuous measurable_fst ?_
  have := hac.map measurable_fst
  rwa [hσ.measurePreserving_fst.map_eq] at this

/-- Under finite-entropy feasibility, every sweep of iterative proportional fitting ends with second
marginal exactly `ν`. -/
theorem snd_proportionalFitting_succ [IsFiniteMeasure R] [IsFiniteMeasure μ]
    (h : schroedingerValue R μ ν ≠ ∞) (n : ℕ) : (proportionalFitting R μ ν (n + 1)).snd = ν := by
  obtain ⟨σ, hσ, hσR⟩ := schroedingerValue_lt_iff.1 h.lt_top
  have := hσ.isFiniteMeasure
  have : IsFiniteMeasure ν := hσ.snd_eq ▸ inferInstance
  have := Measure.isFiniteMeasure_fitLaw (π := proportionalFitting R μ ν n) (μ := μ)
    measurable_fst
  have hac : σ ≪ (proportionalFitting R μ ν n).fitLaw Prod.fst μ :=
    (klDiv_ne_top_iff.1 (klDiv_ne_top_proportionalFitting hσ hσR.ne n).2).1
  rw [proportionalFitting_succ, proportionalFittingStep_def, Measure.snd]
  refine Measure.map_fitLaw_of_absolutelyContinuous measurable_snd ?_
  have := hac.map measurable_snd
  rwa [hσ.measurePreserving_snd.map_eq] at this

end TauCeti
