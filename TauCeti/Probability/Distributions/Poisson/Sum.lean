/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Finite sums of independent Poisson variables

The sum of independent Poisson counts is Poisson with rate equal to the sum of their rates.
The native natural-number law is given both for random variables and as a product-measure
pushforward. Empty families and zero rates are included, as needed when conditioning on a
Poisson total or allocating a total among categories.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*}

/-- The sum of a finite independent family of Poisson variables is Poisson with rate equal
to the sum of the rates. Only the variables indexed by `s` need carry a Poisson law.
Empty families and zero rates are included. -/
theorem _root_.ProbabilityTheory.iIndepFun.hasLaw_sum_poissonMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    {s : Finset ι} (hindep : iIndepFun X P)
    (hlaw : ∀ i ∈ s, HasLaw (X i) (poissonMeasure (r i)) P) :
    HasLaw (fun ω => ∑ i ∈ s, X i ω) (poissonMeasure (∑ i ∈ s, r i)) P := by
  classical
  let _ := hindep.isProbabilityMeasure
  have hmeas : AEMeasurable (fun ω => ∑ i ∈ s, X i ω) P :=
    Finset.aemeasurable_fun_sum _ fun i hi => (hlaw i hi).aemeasurable
  refine ⟨hmeas, measure_eq_of_pgf_eqOn fun z hz => ?_⟩
  rw [pgf_map hmeas]
  have hsum := iIndepFun.pgf_sum_of_abs_le_one hindep s
    (fun i hi => (hlaw i hi).aemeasurable) (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)
  have hfun : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
    funext ω
    exact (Finset.sum_apply ω s X).symm
  rw [hfun, hsum]
  rw [Finset.prod_congr rfl (fun i hi => HasLaw.pgf_eq (hlaw i hi) z)]
  simp_rw [pgf_poissonMeasure]
  rw [← Real.exp_sum, ← Finset.sum_mul, NNReal.coe_sum]

/-- The sum pushforward of independent Poisson laws has rate equal to the sum of their rates. -/
@[simp]
theorem map_sum_pi_poissonMeasure [Fintype ι] (r : ι → ℝ≥0) :
    (Measure.pi (fun i => poissonMeasure (r i))).map (fun k => ∑ i, k i) =
      poissonMeasure (∑ i, r i) := by
  have hindep : iIndepFun (fun i (k : ι → ℕ) => k i)
      (Measure.pi (fun i => poissonMeasure (r i))) :=
    iIndepFun_pi (X := fun _ => (id : ℕ → ℕ)) fun _ => aemeasurable_id
  exact (hindep.hasLaw_sum_poissonMeasure (s := Finset.univ)
    (fun i _ => (measurePreserving_eval (fun i => poissonMeasure (r i)) i).hasLaw)).map_eq

end TauCeti.Probability
