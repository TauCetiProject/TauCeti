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

The proof uses the existing probability-generating-function multiplicativity and uniqueness
theorems, together with `pgf_poissonMeasure`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The sum of a finite independent family of Poisson variables is Poisson with rate equal
to the sum of the rates. Empty families and zero rates are included. -/
theorem _root_.ProbabilityTheory.iIndepFun.hasLaw_sum_poissonMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) (poissonMeasure (r i)) P) :
    HasLaw (fun ω => ∑ i, X i ω) (poissonMeasure (∑ i, r i)) P := by
  classical
  let _ := hindep.isProbabilityMeasure
  have hmeas : AEMeasurable (fun ω => ∑ i, X i ω) P :=
    Finset.aemeasurable_fun_sum _ fun i _ => (hlaw i).aemeasurable
  refine ⟨hmeas, measure_eq_of_pgf_eqOn fun z hz => ?_⟩
  rw [pgf_map hmeas]
  have hsum := iIndepFun.pgf_sum_of_abs_le_one hindep Finset.univ
    (fun i _ => (hlaw i).aemeasurable) (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)
  have hfun : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    exact (Fintype.sum_apply ω X).symm
  rw [hfun, hsum]
  simp_rw [HasLaw.pgf_eq (hlaw _), pgf_poissonMeasure]
  rw [← Real.exp_sum, ← Finset.sum_mul, NNReal.coe_sum]

/-- The sum pushforward of independent Poisson laws has rate equal to the sum of their rates. -/
@[simp]
theorem map_sum_pi_poissonMeasure (r : ι → ℝ≥0) :
    (Measure.pi (fun i => poissonMeasure (r i))).map (fun k => ∑ i, k i) =
      poissonMeasure (∑ i, r i) := by
  have hindep : iIndepFun (fun i (k : ι → ℕ) => k i)
      (Measure.pi (fun i => poissonMeasure (r i))) :=
    iIndepFun_pi (X := fun _ => (id : ℕ → ℕ)) fun _ => aemeasurable_id
  exact (hindep.hasLaw_sum_poissonMeasure
    (fun i => (measurePreserving_eval (fun i => poissonMeasure (r i)) i).hasLaw)).map_eq

end TauCeti.Probability
