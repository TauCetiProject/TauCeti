/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# The extremes of a finite independent family

Let `X : ι → Ω → ℝ` be an independent family over a nonempty finite index type, with
member `X i` having law `μ i`. This file computes the law of the two extremes of the family: the
maximum `Finset.univ.sup' Finset.univ_nonempty fun i => X i ω` and the minimum
`Finset.univ.inf' Finset.univ_nonempty fun i => X i ω`. Their cumulative distribution functions
are the product of the marginal cdfs and one minus the product of their survival probabilities.

For an identically distributed family with common law `μ`, writing `d = Fintype.card ι`, these
specialize to `(cdf μ x) ^ d` and `1 - (1 - cdf μ x) ^ d`.

Both extremes are taken over `Finset.univ` together with its nonemptiness proof, so neither
formula acquires the default value that an empty family would force on a `Finset.sup` or a
`Finset.inf`: `d = 0` never occurs.

**One event identity does the work.** The maximum is at most `x` exactly when every member is
(`Finset.sup'_le_iff`), and `x` is below the minimum exactly when it is below every member
(`Finset.lt_inf'_iff`). Independence turns each of those intersections into the product of the
corresponding marginal probabilities. The minimum is then read off its complementary event,
which is why its formula has an outer subtraction.

`cdf_min_iid` specialises to the exponential family as `hasLaw_min_iid_expMeasure`: the minimum
of `d` i.i.d. exponentials of rate `r` is exponential of rate `d * r`.

## Main results

* `TauCeti.Probability.cdf_max_indep`, `TauCeti.Probability.cdf_min_indep` — the cdfs of the
  extremes as products of the marginal cdfs or survival probabilities;
* `TauCeti.Probability.cdf_max_iid`, `TauCeti.Probability.cdf_min_iid` — the corresponding powers
  for a common marginal law.

The other order statistics are in `TauCeti.Probability.Distributions.OrderStatistic.Basic`, where
`TauCeti.orderStatistic_zero` and `TauCeti.orderStatistic_last` identify
the minimum and the maximum as the extreme order statistics.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Fintype ι] [Nonempty ι] {P : Measure Ω}
  {μ : Measure ℝ} {μs : ι → Measure ℝ} {X : ι → Ω → ℝ} {r : ℝ}

/-- The maximum of a finite family is at most `x` exactly when every member is. -/
private theorem setOf_max_le (X : ι → Ω → ℝ) (x : ℝ) :
    {ω | (Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) ≤ x}
      = ⋂ i ∈ (Finset.univ : Finset ι), X i ⁻¹' Iic x := by
  ext ω
  simp [Finset.sup'_le_iff]

/-- The minimum of a finite family exceeds `x` exactly when every member does. -/
private theorem setOf_lt_min (X : ι → Ω → ℝ) (x : ℝ) :
    {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω}
      = ⋂ i ∈ (Finset.univ : Finset ι), X i ⁻¹' Ioi x := by
  ext ω
  simp [Finset.lt_inf'_iff]

/-- The maximum of a finite independent family is at most `x` with probability equal to the
product of the marginal lower-tail probabilities. -/
theorem measure_setOf_max_le_indep (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μs i) P) (x : ℝ) :
    P {ω | (Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) ≤ x} =
      ∏ i, μs i (Iic x) := by
  rw [setOf_max_le,
    hindep.measure_inter_preimage_eq_mul Finset.univ (sets := fun _ => Iic x)
      fun i _ => measurableSet_Iic]
  exact Finset.prod_congr rfl fun i _ =>
    (hlaw i).measure_eq (p := fun y => y ≤ x) measurableSet_Iic

/-- The minimum of a finite independent family exceeds `x` with probability equal to the product
of the marginal upper-tail probabilities. -/
theorem measure_setOf_lt_min_indep (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μs i) P) (x : ℝ) :
    P {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω} =
      ∏ i, μs i (Ioi x) := by
  rw [setOf_lt_min,
    hindep.measure_inter_preimage_eq_mul Finset.univ (sets := fun _ => Ioi x)
      fun i _ => measurableSet_Ioi]
  exact Finset.prod_congr rfl fun i _ =>
    (hlaw i).measure_eq (p := fun y => x < y) measurableSet_Ioi

/-- The real-valued lower-tail formula for the maximum of a finite independent family. -/
theorem measureReal_setOf_max_le_indep [∀ i, IsProbabilityMeasure (μs i)]
    (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) (μs i) P) (x : ℝ) :
    P.real {ω | (Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) ≤ x} =
      ∏ i, cdf (μs i) x := by
  rw [measureReal_def, measure_setOf_max_le_indep hindep hlaw x, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [← measureReal_def, ← cdf_eq_real]

/-- The real-valued upper-tail formula for the minimum of a finite independent family. -/
theorem measureReal_setOf_lt_min_indep [∀ i, IsProbabilityMeasure (μs i)]
    (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) (μs i) P) (x : ℝ) :
    P.real {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω} =
      ∏ i, (1 - cdf (μs i) x) := by
  have _ : IsProbabilityMeasure P := (hlaw (Classical.arbitrary ι)).isProbabilityMeasure
  rw [measureReal_def, measure_setOf_lt_min_indep hindep hlaw x, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [← measureReal_def, ← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
      ← cdf_eq_real]

/-- The minimum of a finite independent family is at most `x` with probability one minus the
product of the marginal upper-tail probabilities. -/
theorem measureReal_setOf_min_le_indep [∀ i, IsProbabilityMeasure (μs i)]
    (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) (μs i) P) (x : ℝ) :
    P.real {ω | (Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) ≤ x} =
      1 - ∏ i, (1 - cdf (μs i) x) := by
  have _ : IsProbabilityMeasure P := (hlaw (Classical.arbitrary ι)).isProbabilityMeasure
  have hcompl : {ω | (Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) ≤ x} =
      {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω}ᶜ := by
    ext ω
    simp
  have hmin : AEMeasurable (fun ω => Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) P := by
    simp_rw [Finset.inf'_univ_eq_ciInf]
    exact AEMeasurable.iInf fun i => (hlaw i).aemeasurable
  have hnull : NullMeasurableSet
      {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω} P :=
    hmin.nullMeasurableSet_preimage measurableSet_Ioi
  rw [hcompl, measureReal_compl₀ hnull, probReal_univ,
    measureReal_setOf_lt_min_indep hindep hlaw x]

/-- The maximum of an independent identically distributed finite family is at most `x` with
probability the `Fintype.card ι`-th power of the common lower-tail probability. -/
theorem measure_setOf_max_le_iid (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    P {ω | (Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) ≤ x}
      = μ (Iic x) ^ Fintype.card ι := by
  simpa [Finset.card_univ] using
    measure_setOf_max_le_indep (μs := fun _ : ι => μ) hindep hlaw x

/-- The minimum of an independent identically distributed finite family exceeds `x` with
probability the `Fintype.card ι`-th power of the common upper-tail probability. -/
theorem measure_setOf_lt_min_iid (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    P {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω}
      = μ (Ioi x) ^ Fintype.card ι := by
  simpa [Finset.card_univ] using
    measure_setOf_lt_min_indep (μs := fun _ : ι => μ) hindep hlaw x

/-- The real-valued form of `TauCeti.Probability.measure_setOf_max_le_iid`: the maximum of `d`
independent identically distributed variables has cumulative distribution function
`(cdf μ x) ^ d`. -/
theorem measureReal_setOf_max_le_iid [IsProbabilityMeasure μ] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    P.real {ω | (Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) ≤ x}
      = cdf μ x ^ Fintype.card ι := by
  let _ : ∀ _ : ι, IsProbabilityMeasure μ := fun _ => inferInstance
  simpa [Finset.card_univ] using
    measureReal_setOf_max_le_indep (μs := fun _ : ι => μ) hindep hlaw x

/-- The real-valued form of `TauCeti.Probability.measure_setOf_lt_min_iid`: the minimum of `d`
independent identically distributed variables exceeds `x` with probability
`(1 - cdf μ x) ^ d`. -/
theorem measureReal_setOf_lt_min_iid [IsProbabilityMeasure μ] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    P.real {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω}
      = (1 - cdf μ x) ^ Fintype.card ι := by
  let _ : ∀ _ : ι, IsProbabilityMeasure μ := fun _ => inferInstance
  simpa [Finset.card_univ] using
    measureReal_setOf_lt_min_indep (μs := fun _ : ι => μ) hindep hlaw x

/-- The minimum of `d` independent identically distributed variables has cumulative distribution
function `1 - (1 - cdf μ x) ^ d`. -/
theorem measureReal_setOf_min_le_iid [IsProbabilityMeasure μ] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    P.real {ω | (Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) ≤ x}
      = 1 - (1 - cdf μ x) ^ Fintype.card ι := by
  let _ : ∀ _ : ι, IsProbabilityMeasure μ := fun _ => inferInstance
  simpa [Finset.card_univ] using
    measureReal_setOf_min_le_indep (μs := fun _ : ι => μ) hindep hlaw x

/-- The cdf of the maximum of a finite independent family is the product of the marginal cdfs. -/
theorem cdf_max_indep [∀ i, IsProbabilityMeasure (μs i)] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μs i) P) (x : ℝ) :
    cdf (P.map fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) x =
      ∏ i, cdf (μs i) x := by
  have hmax : AEMeasurable (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) P := by
    simp_rw [Finset.sup'_univ_eq_ciSup]
    exact AEMeasurable.iSup fun i => (hlaw i).aemeasurable
  have _ : IsProbabilityMeasure P := (hlaw (Classical.arbitrary ι)).isProbabilityMeasure
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hmax measurableSet_Iic,
    ← measureReal_setOf_max_le_indep hindep hlaw x]
  rfl

/-- The cdf of the minimum of a finite independent family is one minus the product of the
marginal survival probabilities. -/
theorem cdf_min_indep [∀ i, IsProbabilityMeasure (μs i)] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μs i) P) (x : ℝ) :
    cdf (P.map fun ω => Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) x =
      1 - ∏ i, (1 - cdf (μs i) x) := by
  have hmin : AEMeasurable (fun ω => Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) P := by
    simp_rw [Finset.inf'_univ_eq_ciInf]
    exact AEMeasurable.iInf fun i => (hlaw i).aemeasurable
  have _ : IsProbabilityMeasure P := (hlaw (Classical.arbitrary ι)).isProbabilityMeasure
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hmin measurableSet_Iic,
    ← measureReal_setOf_min_le_indep hindep hlaw x]
  rfl

/-- The law of the maximum of `d` independent identically distributed variables, in cumulative
distribution function form. -/
theorem cdf_max_iid [IsProbabilityMeasure μ] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    cdf (P.map fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) x
      = cdf μ x ^ Fintype.card ι := by
  let _ : ∀ _ : ι, IsProbabilityMeasure μ := fun _ => inferInstance
  simpa [Finset.card_univ] using
    cdf_max_indep (μs := fun _ : ι => μ) hindep hlaw x

/-- The law of the minimum of `d` independent identically distributed variables, in cumulative
distribution function form. -/
theorem cdf_min_iid [IsProbabilityMeasure μ] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    cdf (P.map fun ω => Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) x
      = 1 - (1 - cdf μ x) ^ Fintype.card ι := by
  let _ : ∀ _ : ι, IsProbabilityMeasure μ := fun _ => inferInstance
  simpa [Finset.card_univ] using
    cdf_min_indep (μs := fun _ : ι => μ) hindep hlaw x

end Probability

end TauCeti
