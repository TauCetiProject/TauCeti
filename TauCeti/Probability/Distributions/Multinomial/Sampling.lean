/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Pi
public import TauCeti.Probability.Distributions.Categorical.Basic
public import TauCeti.Probability.Distributions.Multinomial.Poisson
public import TauCeti.Probability.Distributions.Multinomial.Transforms
public import TauCeti.Probability.Independence.ConvolutionPower

/-!
# Counts in independent categorical samples

The count vector of a finite i.i.d. categorical sample has the multinomial law. If the
sample size is an independent Poisson variable, the category counts instead have the
product of their Poisson laws. This is the independent-count calculation behind the
construction of a finite Poisson random measure from independent locations.

Counts retain repeated occurrences. Zero trials, zero Poisson rate and zero-weight
categories are included. The random-size theorem requires independence from the entire
sequence, not merely pairwise independence from its coordinates.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 3 (Poisson sampling).
* N. L. Johnson, S. Kotz and N. Balakrishnan, *Discrete Multivariate Distributions*,
  Wiley, 1997, Chapter 35 (multinomial sampling).
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Summing `n` independent one-trial multinomial vectors gives the `n`-trial law. -/
@[simp]
theorem convolutionPower_multinomialMeasure_one (n : ℕ) (p : StdSimplex ℝ≥0 ι) :
    (multinomialMeasure 1 p).convolutionPower n = multinomialMeasure n p := by
  let f : (ι → ℕ) →+ EuclideanSpace ℝ ι :=
    { toFun := multinomialToEuclidean
      map_zero' := by ext; simp [multinomialToEuclidean_apply]
      map_add' := by intros; ext; simp [multinomialToEuclidean_apply] }
  apply (measurableEmbedding_multinomialToEuclidean (ι := ι)).map_injective
  let := isProbabilityMeasure_multinomialMeasure 1 p
  let := isProbabilityMeasure_multinomialMeasure n p
  have hmap : ((multinomialMeasure 1 p).convolutionPower n).map multinomialToEuclidean =
      ((multinomialMeasure 1 p).map multinomialToEuclidean).convolutionPower n :=
    Measure.map_convolutionPower _ f measurable_multinomialToEuclidean n
  rw [hmap]
  apply Measure.ext_of_charFun
  funext t
  rw [Measure.charFun_convolutionPower,
    charFun_map_multinomialToEuclidean_multinomialMeasure,
    charFun_map_multinomialToEuclidean_multinomialMeasure]
  simp

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω ι J : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] {P : Measure Ω}
  {p : StdSimplex ℝ≥0 ι}

/-- Counts in a finite independent categorical sample have the multinomial law.
The finite set of trial indices may be empty. -/
theorem iIndepFun.hasLaw_card_filter_multinomialMeasure {X : J → Ω → ι}
    (hind : iIndepFun X P) (hX : ∀ j, HasLaw (X j) (categoricalMeasure p) P)
    (s : Finset J) :
    HasLaw (fun ω i => (s.filter fun j => X j ω = i).card)
      (multinomialMeasure s.card p) P := by
  classical
  have := hind.isProbabilityMeasure
  let := isProbabilityMeasure_multinomialMeasure 1 p
  let Y (j : J) (ω : Ω) : ι → ℕ := Pi.single (X j ω) 1
  have hY (j : J) : HasLaw (Y j) (multinomialMeasure 1 p) P :=
    (hasLaw_piSingle_categoricalMeasure p).comp (hX j)
  have hsum := (hind.comp (fun _ i => Pi.single i (1 : ℕ))
    (fun _ => measurable_of_countable _)).hasLaw_finset_sum_convolutionPower hY s
  rw [convolutionPower_multinomialMeasure_one] at hsum
  convert hsum using 1
  funext ω
  simpa only [Finset.sum_apply, Function.comp_def] using
    (s.sum_pi_single_one_eq_card_filter (fun j => X j ω)).symm

/-- Counts in an i.i.d. categorical sequence stopped at an independent natural-valued
sample size have the corresponding mixture of multinomial laws. -/
theorem iIndepFun.hasLaw_card_filter_bind_multinomialMeasure
    {X : ℕ → Ω → ι} {N : Ω → ℕ} {ρ : Measure ℕ} (hind : iIndepFun X P)
    (hX : ∀ j, HasLaw (X j) (categoricalMeasure p) P)
    (hN : HasLaw N ρ P) (hNX : IndepFun N (fun ω j => X j ω) P) :
    HasLaw (fun ω i => ((Finset.range (N ω)).filter fun j => X j ω = i).card)
      (ρ.bind fun n => multinomialMeasure n p) P := by
  classical
  let Y (j : ℕ) (ω : Ω) : ι → ℕ := Pi.single (X j ω) 1
  have hY (j : ℕ) : HasLaw (Y j) (multinomialMeasure 1 p) P :=
    (hasLaw_piSingle_categoricalMeasure p).comp (hX j)
  have hNY : IndepFun N (fun ω j => Y j ω) P :=
    hNX.comp measurable_id (measurable_pi_iff.2 fun j =>
      (measurable_of_countable (fun i : ι => Pi.single i (1 : ℕ))).comp
        (measurable_pi_apply j))
  have hsum := (hind.comp (fun _ i => Pi.single i (1 : ℕ))
    (fun _ => measurable_of_countable _)).hasLaw_sum_range_bind hY hN hNY
  have hpowers : (multinomialMeasure 1 p).convolutionPower =
      fun n => multinomialMeasure n p :=
    funext fun n => convolutionPower_multinomialMeasure_one n p
  rw [hpowers] at hsum
  simpa only [Function.comp_def, Finset.sum_pi_single_one_eq_card_filter] using hsum

/-- Counts in an i.i.d. categorical sequence stopped at an independent Poisson sample size
have the product of Poisson laws. Zero rates and zero-weight categories are allowed. -/
theorem iIndepFun.hasLaw_card_filter_pi_poissonMeasure {X : ℕ → Ω → ι} {N : Ω → ℕ}
    {r : ℝ≥0} (hind : iIndepFun X P)
    (hX : ∀ j, HasLaw (X j) (categoricalMeasure p) P)
    (hN : HasLaw N (poissonMeasure r) P) (hNX : IndepFun N (fun ω j => X j ω) P) :
    HasLaw (fun ω i => ((Finset.range (N ω)).filter fun j => X j ω = i).card)
      (Measure.pi fun i => poissonMeasure (r * p.weights i)) P := by
  simpa only [bind_poissonMeasure_multinomialMeasure] using
    hind.hasLaw_card_filter_bind_multinomialMeasure hX hN hNX

/-- Poisson sampling makes all category counts jointly independent, even for categories
with zero probability. -/
theorem iIndepFun.iIndepFun_card_filter_of_hasLaw_poissonMeasure {X : ℕ → Ω → ι} {N : Ω → ℕ}
    {r : ℝ≥0} (hind : iIndepFun X P)
    (hX : ∀ j, HasLaw (X j) (categoricalMeasure p) P)
    (hN : HasLaw N (poissonMeasure r) P) (hNX : IndepFun N (fun ω j => X j ω) P) :
    iIndepFun (fun i ω => ((Finset.range (N ω)).filter fun j => X j ω = i).card) P := by
  exact (hind.hasLaw_card_filter_bind_multinomialMeasure hX hN hNX).iIndepFun_of_poisson_multinomial

end ProbabilityTheory

namespace TauCeti.Probability

variable {ι J : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Counting categories under a finite product of categorical laws gives the multinomial
law. This includes the empty product of trials. -/
@[simp]
theorem map_card_filter_pi_categoricalMeasure [Fintype J] (p : StdSimplex ℝ≥0 ι) :
    (Measure.pi fun _ : J => categoricalMeasure p).map
      (fun x i => (Finset.univ.filter fun j => x j = i).card) =
        multinomialMeasure (Fintype.card J) p := by
  simpa using ((iIndepFun_pi (μ := fun _ : J => categoricalMeasure p)
    (fun _ => aemeasurable_id)).hasLaw_card_filter_multinomialMeasure
      (fun j => (measurePreserving_eval (fun _ : J => categoricalMeasure p) j).hasLaw)
        Finset.univ).map_eq

/-- Independently drawing a Poisson sample size and an infinite categorical sequence,
then counting the selected prefix, gives independent Poisson category counts. -/
@[simp]
theorem map_card_filter_prod_poissonMeasure (r : ℝ≥0) (p : StdSimplex ℝ≥0 ι) :
    ((poissonMeasure r).prod (Measure.infinitePi fun _ : ℕ => categoricalMeasure p)).map
      (fun z i => ((Finset.range z.1).filter fun j => z.2 j = i).card) =
        Measure.pi (fun i => poissonMeasure (r * p.weights i)) := by
  let μ := Measure.infinitePi fun _ : ℕ => categoricalMeasure p
  have hsnd := (measurePreserving_snd (μ := poissonMeasure r) (ν := μ)).hasLaw
  have hX (j : ℕ) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => categoricalMeasure p) j).hasLaw.comp hsnd
  have hind : iIndepFun (fun j (z : ℕ × (ℕ → ι)) => z.2 j)
      ((poissonMeasure r).prod μ) :=
    (iIndepFun_iff_hasLaw_Pi_infinitePi hX measurable_snd.aemeasurable).2 hsnd
  exact (hind.hasLaw_card_filter_pi_poissonMeasure hX
    (measurePreserving_fst (μ := poissonMeasure r) (ν := μ)).hasLaw
    (indepFun_prod measurable_id measurable_id)).map_eq

end TauCeti.Probability
