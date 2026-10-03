/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: √2
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Regularity
import TauCeti.Combinatorics.DenseGraphLimits.Graphon.OfMatrix
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Block averaging with a nonempty null cell

On a three-point carrier, put mass `1/2` at each of `0` and `1` and no mass at `2`.
The complete adjacency matrix has value `1` between distinct points, including between the
null atom and the positive atoms. Split off `{2}`, then refine the positive cell into singletons.
The coarse energy is `1/4`, the fine energy is `1/2`, and both the coarse approximation defect
and the refinement increment have squared `L²` seminorm `1/4`.

These computed values test the zero convention for rectangle averages separately from their
weighted energy: averaging erases edges incident to `2` strictly, while the null cell contributes
nothing to the integrals. The Pythagoras and energy-increment identities are exercised on these
partitions, together with a genuinely bad cut and the part-count bound of weak regularity.
The exported witness `stepGraphonAvg_not_injective_bernoulliMeasure` shows that averaging over
singletons need not recover a strict graphon when the carrier has a zero-mass atom.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace TauCeti.DenseGraphLimits

private abbrev weights : Measure (Fin 3) :=
  bernoulliMeasure 0 1 ⟨1 / 2, by norm_num, by norm_num⟩

private def adjacency : Graphon (Fin 3) weights :=
  Graphon.ofMatrix weights (fun i j ↦ if i = j then 0 else 1) (by
    intro i j
    simp [eq_comm])

private theorem adjacency_apply (i j : Fin 3) :
    adjacency i j = if i = j then 0 else 1 := by
  rw [adjacency, Graphon.ofMatrix_apply]
  split <;> rfl

private def coarse : Finpartition (univ : Set (Fin 3)) := Finpartition.bipartition {2}

private def fine : Finpartition (univ : Set (Fin 3)) :=
  coarse ⊓ Finpartition.bipartition {0}

private theorem measurable_parts (P : Finpartition (univ : Set (Fin 3))) :
    ∀ p ∈ P.parts, MeasurableSet p := fun _ _ ↦ MeasurableSet.of_discrete

private def coarseAvg : Graphon (Fin 3) weights :=
  stepGraphonAvg coarse (measurable_parts coarse) adjacency

private def fineAvg : Graphon (Fin 3) weights :=
  stepGraphonAvg fine (measurable_parts fine) adjacency

private theorem integral_weights_prod (f : Fin 3 × Fin 3 → ℝ) :
    ∫ z, f z ∂(weights.prod weights) =
      (f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1)) / 4 := by
  rw [integral_prod _ Integrable.of_finite]
  simp only [weights, integral_bernoulliMeasure, smul_eq_mul]
  norm_num
  ring

private theorem coarse_parts : coarse.parts = {{2}, {2}ᶜ} := by
  classical
  rw [coarse, Finpartition.parts_bipartition]
  have h : ({2}ᶜ : Set (Fin 3)) ≠ ∅ := by
    intro h
    have : (0 : Fin 3) ∈ ({2}ᶜ : Set (Fin 3)) := by simp
    simp [h] at this
  simp [Ne.symm h]

private theorem fine_parts : fine.parts = {{0}, {1}, {2}} := by
  classical
  have h02 : ({2} : Set (Fin 3)) ∩ {0} = ∅ := by ext x; fin_cases x <;> simp
  have h2 : ({2} : Set (Fin 3)) ∩ {0}ᶜ = {2} := by ext x; fin_cases x <;> simp
  have h0 : ({2}ᶜ : Set (Fin 3)) ∩ {0} = {0} := by ext x; fin_cases x <;> simp
  have h1 : ({2}ᶜ : Set (Fin 3)) ∩ {0}ᶜ = {1} := by ext x; fin_cases x <;> simp
  have hn : ({0}ᶜ : Set (Fin 3)) ≠ ∅ := by
    intro h
    have : (1 : Fin 3) ∈ ({0}ᶜ : Set (Fin 3)) := by simp
    simp [h] at this
  ext r
  simp only [fine, Fin.isValue, Finpartition.parts_inf, inf_eq_inter, coarse_parts,
    Finpartition.parts_bipartition, bot_eq_empty, Finset.mem_insert, empty_ne_singleton,
    Finset.mem_singleton, Ne.symm hn, or_self, not_false_eq_true, Finset.erase_eq_of_notMem,
    Finset.mem_erase, ne_eq, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨hne, a, b, ⟨ha, hb⟩, hab⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  · rintro (rfl | rfl | rfl)
    · exact ⟨by simp, {2}ᶜ, {0}, ⟨Or.inr rfl, Or.inl rfl⟩, h0⟩
    · exact ⟨by simp, {2}ᶜ, {0}ᶜ, ⟨Or.inr rfl, Or.inr rfl⟩, h1⟩
    · exact ⟨by simp, {2}, {0}ᶜ, ⟨Or.inl rfl, Or.inr rfl⟩, h2⟩

private theorem coarseAvg_apply (i j : Fin 3) :
    coarseAvg i j = if i = 2 ∨ j = 2 then 0 else 1 / 2 := by
  classical
  let p : coarse.parts := ⟨if i = 2 then {2} else {2}ᶜ, by split <;> simp [coarse_parts]⟩
  let q : coarse.parts := ⟨if j = 2 then {2} else {2}ᶜ, by split <;> simp [coarse_parts]⟩
  have hi : i ∈ (p : Set (Fin 3)) := by simp [p]; split <;> simp_all
  have hj : j ∈ (q : Set (Fin 3)) := by simp [q]; split <;> simp_all
  rw [coarseAvg, stepGraphonAvg_apply coarse (measurable_parts coarse) adjacency hi hj,
    setAverage_eq, measureReal_prod_prod, ← integral_indicator (by measurability),
    integral_weights_prod]
  fin_cases i <;> fin_cases j <;>
    norm_num [p, q, measureReal_def, weights, bernoulliMeasure_apply,
      adjacency_apply, Set.indicator]

private theorem fineAvg_apply (i j : Fin 3) :
    fineAvg i j = if i = 2 ∨ j = 2 then 0 else if i = j then 0 else 1 := by
  classical
  let p : fine.parts := ⟨{i}, by fin_cases i <;> simp [fine_parts]⟩
  let q : fine.parts := ⟨{j}, by fin_cases j <;> simp [fine_parts]⟩
  rw [fineAvg, stepGraphonAvg_apply fine (measurable_parts fine) adjacency
    (p := p) (q := q) (by simp [p]) (by simp [q]),
    setAverage_eq, measureReal_prod_prod, ← integral_indicator (by measurability),
    integral_weights_prod]
  fin_cases i <;> fin_cases j <;>
    norm_num [p, q, measureReal_def, weights, bernoulliMeasure_apply,
      adjacency_apply, Set.indicator]

-- The null part is nonempty, so omitting only empty parts must retain it.
example : ({2} : Set (Fin 3)) ∈ coarse.parts ∧
    ({2} : Set (Fin 3)) ∈ fine.parts ∧ weights {2} = 0 := by
  classical
  norm_num [coarse_parts, fine_parts, weights, bernoulliMeasure_apply]

-- Null rows and columns are erased, including a value that was strictly nonzero.
example : adjacency 2 0 = 1 ∧ fineAvg 2 0 = 0 ∧ fineAvg 0 2 = 0 := by
  norm_num [adjacency_apply, fineAvg_apply]

/-- Even averaging over singletons can lose information: on a three-point Bernoulli carrier,
the zero-mass atom's row and column are erased. -/
theorem stepGraphonAvg_not_injective_bernoulliMeasure :
    ∃ (P : Finpartition (univ : Set (Fin 3))) (hP : ∀ p ∈ P.parts, MeasurableSet p),
      P.parts = {{0}, {1}, {2}} ∧
      ¬ Function.Injective (stepGraphonAvg
        (μ := bernoulliMeasure (0 : Fin 3) 1 ⟨1 / 2, by norm_num, by norm_num⟩) P hP) := by
  refine ⟨fine, measurable_parts fine, fine_parts, ?_⟩
  intro hinj
  have hidem : stepGraphonAvg fine (measurable_parts fine) fineAvg =
      stepGraphonAvg fine (measurable_parts fine) adjacency := by
    rw [fineAvg, stepGraphonAvg_idem]
  have hval := congrArg (fun W : Graphon (Fin 3) weights ↦ W 2 0) (hinj hidem)
  norm_num [fineAvg_apply, adjacency_apply] at hval

private theorem coarse_energy :
    graphonPartitionEnergy weights coarse (measurable_parts coarse) adjacency = 1 / 4 := by
  have h : l2sq weights coarseAvg.toSymmKernel = 1 / 4 := by
    rw [l2sq_def, integral_weights_prod]
    norm_num [Graphon.coe_toSymmKernel, coarseAvg_apply]
  simpa only [graphonPartitionEnergy_eq, coarseAvg] using h

private theorem fine_energy :
    graphonPartitionEnergy weights fine (measurable_parts fine) adjacency = 1 / 2 := by
  have h : l2sq weights fineAvg.toSymmKernel = 1 / 2 := by
    rw [l2sq_def, integral_weights_prod]
    norm_num [Graphon.coe_toSymmKernel, fineAvg_apply]
  simpa only [graphonPartitionEnergy_eq, fineAvg] using h

private theorem adjacency_l2sq : l2sq weights adjacency.toSymmKernel = 1 / 2 := by
  rw [l2sq_def, integral_weights_prod]
  norm_num [Graphon.coe_toSymmKernel, adjacency_apply]

-- Check the numerical defect independently, then exercise the projection identity.
example : l2sq weights (adjacency.toSymmKernel - coarseAvg.toSymmKernel) = 1 / 4 := by
  rw [l2sq_def, integral_weights_prod]
  norm_num [coarseAvg_apply, adjacency_apply]

example : l2sq weights (adjacency.toSymmKernel - coarseAvg.toSymmKernel) =
    1 / 2 - 1 / 4 := by
  rw [coarseAvg, l2sq_sub_stepGraphonAvg, adjacency_l2sq, coarse_energy]

-- A positive refinement gain despite the retained null part. Check it independently
-- before applying the energy-increment theorem to the same partitions.
example : l2sq weights (fineAvg.toSymmKernel - coarseAvg.toSymmKernel) = 1 / 4 := by
  rw [l2sq_def, integral_weights_prod]
  norm_num [coarseAvg_apply, fineAvg_apply]

example : 1 / 2 = (1 / 4 : ℝ) + l2sq weights
    (fineAvg.toSymmKernel - coarseAvg.toSymmKernel) := by
  simpa only [coarse_energy, fine_energy, coarseAvg, fineAvg] using
    graphonPartitionEnergy_increment weights coarse fine (measurable_parts coarse)
      (measurable_parts fine) inf_le_left adjacency

-- The finite refinement counts the null cell as a part, even though its energy weight is zero.
example : coarse.parts.card = 2 ∧ fine.parts.card = 3 ∧ fine ≤ coarse := by
  classical
  refine ⟨?_, ?_, inf_le_left⟩ <;> simp [coarse_parts, fine_parts]

private theorem bad_cut :
    1 / 16 < cutNorm weights (adjacency.toSymmKernel - coarseAvg.toSymmKernel) := by
  have hrect : (adjacency.toSymmKernel - coarseAvg.toSymmKernel).rectIntegral
      weights {0} {1} = 1 / 8 := by
    rw [SymmKernel.rectIntegral_def, ← integral_indicator (by measurability),
      integral_weights_prod]
    norm_num [Set.indicator, adjacency_apply, coarseAvg_apply]
  have hbound := abs_rectIntegral_le_cutNorm weights
    (adjacency.toSymmKernel - coarseAvg.toSymmKernel)
    (MeasurableSet.singleton 0) (MeasurableSet.singleton 1)
  rw [hrect] at hbound
  norm_num at hbound
  linarith

-- This exercises the strict energy-gain constructor from a nonzero cut witness, on an
-- input partition containing a nonempty null part. No non-null-part assumption is supplied.
example : ∃ (Q : Finpartition (univ : Set (Fin 3)))
    (hQ : ∀ q ∈ Q.parts, MeasurableSet q), Q ≤ coarse ∧ Q.parts.card ≤ 8 ∧
      1 / 4 + (1 / 16 : ℝ) ^ 2 < graphonPartitionEnergy weights Q hQ adjacency := by
  obtain ⟨Q, hQ, href, hcard, henergy⟩ := exists_refinement_energy_add_sq_lt weights
    coarse (measurable_parts coarse) adjacency (by norm_num) bad_cut
  refine ⟨Q, hQ, href, ?_, ?_⟩
  · simpa [coarse_parts] using hcard
  · simpa only [coarse_energy] using henergy

-- A nonintegral reciprocal-square tolerance checks the ceiling and the iteration's part
-- bound at the public endpoint: ceil(1 / (3/4)^2) = 2, hence at most 16 parts.
example : ∃ (P : Finpartition (univ : Set (Fin 3)))
    (hP : ∀ p ∈ P.parts, MeasurableSet p), P.parts.card ≤ 16 ∧
      cutNorm weights (adjacency.toSymmKernel -
        (stepGraphonAvg P hP adjacency).toSymmKernel) ≤ 3 / 4 := by
  obtain ⟨P, hP, hcard, hnorm⟩ :=
    weak_regularity_frieze_kannan weights adjacency (ε := 3 / 4) (by norm_num)
  refine ⟨P, hP, ?_, hnorm⟩
  have hceil : Nat.ceil (1 / (3 / 4 : ℝ) ^ 2) = 2 := by
    apply (Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).2
    norm_num
  simpa only [hceil, Nat.reducePow] using hcard

end TauCeti.DenseGraphLimits
