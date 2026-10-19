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
nothing to the integrals. The defect identity `l2sq_sub_stepGraphonAvg` and the Pythagoras
increment `graphonPartitionEnergy_increment` are exercised on these partitions, together with
a cut witness and the iteration's part-count bound, starting from the coarse partition at a
tolerance that forces refinement and checking that the null singleton persists. Averaging over
singletons does not recover the original strict representative: the zero-mass atom's row and
column are replaced by
zero. The exported witness `exists_partition_stepGraphonAvg_ne_self_bernoulliMeasure` records this
failure for a partition into all three singletons.

The carrier, graphon, partitions and block averages live in the namespace `NullCellExample`, so
the computed values can be cited by name.

## Main results

* `NullCellExample.coarse_energy`, `NullCellExample.fine_energy` — the energies `1/4` and `1/2`;
* `NullCellExample.l2sq_adjacency_sub_coarseAvg` and
  `NullCellExample.l2sq_adjacency_sub_coarseAvg_eq_sub` — the coarse defect, directly and through
  `l2sq_sub_stepGraphonAvg`;
* `NullCellExample.l2sq_fineAvg_sub_coarseAvg` and
  `NullCellExample.fine_energy_eq_coarse_energy_add` — the refinement increment, directly
  and through `graphonPartitionEnergy_increment`;
* `NullCellExample.lt_cutNorm_adjacency_sub_coarseAvg` and
  `NullCellExample.exists_refinement_coarse_energy_add_sq_lt` — the cut witness and the strict
  energy gain it produces;
* `NullCellExample.exists_refinement_coarse_cutNorm_le_one_div_sixteen` — the iteration bound at
  tolerance `1/16`;
* `exists_partition_stepGraphonAvg_ne_self_bernoulliMeasure` — averaging over singletons can
  change a strict graphon.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace TauCeti.DenseGraphLimits

namespace NullCellExample

/-- The carrier weights: mass `1/2` at each of `0` and `1`, and no mass at `2`. -/
abbrev weights : Measure (Fin 3) :=
  bernoulliMeasure 0 1 ⟨1 / 2, by norm_num, by norm_num⟩

/-- The complete adjacency matrix on `Fin 3`, as a graphon over `weights`: value `1` between
distinct points, including between the null atom `2` and the positive atoms. -/
def adjacency : Graphon (Fin 3) weights :=
  Graphon.ofMatrix weights (fun i j ↦ if i = j then 0 else 1) (by
    intro i j
    simp [eq_comm])

/-- `adjacency` is `0` on the diagonal and `1` off it. -/
@[simp] theorem adjacency_apply (i j : Fin 3) :
    adjacency i j = if i = j then 0 else 1 := by
  rw [adjacency, Graphon.ofMatrix_apply]
  split <;> simp

/-- The coarse partition `{{2}, {0, 1}}`, splitting off the null atom. -/
def coarse : Finpartition (univ : Set (Fin 3)) := Finpartition.bipartition {2}

/-- The fine partition into singletons, refining `coarse`. -/
def fine : Finpartition (univ : Set (Fin 3)) :=
  coarse ⊓ Finpartition.bipartition {0}

/-- The block average of `adjacency` over `coarse`. -/
def coarseAvg : Graphon (Fin 3) weights :=
  stepGraphonAvg coarse (fun _ _ ↦ MeasurableSet.of_discrete) adjacency

/-- The block average of `adjacency` over `fine`. -/
def fineAvg : Graphon (Fin 3) weights :=
  stepGraphonAvg fine (fun _ _ ↦ MeasurableSet.of_discrete) adjacency

private theorem integral_weights_prod (f : Fin 3 × Fin 3 → ℝ) :
    ∫ z, f z ∂(weights.prod weights) =
      (f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1)) / 4 := by
  rw [integral_prod _ Integrable.of_finite]
  simp only [weights, integral_bernoulliMeasure, smul_eq_mul]
  ring

/-- The parts of `coarse` are `{2}` and its complement. -/
theorem coarse_parts : coarse.parts = {{2}, {2}ᶜ} := by
  classical
  rw [coarse, Finpartition.parts_bipartition]
  have h : ({2}ᶜ : Set (Fin 3)) ≠ ∅ := Set.Nonempty.ne_empty ⟨0, by simp⟩
  simp [Ne.symm h]

/-- The parts of `fine` are the three singletons. -/
theorem fine_parts : fine.parts = {{0}, {1}, {2}} := by
  classical
  have h02 : ({2} : Set (Fin 3)) ∩ {0} = ∅ := by ext x; fin_cases x <;> simp
  have h2 : ({2} : Set (Fin 3)) ∩ {0}ᶜ = {2} := by ext x; fin_cases x <;> simp
  have h0 : ({2}ᶜ : Set (Fin 3)) ∩ {0} = {0} := by ext x; fin_cases x <;> simp
  have h1 : ({2}ᶜ : Set (Fin 3)) ∩ {0}ᶜ = {1} := by ext x; fin_cases x <;> simp
  have hn : ({0}ᶜ : Set (Fin 3)) ≠ ∅ := Set.Nonempty.ne_empty ⟨1, by simp⟩
  rw [fine, Finpartition.parts_inf, coarse_parts, Finpartition.parts_bipartition]
  simp [Finset.product_eq_biUnion, h0, h1, h2, h02, Ne.symm hn,
    Set.empty_ne_singleton, Finset.erase_insert_of_ne, Finset.insert_comm, Finset.pair_comm]

private theorem stepGraphonAvg_adjacency_apply
    (P : Finpartition (univ : Set (Fin 3))) {p q : P.parts} {i j : Fin 3}
    (hi : i ∈ (p : Set (Fin 3))) (hj : j ∈ (q : Set (Fin 3))) :
    stepGraphonAvg P (fun _ _ ↦ MeasurableSet.of_discrete) adjacency i j =
      let f := ((p : Set (Fin 3)) ×ˢ (q : Set (Fin 3))).indicator
        (fun z ↦ adjacency z.1 z.2)
      (weights.real (p : Set (Fin 3)) * weights.real (q : Set (Fin 3)))⁻¹ *
        ((f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1)) / 4) := by
  rw [stepGraphonAvg_apply P (fun _ _ ↦ MeasurableSet.of_discrete) adjacency hi hj,
    setAverage_eq, measureReal_prod_prod, ← integral_indicator (by measurability),
    integral_weights_prod, smul_eq_mul]

/-- The coarse block average is `1/2` on the positive cell and `0` on every entry incident to
the null atom. -/
@[simp] theorem coarseAvg_apply (i j : Fin 3) :
    coarseAvg i j = if i = 2 ∨ j = 2 then 0 else 1 / 2 := by
  classical
  let p : coarse.parts := ⟨if i = 2 then {2} else {2}ᶜ, by split <;> simp [coarse_parts]⟩
  let q : coarse.parts := ⟨if j = 2 then {2} else {2}ᶜ, by split <;> simp [coarse_parts]⟩
  have hi : i ∈ (p : Set (Fin 3)) := by fin_cases i <;> simp [p]
  have hj : j ∈ (q : Set (Fin 3)) := by fin_cases j <;> simp [q]
  rw [coarseAvg, stepGraphonAvg_adjacency_apply coarse hi hj]
  fin_cases i <;> fin_cases j <;>
    norm_num [p, q, weights, bernoulliMeasure_real_apply, adjacency_apply,
      Set.indicator_of_mem, Set.indicator_of_notMem]

/-- The fine block average agrees with `adjacency` away from the null atom and is `0` on every
entry incident to it. -/
@[simp] theorem fineAvg_apply (i j : Fin 3) :
    fineAvg i j = if i = 2 ∨ j = 2 then 0 else if i = j then 0 else 1 := by
  classical
  let p : fine.parts := ⟨{i}, by fin_cases i <;> simp [fine_parts]⟩
  let q : fine.parts := ⟨{j}, by fin_cases j <;> simp [fine_parts]⟩
  rw [fineAvg, stepGraphonAvg_adjacency_apply fine
    (p := p) (q := q) (by simp [p]) (by simp [q])]
  fin_cases i <;> fin_cases j <;>
    norm_num [p, q, weights, bernoulliMeasure_real_apply, adjacency_apply,
      Set.indicator_of_mem, Set.indicator_of_notMem]

-- The null part is nonempty, so omitting only empty parts must retain it.
example : ({2} : Set (Fin 3)) ∈ coarse.parts ∧
    ({2} : Set (Fin 3)) ∈ fine.parts ∧ weights {2} = 0 := by
  classical
  norm_num [coarse_parts, fine_parts, weights, bernoulliMeasure_apply]

-- Null rows and columns are erased, including a value that was strictly nonzero.
example : adjacency 2 0 = 1 ∧ fineAvg 2 0 = 0 ∧ fineAvg 0 2 = 0 := by
  norm_num [adjacency_apply, fineAvg_apply]

/-- **The coarse energy is `1/4`.** -/
theorem coarse_energy :
    graphonPartitionEnergy weights coarse (fun _ _ ↦ MeasurableSet.of_discrete) adjacency =
      1 / 4 := by
  have h : l2sq weights coarseAvg.toSymmKernel = 1 / 4 := by
    rw [l2sq_def, integral_weights_prod]
    norm_num [Graphon.coe_toSymmKernel, coarseAvg_apply]
  simpa only [graphonPartitionEnergy_eq, coarseAvg] using h

/-- **The fine energy is `1/2`**, although the null cell is a part of `fine`. -/
theorem fine_energy :
    graphonPartitionEnergy weights fine (fun _ _ ↦ MeasurableSet.of_discrete) adjacency =
      1 / 2 := by
  have h : l2sq weights fineAvg.toSymmKernel = 1 / 2 := by
    rw [l2sq_def, integral_weights_prod]
    norm_num [Graphon.coe_toSymmKernel, fineAvg_apply]
  simpa only [graphonPartitionEnergy_eq, fineAvg] using h

/-- The squared `L²` seminorm of `adjacency` is `1/2`. -/
theorem l2sq_adjacency : l2sq weights adjacency.toSymmKernel = 1 / 2 := by
  rw [l2sq_def, integral_weights_prod]
  norm_num [Graphon.coe_toSymmKernel, adjacency_apply]

/-- **The coarse approximation defect**, computed directly: `‖W - W_coarse‖₂² = 1/4`. -/
theorem l2sq_adjacency_sub_coarseAvg :
    l2sq weights (adjacency.toSymmKernel - coarseAvg.toSymmKernel) = 1 / 4 := by
  rw [l2sq_def, integral_weights_prod]
  norm_num [coarseAvg_apply, adjacency_apply]

/-- **The defect identity** `l2sq_sub_stepGraphonAvg` on the coarse partition:
`‖W - W_coarse‖₂² = ‖W‖₂² - energy(coarse) = 1/2 - 1/4`, in agreement with
`l2sq_adjacency_sub_coarseAvg`. -/
theorem l2sq_adjacency_sub_coarseAvg_eq_sub :
    l2sq weights (adjacency.toSymmKernel - coarseAvg.toSymmKernel) = 1 / 2 - 1 / 4 := by
  rw [coarseAvg, l2sq_sub_stepGraphonAvg, l2sq_adjacency, coarse_energy]

/-- **The refinement increment**, computed directly: `‖W_fine - W_coarse‖₂² = 1/4`, a positive
gain despite the retained null part. -/
theorem l2sq_fineAvg_sub_coarseAvg :
    l2sq weights (fineAvg.toSymmKernel - coarseAvg.toSymmKernel) = 1 / 4 := by
  rw [l2sq_def, integral_weights_prod]
  norm_num [coarseAvg_apply, fineAvg_apply]

/-- **The Pythagoras increment** `graphonPartitionEnergy_increment` on `coarse ≥ fine`:
`energy(fine) = energy(coarse) + ‖W_fine - W_coarse‖₂²`, that is `1/2 = 1/4 + 1/4`, in agreement
with `l2sq_fineAvg_sub_coarseAvg`. -/
theorem fine_energy_eq_coarse_energy_add :
    1 / 2 = (1 / 4 : ℝ) + l2sq weights (fineAvg.toSymmKernel - coarseAvg.toSymmKernel) := by
  simpa only [coarse_energy, fine_energy, coarseAvg, fineAvg] using
    graphonPartitionEnergy_increment weights coarse fine (fun _ _ ↦ MeasurableSet.of_discrete)
      (fun _ _ ↦ MeasurableSet.of_discrete) inf_le_left adjacency

-- The finite refinement counts the null cell as a part, even though its energy weight is zero.
example : coarse.parts.card = 2 ∧ fine.parts.card = 3 ∧ fine ≤ coarse := by
  classical
  refine ⟨?_, ?_, inf_le_left⟩ <;> simp [coarse_parts, fine_parts]

/-- **A cut witness.** The rectangle `{0} × {1}` carries `1/8` of `W - W_coarse`, so the cut norm
of the coarse defect exceeds `1/16`. -/
theorem lt_cutNorm_adjacency_sub_coarseAvg :
    1 / 16 < cutNorm weights (adjacency.toSymmKernel - coarseAvg.toSymmKernel) := by
  have hrect : (adjacency.toSymmKernel - coarseAvg.toSymmKernel).rectIntegral
      weights {0} {1} = 1 / 8 := by
    rw [SymmKernel.rectIntegral_def, ← integral_indicator (by measurability),
      integral_weights_prod]
    norm_num [Set.indicator_of_mem, Set.indicator_of_notMem, adjacency_apply, coarseAvg_apply]
  have hbound := abs_rectIntegral_le_cutNorm weights
    (adjacency.toSymmKernel - coarseAvg.toSymmKernel)
    (MeasurableSet.singleton 0) (MeasurableSet.singleton 1)
  rw [hrect] at hbound
  exact lt_of_lt_of_le (by norm_num) hbound

/-- **The strict energy gain from the cut witness.** `exists_refinement_energy_add_sq_lt`, applied
to `lt_cutNorm_adjacency_sub_coarseAvg` on an input partition containing a nonempty null part (no
non-null-part assumption is supplied), refines `coarse` into at most `8` parts with energy above
`1/4 + (1/16)²`. -/
theorem exists_refinement_coarse_energy_add_sq_lt : ∃ (Q : Finpartition (univ : Set (Fin 3)))
    (hQ : ∀ q ∈ Q.parts, MeasurableSet q), Q ≤ coarse ∧ Q.parts.card ≤ 8 ∧
      1 / 4 + (1 / 16 : ℝ) ^ 2 < graphonPartitionEnergy weights Q hQ adjacency := by
  obtain ⟨Q, hQ, href, hcard, henergy⟩ := exists_refinement_energy_add_sq_lt weights
    coarse (fun _ _ ↦ MeasurableSet.of_discrete) adjacency (by norm_num)
    lt_cutNorm_adjacency_sub_coarseAvg
  refine ⟨Q, hQ, href, ?_, ?_⟩
  · simpa [coarse_parts] using hcard
  · simpa only [coarse_energy] using henergy

/-- **The iteration bound at tolerance `1/16`.** Starting from `coarse`, which the cut witness
rules out, the 256-step invariant `exists_partition_cutNorm_le_or_energy_add_mul_sq_lt` yields a
proper refinement with at most `4 ^ ⌈1 / (1/16)²⌉ * 2` parts whose block average is within
`1/16` in cut norm; its energy alternative contradicts the upper bound of one. The refinement
retains the nonempty null singleton `{2}`. -/
theorem exists_refinement_coarse_cutNorm_le_one_div_sixteen :
    ∃ (Q : Finpartition (univ : Set (Fin 3)))
    (hQ : ∀ q ∈ Q.parts, MeasurableSet q), Q ≤ coarse ∧
      ({2} : Set (Fin 3)) ∈ Q.parts ∧ Q ≠ coarse ∧
      Q.parts.card ≤ 4 ^ Nat.ceil (1 / (1 / 16 : ℝ) ^ 2) * 2 ∧
      cutNorm weights (adjacency.toSymmKernel -
        (stepGraphonAvg Q hQ adjacency).toSymmKernel) ≤ 1 / 16 := by
  classical
  obtain ⟨Q, hQ, href, hcard, hgood | henergy⟩ :=
    exists_partition_cutNorm_le_or_energy_add_mul_sq_lt weights adjacency
      (ε := 1 / 16) (by norm_num) 255 coarse (fun _ _ ↦ MeasurableSet.of_discrete)
  · obtain ⟨q, ⟨hq, hxq⟩, _⟩ := Q.isPartition_parts.2 2
    obtain ⟨p, hp, hqp⟩ := href hq
    have hxp : (2 : Fin 3) ∈ p := hqp hxq
    have hp_eq : p = {2} := by
      simp only [coarse_parts, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · rfl
      · simp at hxp
    have hq_eq : q = {2} :=
      Set.Subset.antisymm (hp_eq ▸ hqp) (Set.singleton_subset_iff.mpr hxq)
    refine ⟨Q, hQ, href, hq_eq ▸ hq, ?_, ?_, hgood⟩
    · intro heq
      subst Q
      exact (not_le_of_gt lt_cutNorm_adjacency_sub_coarseAvg) hgood
    · have hceil : Nat.ceil (1 / (1 / 16 : ℝ) ^ 2) = 256 := by norm_num
      rw [hceil]
      simpa [coarse_parts] using hcard
  · have hbound := graphonPartitionEnergy_le_one weights Q hQ adjacency
    rw [coarse_energy] at henergy
    norm_num at henergy
    linarith

-- Separately check nonintegral ceiling arithmetic at the public endpoint:
-- ceil(1 / (3/4)^2) = 2, hence at most 16 parts.
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
  rw [hceil] at hcard
  simpa using hcard

end NullCellExample

open NullCellExample in
/-- On the three-point carrier with masses `1/2`, `1/2`, and `0`, averaging over the
singleton partition can change the original strict graphon. The zero-mass atom's incident
edges are erased. -/
theorem exists_partition_stepGraphonAvg_ne_self_bernoulliMeasure :
    ∃ (P : Finpartition (univ : Set (Fin 3)))
      (W : Graphon (Fin 3)
        (bernoulliMeasure 0 1 ⟨1 / 2, by norm_num, by norm_num⟩)),
      P.parts = {{0}, {1}, {2}} ∧
      stepGraphonAvg P (fun _ _ ↦ MeasurableSet.of_discrete) W ≠ W := by
  refine ⟨fine, adjacency, fine_parts, ?_⟩
  rw [← fineAvg]
  intro h
  have hval := congrArg (fun W : Graphon (Fin 3) weights ↦ W 2 0) h
  norm_num [fineAvg_apply, adjacency_apply] at hval

end TauCeti.DenseGraphLimits
