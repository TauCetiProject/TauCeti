/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Extreme
public import TauCeti.MeasureTheory.Measure.Face

/-!
# Jointly exchangeable laws carried by symmetric arrays

A graph on `ℕ`, read as its adjacency array, is a symmetric `Bool`-valued array with `false` on
the diagonal. The array-side interface a graph-law adapter needs is therefore the jointly
exchangeable probability laws on `ℕ × ℕ → α` that are **carried by** the symmetric arrays with a
prescribed diagonal value, in the sense that the complement of that measurable set is null. This
file names that carrier and that set of laws, and records that the laws so carried are a face of
all jointly exchangeable probability laws, so that the extreme-point characterisation of joint
dissociation restricts to them unchanged: a law carried by the symmetric arrays is dissociated if
and only if it is extreme among the jointly exchangeable laws carried by the symmetric arrays.

Nothing here mentions graphs; the graph encoding and the adapter live with the graph laws.

## Main results

* `TauCeti.Probability.symmetricArrays`, `measurableSet_symmetricArrays` — the carrier.
* `TauCeti.Probability.symmetricJointlyExchangeableProbabilityMeasures`, with its membership and
  convexity lemmas — the jointly exchangeable probability laws carried by the symmetric arrays.
* `TauCeti.Probability.extremePoints_symmetricJointlyExchangeableProbabilityMeasures` — its
  extreme points are the extreme jointly exchangeable laws it contains.
* `TauCeti.Probability.jointlyDissociated_iff_mem_extremePoints_symmetric` — **joint dissociation
  is extremality** among the jointly exchangeable laws carried by the symmetric arrays.
-/

public section

open MeasureTheory TauCeti.MeasureTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The symmetric arrays with constant diagonal value `d`. -/
def symmetricArrays (α : Type*) (d : α) : Set (ℕ × ℕ → α) :=
  {x | (∀ i j, x (i, j) = x (j, i)) ∧ ∀ i, x (i, i) = d}

omit [MeasurableSpace α] in
/-- Membership in the symmetric arrays with diagonal `d`. -/
@[simp]
theorem mem_symmetricArrays_iff {d : α} {x : ℕ × ℕ → α} :
    x ∈ symmetricArrays α d ↔ (∀ i j, x (i, j) = x (j, i)) ∧ ∀ i, x (i, i) = d :=
  Iff.rfl

/-- The symmetric arrays with diagonal `d` form a measurable set. -/
theorem measurableSet_symmetricArrays [MeasurableEq α] (d : α) :
    MeasurableSet (symmetricArrays α d) := by
  have h1 : MeasurableSet {x : ℕ × ℕ → α | ∀ i j, x (i, j) = x (j, i)} := by
    have : {x : ℕ × ℕ → α | ∀ i j, x (i, j) = x (j, i)}
        = ⋂ i, ⋂ j, {x : ℕ × ℕ → α | x (i, j) = x (j, i)} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _)
  have h2 : MeasurableSet {x : ℕ × ℕ → α | ∀ i, x (i, i) = d} := by
    have : {x : ℕ × ℕ → α | ∀ i, x (i, i) = d} = ⋂ i, {x : ℕ × ℕ → α | x (i, i) = d} := by
      ext; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  exact h1.inter h2

/-- The jointly exchangeable probability laws carried by the symmetric arrays with diagonal `d`:
those giving mass zero to the complement of `symmetricArrays α d`. -/
def symmetricJointlyExchangeableProbabilityMeasures (α : Type*) [MeasurableSpace α] (d : α) :
    Set (Measure (ℕ × ℕ → α)) :=
  {ν ∈ jointlyExchangeableProbabilityMeasures α | ν (symmetricArrays α d)ᶜ = 0}

/-- Membership in the jointly exchangeable laws carried by the symmetric arrays. -/
@[simp]
theorem mem_symmetricJointlyExchangeableProbabilityMeasures_iff {d : α}
    {ν : Measure (ℕ × ℕ → α)} :
    ν ∈ symmetricJointlyExchangeableProbabilityMeasures α d
      ↔ ν ∈ jointlyExchangeableProbabilityMeasures α ∧ ν (symmetricArrays α d)ᶜ = 0 :=
  Iff.rfl

/-- The jointly exchangeable laws carried by the symmetric arrays are a face of all jointly
exchangeable probability laws. -/
theorem isExtreme_symmetricJointlyExchangeableProbabilityMeasures (d : α) :
    IsExtreme ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α)
      (symmetricJointlyExchangeableProbabilityMeasures α d) :=
  Measure.isExtreme_setOf_measure_compl_eq_zero _ _

/-- The jointly exchangeable laws carried by the symmetric arrays form a convex set. -/
theorem convex_symmetricJointlyExchangeableProbabilityMeasures (d : α) :
    Convex ℝ≥0∞ (symmetricJointlyExchangeableProbabilityMeasures α d) := by
  rintro ν₁ ⟨hν₁, h₁⟩ ν₂ ⟨hν₂, h₂⟩ a b ha hb hab
  refine ⟨convex_jointlyExchangeableProbabilityMeasures hν₁ hν₂ ha hb hab, ?_⟩
  simp [Measure.add_apply, Measure.smul_apply, h₁, h₂]

/-- The extreme points of the jointly exchangeable laws carried by the symmetric arrays are the
extreme jointly exchangeable laws so carried. -/
theorem extremePoints_symmetricJointlyExchangeableProbabilityMeasures (d : α) :
    extremePoints ℝ≥0∞ (symmetricJointlyExchangeableProbabilityMeasures α d)
      = symmetricJointlyExchangeableProbabilityMeasures α d
        ∩ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α) :=
  Measure.extremePoints_setOf_measure_compl_eq_zero _ _

/-- **Joint dissociation is extremality among the laws carried by the symmetric arrays**: a
jointly exchangeable probability law carried by the symmetric arrays with diagonal `d` is an
extreme point of those laws if and only if its coordinate array is jointly dissociated. -/
theorem jointlyDissociated_iff_mem_extremePoints_symmetric {d : α} {ρ : Measure (ℕ × ℕ → α)}
    [IsProbabilityMeasure ρ] (hexch : JointlyExchangeable ρ fun p x => x p)
    (hsym : ρ (symmetricArrays α d)ᶜ = 0) :
    JointlyDissociated ρ (fun p x => x p)
      ↔ ρ ∈ extremePoints ℝ≥0∞ (symmetricJointlyExchangeableProbabilityMeasures α d) := by
  rw [extremePoints_symmetricJointlyExchangeableProbabilityMeasures, Set.mem_inter_iff,
    ← jointlyDissociated_iff_mem_extremePoints hexch]
  refine ⟨fun h => ⟨⟨?_, hsym⟩, h⟩, fun h => h.2⟩
  exact mem_jointlyExchangeableProbabilityMeasures_iff.2 ⟨hexch, inferInstance⟩

end Probability

end TauCeti
