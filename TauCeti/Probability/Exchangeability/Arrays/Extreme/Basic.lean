/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Ergodic
public import TauCeti.MeasureTheory.Group.ErgodicExtreme
public import TauCeti.MeasureTheory.Measure.Face

/-!
# Extreme jointly exchangeable array laws

A jointly exchangeable probability law on array path space `ℕ × ℕ → α` is an extreme point of
the convex set of jointly exchangeable probability laws if and only if its coordinate array is
jointly dissociated. With the corner-tail theorem and the ergodicity theorem this completes the
representation-free triangle for jointly exchangeable arrays: joint dissociation, triviality of
the corner tail, ergodicity of the diagonal finitary relabelling action, and extremality are one
condition, stated on the law alone for any measurable value space.

The jointly exchangeable probability laws are the invariant probability laws for the diagonal
finitary action established in `Arrays.Ergodic`. The extreme-point characterisation is the general
one for a countable group action, `ErgodicSMul.iff_mem_extremePoints`, composed with
`jointlyDissociated_iff_ergodicSMul`.

## Main results

* `TauCeti.Probability.jointlyExchangeableProbabilityMeasures` — the convex set, and its
  identification with the invariant measures of total mass one of the diagonal action;
* `TauCeti.Probability.jointlyDissociated_iff_mem_extremePoints` — **joint dissociation is
  extremality** among jointly exchangeable probability laws, with
  `jointlyDissociated_of_mem_extremePoints` reading dissociation off an extreme point;
* `TauCeti.Probability.jointlyExchangeableProbabilityMeasuresOn` — the jointly exchangeable
  probability laws carried by a set of arrays, a face of the whole set, so that
  `jointlyDissociated_iff_mem_extremePoints_on` restricts the characterisation to them, and
  `jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag` the case of the symmetric
  arrays with a fixed diagonal, the adjacency arrays of graphs when `α = Bool`;
* `TauCeti.Probability.JointlyDissociated.ae_eq_of_comp_eq` — the integral form: a jointly
  dissociated law written as a mixture of jointly exchangeable laws has almost every component
  equal to itself.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Section 5: exchangeable random graphs as symmetric zero-diagonal arrays, and
  dissociated laws as the extreme ones.
-/

public section

open MeasureTheory TauCeti.MeasureTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The convex set of jointly exchangeable probability laws on array path space. -/
def jointlyExchangeableProbabilityMeasures (α : Type*) [MeasurableSpace α] :
    Set (Measure (ℕ × ℕ → α)) :=
  {ν | JointlyExchangeable ν (fun p x ↦ x p) ∧ IsProbabilityMeasure ν}

/-- Membership in the jointly exchangeable probability laws. -/
@[simp]
theorem mem_jointlyExchangeableProbabilityMeasures_iff {ν : Measure (ℕ × ℕ → α)} :
    ν ∈ jointlyExchangeableProbabilityMeasures α
      ↔ JointlyExchangeable ν (fun p x ↦ x p) ∧ IsProbabilityMeasure ν :=
  Iff.rfl

/-- The jointly exchangeable probability laws are the probability laws invariant under the
diagonal finitary action. -/
theorem jointlyExchangeableProbabilityMeasures_eq :
    jointlyExchangeableProbabilityMeasures α
      = invariantMeasuresOfMeasureUnivEq FinitaryPerm (ℕ × ℕ → α) 1 := by
  ext ν
  rw [mem_invariantMeasuresOfMeasureUnivEq_iff]
  constructor
  · rintro ⟨hν, hp⟩
    exact ⟨hν.smulInvariantMeasure, hp.measure_univ⟩
  · rintro ⟨hν, hp⟩
    have : IsProbabilityMeasure ν := ⟨hp⟩
    exact ⟨jointlyExchangeable_of_smulInvariantMeasure, inferInstance⟩

/-- The jointly exchangeable probability laws form a convex set. -/
theorem convex_jointlyExchangeableProbabilityMeasures :
    Convex ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α) := by
  rw [jointlyExchangeableProbabilityMeasures_eq]
  exact convex_invariantMeasuresOfMeasureUnivEq

/-- **Joint dissociation is extremality**: a jointly exchangeable probability law is an extreme
point of the jointly exchangeable probability laws if and only if its coordinate array is jointly
dissociated. -/
theorem jointlyDissociated_iff_mem_extremePoints {ρ : Measure (ℕ × ℕ → α)}
    [IsProbabilityMeasure ρ] (hexch : JointlyExchangeable ρ fun p x ↦ x p) :
    JointlyDissociated ρ (fun p x ↦ x p)
      ↔ ρ ∈ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α) := by
  rw [jointlyDissociated_iff_ergodicSMul hexch, jointlyExchangeableProbabilityMeasures_eq]
  exact ErgodicSMul.iff_mem_extremePoints

/-- The jointly exchangeable probability laws carried by a set `s` of arrays: those giving mass
zero to `sᶜ`. -/
def jointlyExchangeableProbabilityMeasuresOn (α : Type*) [MeasurableSpace α]
    (s : Set (ℕ × ℕ → α)) : Set (Measure (ℕ × ℕ → α)) :=
  {ν ∈ jointlyExchangeableProbabilityMeasures α | ν sᶜ = 0}

/-- Membership in the jointly exchangeable laws carried by `s`. -/
@[simp]
theorem mem_jointlyExchangeableProbabilityMeasuresOn_iff {s : Set (ℕ × ℕ → α)}
    {ν : Measure (ℕ × ℕ → α)} :
    ν ∈ jointlyExchangeableProbabilityMeasuresOn α s
      ↔ ν ∈ jointlyExchangeableProbabilityMeasures α ∧ ν sᶜ = 0 :=
  Iff.rfl

/-- The jointly exchangeable laws carried by `s` are a face of all jointly exchangeable
probability laws. -/
theorem isExtreme_jointlyExchangeableProbabilityMeasuresOn (s : Set (ℕ × ℕ → α)) :
    IsExtreme ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α)
      (jointlyExchangeableProbabilityMeasuresOn α s) :=
  isExtreme_setOf_measure_eq_zero _ _

/-- The jointly exchangeable laws carried by `s` form a convex set. -/
theorem convex_jointlyExchangeableProbabilityMeasuresOn (s : Set (ℕ × ℕ → α)) :
    Convex ℝ≥0∞ (jointlyExchangeableProbabilityMeasuresOn α s) :=
  convex_jointlyExchangeableProbabilityMeasures.setOf_measure_eq_zero _

/-- The extreme points of the jointly exchangeable laws carried by `s` are the extreme jointly
exchangeable laws so carried. -/
theorem extremePoints_jointlyExchangeableProbabilityMeasuresOn (s : Set (ℕ × ℕ → α)) :
    extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasuresOn α s)
      = jointlyExchangeableProbabilityMeasuresOn α s
        ∩ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α) :=
  extremePoints_setOf_measure_eq_zero _ _

/-- **Joint dissociation is extremality among the laws carried by `s`**: a jointly exchangeable
probability law carried by `s` is an extreme point of the jointly exchangeable laws carried by `s`
if and only if its coordinate array is jointly dissociated. -/
theorem jointlyDissociated_iff_mem_extremePoints_on {s : Set (ℕ × ℕ → α)}
    {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ]
    (hexch : JointlyExchangeable ρ fun p x ↦ x p) (hs : ρ sᶜ = 0) :
    JointlyDissociated ρ (fun p x ↦ x p)
      ↔ ρ ∈ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasuresOn α s) := by
  rw [extremePoints_jointlyExchangeableProbabilityMeasuresOn, Set.mem_inter_iff,
    ← jointlyDissociated_iff_mem_extremePoints hexch]
  exact ⟨fun h ↦ ⟨⟨⟨hexch, inferInstance⟩, hs⟩, h⟩, fun h ↦ h.2⟩

/-- An extreme point of the jointly exchangeable probability laws is jointly exchangeable. -/
theorem jointlyExchangeable_of_mem_extremePoints {ρ : Measure (ℕ × ℕ → α)}
    (h : ρ ∈ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α)) :
    JointlyExchangeable ρ fun p x ↦ x p :=
  h.1.1

/-- An extreme point of the jointly exchangeable probability laws is a probability law. -/
theorem isProbabilityMeasure_of_mem_extremePoints {ρ : Measure (ℕ × ℕ → α)}
    (h : ρ ∈ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α)) :
    IsProbabilityMeasure ρ :=
  h.1.2

/-- The coordinate array of an extreme point of the jointly exchangeable probability laws is
jointly dissociated. -/
theorem jointlyDissociated_of_mem_extremePoints {ρ : Measure (ℕ × ℕ → α)}
    (h : ρ ∈ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α)) :
    JointlyDissociated ρ fun p x ↦ x p :=
  have := isProbabilityMeasure_of_mem_extremePoints h
  (jointlyDissociated_iff_mem_extremePoints (jointlyExchangeable_of_mem_extremePoints h)).2 h

/-- The coordinate array of an extreme point of the jointly exchangeable laws carried by `s` is
jointly dissociated. -/
theorem jointlyDissociated_of_mem_extremePoints_on {s : Set (ℕ × ℕ → α)}
    {ρ : Measure (ℕ × ℕ → α)}
    (h : ρ ∈ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasuresOn α s)) :
    JointlyDissociated ρ fun p x ↦ x p :=
  jointlyDissociated_of_mem_extremePoints
    ((extremePoints_jointlyExchangeableProbabilityMeasuresOn s ▸ h).2)

/-- The jointly exchangeable probability laws carried by the symmetric arrays with diagonal `d`.
For `α = Bool` and `d = false` the carrier is the adjacency arrays of the simple graphs on `ℕ`,
and these are the laws of exchangeable random graphs read as arrays. -/
def jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag (α : Type*) [MeasurableSpace α]
    (d : α) : Set (Measure (ℕ × ℕ → α)) :=
  jointlyExchangeableProbabilityMeasuresOn α (symmetricArraysWithDiag α d)

/-- The jointly exchangeable laws carried by the symmetric arrays are the carried laws at that
carrier. -/
theorem jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_eq (d : α) :
    jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag α d
      = jointlyExchangeableProbabilityMeasuresOn α (symmetricArraysWithDiag α d) :=
  (rfl)

/-- Membership in the jointly exchangeable laws carried by the symmetric arrays. -/
@[simp]
theorem mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff {d : α}
    {ν : Measure (ℕ × ℕ → α)} :
    ν ∈ jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag α d
      ↔ ν ∈ jointlyExchangeableProbabilityMeasures α ∧ ν (symmetricArraysWithDiag α d)ᶜ = 0 :=
  Iff.rfl

open ProbabilityTheory in
/-- **A jointly dissociated array law is not a nontrivial mixture of jointly exchangeable
laws.** If `ρ` is the mixture `κ ∘ₘ π` of a Markov kernel whose laws are almost all jointly
exchangeable, then almost every `κ z` is `ρ` itself. This is the integral form of
`jointlyDissociated_iff_mem_extremePoints`. -/
theorem JointlyDissociated.ae_eq_of_comp_eq [StandardBorelSpace α] {Z : Type*}
    [MeasurableSpace Z] {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ] {π : Measure Z}
    {κ : Kernel Z (ℕ × ℕ → α)} [IsMarkovKernel κ]
    (hρ : JointlyDissociated ρ fun p x ↦ x p)
    (hκ : ∀ᵐ z ∂π, JointlyExchangeable (κ z) fun p x ↦ x p) (hmix : κ ∘ₘ π = ρ) :
    ∀ᵐ z ∂π, κ z = ρ := by
  have hinv : ∀ᵐ z ∂π, SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) (κ z) :=
    hκ.mono fun _ hz ↦ hz.smulInvariantMeasure
  have : SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ := hmix ▸ smulInvariantMeasure_comp hinv
  have := ergodicSMul_of_jointlyDissociated hρ
  exact ErgodicSMul.ae_eq_of_comp_eq hinv hmix

end Probability

end TauCeti
