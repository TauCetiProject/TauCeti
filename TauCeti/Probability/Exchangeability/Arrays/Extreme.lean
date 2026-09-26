/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Ergodic
public import TauCeti.MeasureTheory.Group.ErgodicExtreme
public import TauCeti.MeasureTheory.Measure.Face
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Extreme jointly exchangeable array laws and finitary tests

A jointly exchangeable probability law on array path space `ℕ × ℕ → α` is an extreme point of
the convex set of jointly exchangeable probability laws if and only if its coordinate array is
jointly dissociated. With the corner-tail theorem and the ergodicity theorem this completes the
representation-free triangle for jointly exchangeable arrays: joint dissociation, triviality of
the corner tail, ergodicity of the diagonal finitary relabelling action, and extremality are one
condition, stated on the law alone for any measurable value space.

The jointly exchangeable probability laws are exactly the probability laws invariant under the
diagonal action of the finitely supported permutations: invariance under the finitary
permutations already gives invariance under every permutation, since a law is determined by its
finite-dimensional marginals and on finitely many indices any permutation agrees with a finitely
supported one. The extreme-point characterisation is then the general one for a countable group
action, `ErgodicSMul.iff_mem_extremePoints`, composed with `jointlyDissociated_iff_ergodicSMul`.
The same finite-dimensional approximation also shows that separate exchangeability can be tested
using pairs of finitely supported axis permutations.

## Main results

* `TauCeti.Probability.jointlyExchangeable_of_smulInvariantMeasure` — invariance under the
  finitary diagonal action gives joint exchangeability;
* `TauCeti.Probability.separatelyExchangeable_iff_map_pairReindex_finitary` — separate
  exchangeability is invariance under pairs of finitely supported axis relabellings;
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

private theorem map_pairReindex_eq_self_of_forall_finset
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ] {σ τ : Equiv.Perm ℕ}
    (h : ∀ F : Finset (ℕ × ℕ), ∃ σ' τ' : Equiv.Perm ℕ,
      ρ.map (pairReindex σ' τ') = ρ ∧
        ∀ p ∈ F, σ' p.1 = σ p.1 ∧ τ' p.2 = τ p.2) :
    (ρ.map fun x : ℕ × ℕ → α ↦ fun p ↦ x (σ p.1, τ p.2)) =
      ρ.map fun x : ℕ × ℕ → α ↦ fun p ↦ x p := by
  have hmeas : ∀ π π' : Equiv.Perm ℕ,
      AEMeasurable (fun x : ℕ × ℕ → α ↦ fun p : ℕ × ℕ ↦ x (π p.1, π' p.2)) ρ :=
    fun π π' ↦ by
      rw [← pairReindex_def]
      exact (measurable_pairReindex π π').aemeasurable
  rw [ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq (hmeas σ τ)
    (Measurable.of_eval fun p ↦ measurable_pi_apply p).aemeasurable]
  intro F
  obtain ⟨σ', τ', hinv, hagree⟩ := h F
  have hinv' : (ρ.map fun x : ℕ × ℕ → α ↦ fun p ↦ x (σ' p.1, τ' p.2)) =
      ρ.map fun x : ℕ × ℕ → α ↦ fun p ↦ x p := by
    simpa only [← pairReindex_def, Measure.map_id'] using hinv
  have hres := (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq (hmeas σ' τ')
    (Measurable.of_eval fun p ↦ measurable_pi_apply p).aemeasurable).mp hinv' F
  have heq : (fun x : ℕ × ℕ → α ↦ F.restrict fun p ↦ x (σ' p.1, τ' p.2)) =
      fun x : ℕ × ℕ → α ↦ F.restrict fun p ↦ x (σ p.1, τ p.2) := by
    funext x p
    obtain ⟨q, hq⟩ := p
    simp only [Finset.restrict_def, (hagree q hq).1, (hagree q hq).2]
  rwa [heq] at hres

/-- A finite law on `ℕ × ℕ → α` invariant under the finitary diagonal action is jointly
exchangeable: invariant under the diagonal relabelling by every permutation of `ℕ`. -/
theorem jointlyExchangeable_of_smulInvariantMeasure {ρ : Measure (ℕ × ℕ → α)}
    [IsFiniteMeasure ρ] [SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ] :
    JointlyExchangeable ρ fun p x ↦ x p := by
  rw [jointlyExchangeable_iff]
  intro σ
  apply map_pairReindex_eq_self_of_forall_finset
  intro F
  obtain ⟨π, hπfin, hπ⟩ := Equiv.Perm.exists_finite_compl_fixedBy_apply_eq_on_finset σ
    (F.image Prod.fst ∪ F.image Prod.snd)
  refine ⟨π, π, ?_, ?_⟩
  · -- the law is invariant under `π`, read through the action
    have hπ' : (MulAction.fixedBy ℕ π⁻¹)ᶜ.Finite := by
      simpa only [MulAction.fixedBy_inv ℕ] using hπfin
    have h := SMulInvariantMeasure.measure_preimage_smul (μ := ρ) (FinitaryPerm.ofPerm π⁻¹ hπ')
    ext s hs
    rw [Measure.map_apply (measurable_pairReindex _ _) hs]
    have := h hs
    simpa only [finitaryPerm_smul_array_def, FinitaryPerm.toPerm_ofPerm, inv_inv] using this
  · intro p hp
    exact ⟨hπ _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)),
      hπ _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))⟩

/-- **Finitely supported permutations already test separate exchangeability.** A finite law on
array path space invariant under every pair of finitely supported axis relabellings is invariant
under every pair of axis relabellings: the law is determined by its finite-dimensional marginals,
and on finitely many indices any permutation agrees with a finitely supported one.

This is the separate counterpart of `jointlyExchangeable_of_smulInvariantMeasure`; it is stated
through the two permutations rather than through a group action because the two axes are
relabelled independently. -/
theorem separatelyExchangeable_of_map_pairReindex_finitary
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]
    (h : ∀ σ τ : Equiv.Perm ℕ, (MulAction.fixedBy ℕ σ)ᶜ.Finite → (MulAction.fixedBy ℕ τ)ᶜ.Finite →
      ρ.map (pairReindex σ τ) = ρ) :
    SeparatelyExchangeable ρ fun p x ↦ x p := by
  rw [separatelyExchangeable_iff]
  intro σ τ
  apply map_pairReindex_eq_self_of_forall_finset
  intro F
  -- finitely supported relabellings agreeing with `σ` and `τ` on the indices that `F` reads
  obtain ⟨σ', hσ'fin, hσ'⟩ :=
    Equiv.Perm.exists_finite_compl_fixedBy_apply_eq_on_finset σ (F.image Prod.fst)
  obtain ⟨τ', hτ'fin, hτ'⟩ :=
    Equiv.Perm.exists_finite_compl_fixedBy_apply_eq_on_finset τ (F.image Prod.snd)
  exact ⟨σ', τ', h σ' τ' hσ'fin hτ'fin, fun p hp ↦
    ⟨hσ' _ (Finset.mem_image_of_mem _ hp), hτ' _ (Finset.mem_image_of_mem _ hp)⟩⟩

/-- A finite law on array path space is separately exchangeable if and only if it is invariant
under every pair of finitely supported axis relabellings. -/
theorem separatelyExchangeable_iff_map_pairReindex_finitary
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ] :
    SeparatelyExchangeable ρ (fun p x ↦ x p) ↔
      ∀ σ τ : Equiv.Perm ℕ, (MulAction.fixedBy ℕ σ)ᶜ.Finite → (MulAction.fixedBy ℕ τ)ᶜ.Finite →
        ρ.map (pairReindex σ τ) = ρ :=
  ⟨fun h σ τ _ _ ↦ (h.measurePreserving_pairReindex σ τ).map_eq,
    separatelyExchangeable_of_map_pairReindex_finitary⟩

/-- A finite law is jointly exchangeable if and only if it is invariant under the finitary
diagonal action. -/
theorem jointlyExchangeable_iff_smulInvariantMeasure {ρ : Measure (ℕ × ℕ → α)}
    [IsFiniteMeasure ρ] :
    JointlyExchangeable ρ (fun p x ↦ x p) ↔ SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ :=
  ⟨JointlyExchangeable.smulInvariantMeasure, fun _ ↦ jointlyExchangeable_of_smulInvariantMeasure⟩

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
