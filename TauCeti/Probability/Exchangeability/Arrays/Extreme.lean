/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Ergodic
public import TauCeti.MeasureTheory.Group.ErgodicExtreme
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Extreme jointly exchangeable array laws

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

## Main results

* `TauCeti.Probability.jointlyExchangeable_of_smulInvariantMeasure` — invariance under the
  finitary diagonal action gives joint exchangeability;
* `TauCeti.Probability.jointlyExchangeableProbabilityMeasures` — the convex set, and its
  identification with the invariant measures of total mass one of the diagonal action;
* `TauCeti.Probability.jointlyDissociated_iff_mem_extremePoints` — **joint dissociation is
  extremality** among jointly exchangeable probability laws, with
  `jointlyDissociated_of_mem_extremePoints` reading dissociation off an extreme point;
* `TauCeti.Probability.JointlyDissociated.ae_eq_of_comp_eq` — the integral form: a jointly
  dissociated law written as a mixture of jointly exchangeable laws has almost every component
  equal to itself.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory TauCeti.MeasureTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- A finite law on `ℕ × ℕ → α` invariant under the finitary diagonal action is jointly
exchangeable: invariant under the diagonal relabelling by every permutation of `ℕ`. -/
theorem jointlyExchangeable_of_smulInvariantMeasure {ρ : Measure (ℕ × ℕ → α)}
    [IsFiniteMeasure ρ] [SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ] :
    JointlyExchangeable ρ fun p x => x p := by
  rw [jointlyExchangeable_iff]
  intro σ
  have hmeas : ∀ π : Equiv.Perm ℕ,
      AEMeasurable (fun x : ℕ × ℕ → α => fun p : ℕ × ℕ => x (π p.1, π p.2)) ρ :=
    fun π => (Measurable.of_eval fun p => measurable_pi_apply (π p.1, π p.2)).aemeasurable
  rw [ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq (hmeas σ)
    (Measurable.of_eval fun p => measurable_pi_apply p).aemeasurable]
  intro F
  -- a finitely supported permutation agreeing with `σ` on every index `F` reads
  obtain ⟨τ, hτfin, hτ⟩ := Equiv.Perm.exists_finite_compl_fixedBy_apply_eq_on_finset σ
    (F.image Prod.fst ∪ F.image Prod.snd)
  -- the law is invariant under `τ`, read through the action
  have hτinv : (ρ.map fun x : ℕ × ℕ → α => fun p : ℕ × ℕ => x (τ p.1, τ p.2))
      = ρ.map fun x : ℕ × ℕ → α => fun p : ℕ × ℕ => x p := by
    have hτ' : (MulAction.fixedBy ℕ τ⁻¹)ᶜ.Finite := by
      simpa only [MulAction.fixedBy_inv ℕ] using hτfin
    have h := SMulInvariantMeasure.measure_preimage_smul (μ := ρ) (FinitaryPerm.ofPerm τ⁻¹ hτ')
    ext s hs
    rw [Measure.map_apply (Measurable.of_eval fun p => measurable_pi_apply (τ p.1, τ p.2)) hs,
      Measure.map_apply (Measurable.of_eval fun p => measurable_pi_apply p) hs]
    have hfun : pairReindex τ τ = fun x : ℕ × ℕ → α => fun p : ℕ × ℕ => x (τ p.1, τ p.2) :=
      funext fun x => funext fun p => pairReindex_apply _ _ x p
    have := h hs
    simp only [finitaryPerm_smul_array_def, FinitaryPerm.toPerm_ofPerm, inv_inv, hfun] at this
    exact this
  have hτmap := (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq (hmeas τ)
    (Measurable.of_eval fun p => measurable_pi_apply p).aemeasurable).mp hτinv F
  have heq : (fun x : ℕ × ℕ → α => F.restrict fun p : ℕ × ℕ => x (τ p.1, τ p.2))
      = fun x : ℕ × ℕ → α => F.restrict fun p : ℕ × ℕ => x (σ p.1, σ p.2) := by
    funext x p
    obtain ⟨q, hq⟩ := p
    have h1 : τ q.1 = σ q.1 := hτ _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq))
    have h2 : τ q.2 = σ q.2 := hτ _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq))
    simp only [Finset.restrict_def, h1, h2]
  rwa [heq] at hτmap

/-- A finite law is jointly exchangeable if and only if it is invariant under the finitary
diagonal action. -/
theorem jointlyExchangeable_iff_smulInvariantMeasure {ρ : Measure (ℕ × ℕ → α)}
    [IsFiniteMeasure ρ] :
    JointlyExchangeable ρ (fun p x => x p) ↔ SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ :=
  ⟨JointlyExchangeable.smulInvariantMeasure, fun _ => jointlyExchangeable_of_smulInvariantMeasure⟩

/-- The convex set of jointly exchangeable probability laws on array path space. -/
def jointlyExchangeableProbabilityMeasures (α : Type*) [MeasurableSpace α] :
    Set (Measure (ℕ × ℕ → α)) :=
  {ν | JointlyExchangeable ν (fun p x => x p) ∧ IsProbabilityMeasure ν}

/-- Membership in the jointly exchangeable probability laws. -/
@[simp]
theorem mem_jointlyExchangeableProbabilityMeasures_iff {ν : Measure (ℕ × ℕ → α)} :
    ν ∈ jointlyExchangeableProbabilityMeasures α
      ↔ JointlyExchangeable ν (fun p x => x p) ∧ IsProbabilityMeasure ν :=
  Iff.rfl

/-- The jointly exchangeable probability laws are the probability laws invariant under the
diagonal finitary action. -/
theorem jointlyExchangeableProbabilityMeasures_eq :
    jointlyExchangeableProbabilityMeasures α
      = invariantMeasuresOfMeasureUnivEq FinitaryPerm (ℕ × ℕ → α) 1 := by
  ext ν
  rw [mem_invariantMeasuresOfMeasureUnivEq_iff]
  constructor
  · rintro ⟨hν, hp⟩; exact ⟨hν.smulInvariantMeasure, hp.measure_univ⟩
  · rintro ⟨hν, hp⟩
    have : IsProbabilityMeasure ν := ⟨hp⟩
    exact ⟨jointlyExchangeable_of_smulInvariantMeasure, inferInstance⟩

/-- The jointly exchangeable probability laws form a convex set. -/
theorem convex_jointlyExchangeableProbabilityMeasures :
    Convex ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α) := by
  rw [jointlyExchangeableProbabilityMeasures_eq]; exact convex_invariantMeasuresOfMeasureUnivEq

/-- **Joint dissociation is extremality**: a jointly exchangeable probability law is an extreme
point of the jointly exchangeable probability laws if and only if its coordinate array is jointly
dissociated. -/
theorem jointlyDissociated_iff_mem_extremePoints {ρ : Measure (ℕ × ℕ → α)}
    [IsProbabilityMeasure ρ] (hexch : JointlyExchangeable ρ fun p x => x p) :
    JointlyDissociated ρ (fun p x => x p)
      ↔ ρ ∈ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α) := by
  rw [jointlyDissociated_iff_ergodicSMul hexch, jointlyExchangeableProbabilityMeasures_eq]
  exact ErgodicSMul.iff_mem_extremePoints

/-- An extreme point of the jointly exchangeable probability laws is jointly exchangeable. -/
theorem jointlyExchangeable_of_mem_extremePoints {ρ : Measure (ℕ × ℕ → α)}
    (h : ρ ∈ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α)) :
    JointlyExchangeable ρ fun p x => x p :=
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
    JointlyDissociated ρ fun p x => x p :=
  have := isProbabilityMeasure_of_mem_extremePoints h
  (jointlyDissociated_iff_mem_extremePoints (jointlyExchangeable_of_mem_extremePoints h)).2 h

open ProbabilityTheory in
/-- **A jointly dissociated array law is not a nontrivial mixture of jointly exchangeable
laws.** If `ρ` is the mixture `κ ∘ₘ π` of a Markov kernel whose laws are almost all jointly
exchangeable, then almost every `κ z` is `ρ` itself. This is the integral form of
`jointlyDissociated_iff_mem_extremePoints`. -/
theorem JointlyDissociated.ae_eq_of_comp_eq [StandardBorelSpace α] {Z : Type*}
    [MeasurableSpace Z] {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ] {π : Measure Z}
    {κ : Kernel Z (ℕ × ℕ → α)} [IsMarkovKernel κ]
    (hρ : JointlyDissociated ρ fun p x => x p)
    (hκ : ∀ᵐ z ∂π, JointlyExchangeable (κ z) fun p x => x p) (hmix : κ ∘ₘ π = ρ) :
    ∀ᵐ z ∂π, κ z = ρ := by
  have hinv : ∀ᵐ z ∂π, SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) (κ z) :=
    hκ.mono fun _ hz => hz.smulInvariantMeasure
  have : SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ := hmix ▸ smulInvariantMeasure_comp hinv
  have := ergodicSMul_of_jointlyDissociated hρ
  exact ErgodicSMul.ae_eq_of_comp_eq hinv hmix

end Probability

end TauCeti
