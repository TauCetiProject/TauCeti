/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import TauCeti.Probability.Independence.InfinitePi

/-!
# Independent and identically distributed families

A family of random variables `X : ι → Ω → E` on `(Ω, μ)` is **independent and identically
distributed** with common law `P` if each `X i` is measurable, the family is mutually independent
under `μ`, and every `X i` pushes `μ` forward to `P`.

This file provides the basic API for `TauCeti.IsIndependentIdenticallyDistributed`: projections to
measurability, mutual and pairwise independence, identical distribution, `MeasurePreserving`,
`HasLaw`, composition with measurable statistics, restriction along injective index maps, canonical
coordinate witnesses on `Measure.pi` and `Measure.infinitePi`, and the strong and weak laws of
large numbers for Banach-space-valued integrable statistics.

## Main definitions

* `TauCeti.IsIndependentIdenticallyDistributed` — a measurable, mutually independent family with a
  named common law `P`.

## Main statements

* `TauCeti.isIndependentIdenticallyDistributed_iff` — definitional characterization.
* `TauCeti.IsIndependentIdenticallyDistributed.comp` — measurable statistics of an i.i.d. family
  are i.i.d.
* `TauCeti.isIndependentIdenticallyDistributed_eval_pi` and
  `TauCeti.isIndependentIdenticallyDistributed_eval_infinitePi` — coordinate projections on
  product spaces are i.i.d.
* `TauCeti.ae_tendsto_sampleMean_of_iid` and `TauCeti.tendstoInMeasure_sampleMean_of_iid` —
  strong and weak laws of large numbers for an integrable statistic of an i.i.d. sequence.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Proposition 2.16,
  pp. 15–16.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace TauCeti

section Defs

variable {Ω E F ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- A family of random variables `X : ι → Ω → E` on `(Ω, μ)` is **independent and identically
distributed** with common law `P` if each `X i` is measurable, the family `X` is mutually
independent under `μ`, and every `X i` has law `P`. -/
def IsIndependentIdenticallyDistributed (μ : Measure Ω) (X : ι → Ω → E) (P : Measure E) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, μ.map (X i) = P

/-- Characterization of `IsIndependentIdenticallyDistributed`. -/
theorem isIndependentIdenticallyDistributed_iff {μ : Measure Ω} {X : ι → Ω → E} {P : Measure E} :
    IsIndependentIdenticallyDistributed μ X P ↔
      (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, μ.map (X i) = P :=
  Iff.rfl

variable {μ : Measure Ω} {X : ι → Ω → E} {P : Measure E}

/-- Each coordinate of an i.i.d. family is measurable. -/
theorem IsIndependentIdenticallyDistributed.measurable
    (h : IsIndependentIdenticallyDistributed μ X P) (i : ι) : Measurable (X i) :=
  h.1 i

/-- Each coordinate of an i.i.d. family is almost-everywhere measurable. -/
theorem IsIndependentIdenticallyDistributed.aemeasurable
    (h : IsIndependentIdenticallyDistributed μ X P) (i : ι) : AEMeasurable (X i) μ :=
  (h.measurable i).aemeasurable

/-- The coordinates of an i.i.d. family are mutually independent. -/
theorem IsIndependentIdenticallyDistributed.iIndepFun
    (h : IsIndependentIdenticallyDistributed μ X P) : iIndepFun X μ :=
  h.2.1

/-- Each coordinate of an i.i.d. family has pushforward law `P`. -/
theorem IsIndependentIdenticallyDistributed.map_eq
    (h : IsIndependentIdenticallyDistributed μ X P) (i : ι) : μ.map (X i) = P :=
  h.2.2 i

/-- The underlying measure of an i.i.d. family is automatically a probability measure. -/
theorem IsIndependentIdenticallyDistributed.isProbabilityMeasure
    (h : IsIndependentIdenticallyDistributed μ X P) : IsProbabilityMeasure μ :=
  h.iIndepFun.isProbabilityMeasure

/-- Each coordinate of an i.i.d. family is measure-preserving into the common law `P`. -/
theorem IsIndependentIdenticallyDistributed.measurePreserving
    (h : IsIndependentIdenticallyDistributed μ X P) (i : ι) : MeasurePreserving (X i) μ P :=
  ⟨h.measurable i, h.map_eq i⟩

/-- Each coordinate of an i.i.d. family satisfies `ProbabilityTheory.HasLaw` with law `P`. -/
theorem IsIndependentIdenticallyDistributed.hasLaw
    (h : IsIndependentIdenticallyDistributed μ X P) (i : ι) : HasLaw (X i) P μ :=
  ⟨h.aemeasurable i, h.map_eq i⟩

/-- The common law of a nonempty i.i.d. family is a probability measure. -/
theorem IsIndependentIdenticallyDistributed.isProbabilityMeasure_law [Nonempty ι]
    (h : IsIndependentIdenticallyDistributed μ X P) : IsProbabilityMeasure P :=
  let ⟨i⟩ := ‹Nonempty ι›
  (h.hasLaw i).isProbabilityMeasure_iff.1 h.isProbabilityMeasure

/-- Distinct coordinates of an i.i.d. family are independent. -/
theorem IsIndependentIdenticallyDistributed.indepFun
    (h : IsIndependentIdenticallyDistributed μ X P) {i j : ι} (hij : i ≠ j) :
    IndepFun (X i) (X j) μ :=
  h.iIndepFun.indepFun hij

/-- The coordinates of an i.i.d. family are pairwise independent. -/
theorem IsIndependentIdenticallyDistributed.pairwise_indepFun
    (h : IsIndependentIdenticallyDistributed μ X P) :
    Pairwise fun i j ↦ IndepFun (X i) (X j) μ :=
  fun _ _ hij ↦ h.indepFun hij

/-- Any two coordinates of an i.i.d. family are identically distributed. -/
theorem IsIndependentIdenticallyDistributed.identDistrib
    (h : IsIndependentIdenticallyDistributed μ X P) (i j : ι) :
    IdentDistrib (X i) (X j) μ μ :=
  (h.hasLaw i).identDistrib (h.hasLaw j)

/-- Applying a measurable statistic coordinatewise preserves the i.i.d. property, pushing the common
law forward to `P.map s`. -/
theorem IsIndependentIdenticallyDistributed.comp [MeasurableSpace F]
    (h : IsIndependentIdenticallyDistributed μ X P) {s : E → F} (hs : Measurable s) :
    IsIndependentIdenticallyDistributed μ (fun i ω ↦ s (X i ω)) (P.map s) := by
  refine ⟨fun i ↦ hs.comp (h.measurable i), h.iIndepFun.comp (fun _ ↦ s) (fun _ ↦ hs), fun i ↦ ?_⟩
  rw [← h.map_eq i, Measure.map_map hs (h.measurable i)]
  rfl

/-- Precomposing an i.i.d. family along an injective index map yields an i.i.d. family with the same
common law. -/
theorem IsIndependentIdenticallyDistributed.precomp
    (h : IsIndependentIdenticallyDistributed μ X P) {g : κ → ι} (hg : Function.Injective g) :
    IsIndependentIdenticallyDistributed μ (fun k ↦ X (g k)) P :=
  ⟨fun k ↦ h.measurable (g k), h.iIndepFun.precomp hg, fun k ↦ h.map_eq (g k)⟩

/-- The coordinate projections on a finite product `Measure.pi (fun _ : ι ↦ P)` of a probability
measure `P` form an i.i.d. family with law `P`. -/
theorem isIndependentIdenticallyDistributed_eval_pi [Fintype ι] (P : Measure E)
    [IsProbabilityMeasure P] :
    IsIndependentIdenticallyDistributed (Measure.pi fun _ : ι ↦ P)
      (fun (i : ι) (x : ι → E) ↦ x i) P := by
  refine ⟨fun i ↦ measurable_pi_apply i, ?_, fun i ↦ (measurePreserving_eval _ i).map_eq⟩
  exact iIndepFun_pi (μ := fun _ : ι ↦ P) (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)

/-- The coordinate projections on `Measure.infinitePi (fun _ : ι ↦ P)` of a probability measure `P`
form an i.i.d. family with law `P`, for any index type `ι`. -/
theorem isIndependentIdenticallyDistributed_eval_infinitePi (P : Measure E)
    [IsProbabilityMeasure P] :
    IsIndependentIdenticallyDistributed (Measure.infinitePi fun _ : ι ↦ P)
      (fun (i : ι) (x : ι → E) ↦ x i) P :=
  ⟨fun i ↦ measurable_pi_apply i,
    TauCeti.Probability.iIndepFun_eval_infinitePi (fun _ : ι ↦ P),
    fun i ↦ Measure.infinitePi_map_eval (fun _ : ι ↦ P) i⟩

end Defs

section LawOfLargeNumbers

variable {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]

/-- **Strong law of large numbers for an integrable statistic of an i.i.d. sequence.** If `X` is
i.i.d. with law `P` and `s : E → F` is `P`-integrable into a Banach space `F`, then the sample
means `n⁻¹ • ∑_{i < n} s (X i ω)` converge `μ`-almost everywhere to `∫ y, s y ∂P`. No extra
measurability hypothesis on `s` is needed beyond `Integrable s P`. -/
theorem ae_tendsto_sampleMean_of_iid {μ : Measure Ω} {X : ℕ → Ω → E} {P : Measure E}
    (h : IsIndependentIdenticallyDistributed μ X P) {s : E → F} (hs : Integrable s P) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, s (X i ω)) atTop
      (𝓝 (∫ y, s y ∂P)) := by
  have := h.isProbabilityMeasure
  have hs_aem : ∀ i : ℕ, AEMeasurable s (μ.map (X i)) := fun i ↦ by
    rw [h.map_eq i]
    exact hs.1.aemeasurable
  have hident : ∀ i : ℕ, IdentDistrib (fun ω ↦ s (X i ω)) (fun ω ↦ s (X 0 ω)) μ μ := fun i ↦
    (h.identDistrib i 0).comp_of_aemeasurable (hs_aem i)
  have hindep : Pairwise fun i j : ℕ ↦ IndepFun (fun ω ↦ s (X i ω)) (fun ω ↦ s (X j ω)) μ :=
    fun _ _ hij ↦ (h.iIndepFun.comp₀ (fun _ ↦ s) h.aemeasurable hs_aem).indepFun hij
  have hint0 : Integrable (fun ω ↦ s (X 0 ω)) μ :=
    ((h.measurePreserving 0).integrable_comp hs.1).2 hs
  have hmean : ∫ ω, s (X 0 ω) ∂μ = ∫ y, s y ∂P := (h.hasLaw 0).integral_comp hs.1
  simpa only [hmean] using strong_law_ae (fun i ω ↦ s (X i ω)) hint0 hindep hident

/-- **Weak law of large numbers for an integrable statistic of an i.i.d. sequence.** If `X` is
i.i.d. with law `P` and `s : E → F` is `P`-integrable into a Banach space `F`, then the sample
means `n⁻¹ • ∑_{i < n} s (X i ω)` converge in probability to `∫ y, s y ∂P`. -/
theorem tendstoInMeasure_sampleMean_of_iid {μ : Measure Ω} {X : ℕ → Ω → E} {P : Measure E}
    (h : IsIndependentIdenticallyDistributed μ X P) {s : E → F} (hs : Integrable s P) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, s (X i ω)) atTop
      (fun _ ↦ ∫ y, s y ∂P) := by
  have := h.isProbabilityMeasure
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, s (X i ω)) μ := fun n ↦ by
    have hsum := (Finset.aestronglyMeasurable_sum (Finset.range n) fun i _ ↦
      hs.1.comp_measurePreserving (h.measurePreserving i)).const_smul (n : ℝ)⁻¹
    convert hsum using 1
    ext ω
    simp [Finset.sum_apply]
  exact tendstoInMeasure_of_tendsto_ae hmeas (ae_tendsto_sampleMean_of_iid h hs)

end LawOfLargeNumbers

end TauCeti
