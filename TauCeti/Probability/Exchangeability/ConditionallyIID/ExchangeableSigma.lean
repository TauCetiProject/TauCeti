/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.PathDisintegration
public import TauCeti.Probability.Exchangeability.PathSpace.HewittSavage
import TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# Exchangeable events of a conditionally i.i.d. process are events of its directing measure

Let `X` be conditionally i.i.d. with directing measure `ν`. Given `ν ω = P`, the path of `X` is an
i.i.d. `P` sequence, so by the Hewitt–Savage zero-one law every exchangeable event `s` has
conditional probability `P^{⊗ℕ} s ∈ {0, 1}`. The event `{X ∈ s}` therefore agrees, up to a `μ`-null
set, with the event `{ν ∈ D}` for `D = {P | P^{⊗ℕ} s = 1}`.

Consequently every σ-algebra for which the directing measure is measurable contains each
exchangeable event of the process up to a null set. Applied to a directing measure that is
measurable for the tail or the shift-invariant σ-algebra, this identifies those σ-algebras with the
exchangeable σ-algebra modulo null sets.

## Main results

* `TauCeti.Probability.ConditionallyIIDWith.preimage_ae_eq_preimage_directing` — an exchangeable
  event of the path agrees almost everywhere with the event that the directing measure lies in
  `{P | P^{⊗ℕ} s = 1}`.
* `TauCeti.Probability.ConditionallyIIDWith.exists_measurableSet_ae_eq` — if the directing measure
  is measurable for a σ-algebra `m`, every exchangeable event of the path agrees almost everywhere
  with an `m`-measurable event.

## Implementation

The proof reads the joint law of `(ν, X)` through the full-path disintegration
`ConditionallyIIDWith.jointPathLaw_eq_iidMixtureLaw`: the measure of `{ν ∈ A, X ∈ B}` is the
integral of `δ_P(A) · P^{⊗ℕ}(B)` against the mixing law, which vanishes as soon as `P^{⊗ℕ}(B) = 0`
for every `P ∈ A`. The two halves of the symmetric difference are rectangles of this kind, with
`(A, B) = (Dᶜ, s)` and `(D, sᶜ)`.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1,
  where the directing measure, the tail σ-field and the exchangeable σ-field are shown to agree
  almost surely.
* E. Hewitt and L. J. Savage, "Symmetric measures on Cartesian products", *Transactions of the
  American Mathematical Society* 80 (1955), 470–501.

No material is adapted from `cameronfreer/exchangeability`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}

/-- The event `{ν ∈ A, X ∈ B}` is null when `B` is null under the i.i.d. law of every `P ∈ A`. -/
private theorem ConditionallyIIDWith.measure_preimage_inter_eq_zero [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) {A : Set (ProbabilityMeasure α)} {B : Set (ℕ → α)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ P ∈ A, Measure.infinitePi (fun _ : ℕ => (P : Measure α)) B = 0) :
    μ (ν ⁻¹' A ∩ (fun ω i => X i ω) ⁻¹' B) = 0 := by
  have hpair : AEMeasurable (fun ω => (ν ω, fun i => X i ω)) μ :=
    h.measurable_directing.aemeasurable.prodMk (AEMeasurable.of_eval h.aemeasurable)
  have hpre : ν ⁻¹' A ∩ (fun ω i => X i ω) ⁻¹' B =
      (fun ω => (ν ω, fun i => X i ω)) ⁻¹' (A ×ˢ B) := (Set.mk_preimage_prod _ _).symm
  have hfibre (P : ProbabilityMeasure α) :
      ((Measure.dirac P).prod (Measure.infinitePi fun _ : ℕ => (P : Measure α))) (A ×ˢ B) = 0 := by
    rw [Measure.prod_prod]
    by_cases hP : P ∈ A
    · rw [hAB P hP, mul_zero]
    · rw [Measure.dirac_apply' P hA, Set.indicator_of_notMem hP, zero_mul]
  rw [hpre, ← Measure.map_apply_of_aemeasurable hpair (hA.prod hB), ← jointPathLaw_def,
    h.jointPathLaw_eq_iidMixtureLaw, iidMixtureLaw_def, Measure.bind_apply (hA.prod hB)
      (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const id measurable_id).aemeasurable]
  simp only [id_eq, hfibre, lintegral_zero]

/-- **Exchangeable events are events of the directing measure.** For a conditionally i.i.d.
process with directing measure `ν`, an exchangeable path event `s` occurs, up to a null set,
exactly when `ν` lies in the set of laws `P` under which `s` is almost sure for an i.i.d. `P`
sequence.

The Hewitt–Savage zero-one law makes `P^{⊗ℕ} s` equal to `0` or `1` for each `P`, and conditionally
on `ν ω = P` the path is i.i.d. `P`. -/
theorem ConditionallyIIDWith.preimage_ae_eq_preimage_directing [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) {s : Set (ℕ → α)}
    (hs : MeasurableSet[exchangeableSigma α] s) :
    (fun ω i => X i ω) ⁻¹' s =ᵐ[μ]
      ν ⁻¹' {P | Measure.infinitePi (fun _ : ℕ => (P : Measure α)) s = 1} := by
  have hs' : MeasurableSet s := exchangeableSigma_le _ hs
  set D := {P : ProbabilityMeasure α | Measure.infinitePi (fun _ : ℕ => (P : Measure α)) s = 1}
  have hD : MeasurableSet D :=
    ((Measure.measurable_coe hs').comp TauCeti.MeasureTheory.measurable_infinitePi_const)
      (measurableSet_singleton 1)
  rw [ae_eq_set]
  constructor
  · rw [Set.sdiff_eq, Set.inter_comm, ← Set.preimage_compl]
    exact h.measure_preimage_inter_eq_zero hD.compl hs' fun P hP =>
      (exchangeableSigma_trivial_of_infinitePi P hs).resolve_right hP
  · rw [Set.sdiff_eq, ← Set.preimage_compl]
    exact h.measure_preimage_inter_eq_zero hD hs'.compl fun P hP =>
      (prob_compl_eq_zero_iff hs').2 hP

/-- **Exchangeable events are measurable for the directing measure's σ-algebra, up to null sets.**
If the directing measure `ν` of a conditionally i.i.d. process is measurable for a σ-algebra `m`
on the sample space, then every exchangeable path event agrees almost everywhere with an
`m`-measurable event. -/
theorem ConditionallyIIDWith.exists_measurableSet_ae_eq [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) {m : MeasurableSpace Ω} (hν : Measurable[m] ν)
    {s : Set (ℕ → α)} (hs : MeasurableSet[exchangeableSigma α] s) :
    ∃ t : Set Ω, MeasurableSet[m] t ∧ (fun ω i => X i ω) ⁻¹' s =ᵐ[μ] t :=
  -- The ambient σ-algebra is passed by name: `m` is also a local `MeasurableSpace Ω` instance and
  -- would otherwise be the one synthesized.
  ⟨_, hν (((Measure.measurable_coe (exchangeableSigma_le _ hs)).comp
      TauCeti.MeasureTheory.measurable_infinitePi_const) (measurableSet_singleton 1)),
    h.preimage_ae_eq_preimage_directing (mΩ := mΩ) hs⟩

end Probability

end TauCeti
