/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Generator
import TauCeti.Dynamics.Ergodic.MeasureEntropy.Factor

/-!
# The Kolmogorov–Sinai theorem for two-sided generators

Let `e : X ≃ᵐ X` preserve a probability measure `μ`. A measurable countable label `ξ` of finite
entropy is a two-sided generator when the σ-algebras of the labels `ξ ∘ e^[k]` and
`ξ ∘ e.symm^[k]`, `k : ℕ`, generate the σ-algebra of `X` modulo `μ`-null sets. Then
`h_μ(e) = h_μ(e, ξ)`.

The proof runs the one-sided argument with the windows
`windowLabel e ξ N x = (ξ (e^[j - N] x))_{0 ≤ j ≤ 2 N}`, the itinerary of length `2 N + 1` started
at `e.symm^[N] x`. Their σ-algebras increase (`TauCeti.monotone_comap_windowLabel`) and contain
those of the forward and backward labels (`TauCeti.iSup_comap_le_iSup_comap_windowLabel`), and each
has entropy rate at most `h_μ(e, ξ)`, since `e.symm^[N]` is a factor map from `e` to
itself (`TauCeti.partitionEntropyRate_windowLabel_le`); then
`TauCeti.partitionEntropyRate_le_of_monotone_comap` applies.

## Main definitions

* `TauCeti.windowLabel e ξ N`: the labels `ξ ∘ e^[j - N]`, `0 ≤ j ≤ 2 N`, of a point.

## Main results

* `TauCeti.partitionEntropyRate_le_of_twoSidedGenerator`: `h(e, η) ≤ h(e, ξ)` for every
  measurable finite label `η` and two-sided generator `ξ`.
* `TauCeti.measureEntropy_eq_partitionEntropyRate_of_twoSidedGenerator`: the Kolmogorov–Sinai
  theorem for two-sided generators.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Definition 4.4 and Theorem 4.4, p. 111.
-/

public section

open MeasureTheory Function
open scoped ENNReal

namespace TauCeti

variable {X ι κ : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- The window of width `2 N + 1` of a label `ξ` along an invertible map `e`: the labels
`ξ (e^[j] (e.symm^[N] x))`, `j < 2 N + 1`, that is `ξ ∘ e^[j - N]` for `0 ≤ j ≤ 2 N`. -/
noncomputable def windowLabel (e : X ≃ X) (ξ : X → ι) (N : ℕ) : X → (Fin (2 * N + 1) → ι) :=
  iteratedPartitionLabel e ξ (2 * N + 1) ∘ e.symm^[N]

/-- The entries of a window. -/
@[simp]
theorem windowLabel_apply (e : X ≃ X) (ξ : X → ι) (N : ℕ) (x : X) (j : Fin (2 * N + 1)) :
    windowLabel e ξ N x j = ξ (e^[j] (e.symm^[N] x)) := by
  rw [windowLabel, comp_apply, iteratedPartitionLabel_apply]

/-- A narrower window is a function of a wider one. -/
theorem windowLabel_eq_comp_of_le (e : X ≃ X) (ξ : X → ι) {N N' : ℕ} (h : N ≤ N') :
    windowLabel e ξ N =
      (fun w : Fin (2 * N' + 1) → ι ↦ fun j : Fin (2 * N + 1) ↦
        w ⟨j + (N' - N), by omega⟩) ∘ windowLabel e ξ N' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  funext x j
  simp only [comp_apply, windowLabel_apply, Nat.add_sub_cancel_left]
  rw [add_comm N d, iterate_add_apply, iterate_add_apply, e.rightInverse_symm.iterate d]

variable [MeasurableSpace ι]

/-- The windows are measurable. -/
theorem measurable_windowLabel {e : X ≃ X} (he : Measurable e) (hes : Measurable e.symm)
    {ξ : X → ι} (hξ : Measurable ξ) (N : ℕ) : Measurable (windowLabel e ξ N) :=
  (measurable_iteratedPartitionLabel he hξ _).comp (hes.iterate N)

/-- The σ-algebras of the windows increase. -/
theorem monotone_comap_windowLabel (e : X ≃ X) (ξ : X → ι) :
    Monotone fun N ↦ MeasurableSpace.comap (windowLabel e ξ N) inferInstance := fun _ _ h ↦
  MeasurableSpace.comap_le_comap_of_eq_comp _
    (measurable_pi_iff.mpr fun _ ↦ measurable_pi_apply _) (windowLabel_eq_comp_of_le e ξ h)

/-- The σ-algebras of the labels `ξ ∘ e^[k]` and `ξ ∘ e.symm^[k]` lie in those of the windows. -/
theorem iSup_comap_le_iSup_comap_windowLabel (e : X ≃ X) (ξ : X → ι) :
    (⨆ k : ℕ, MeasurableSpace.comap (fun x ↦ ξ (e^[k] x)) ‹MeasurableSpace ι› ⊔
        MeasurableSpace.comap (fun x ↦ ξ (e.symm^[k] x)) ‹MeasurableSpace ι›) ≤
      ⨆ N, MeasurableSpace.comap (windowLabel e ξ N) inferInstance := by
  refine iSup_le fun k ↦ le_iSup_of_le k (sup_le ?_ ?_)
  · refine MeasurableSpace.comap_le_comap_of_eq_comp
      (fun w : Fin (2 * k + 1) → ι ↦ w ⟨2 * k, by omega⟩) (measurable_pi_apply _) ?_
    funext x
    simp only [comp_apply, windowLabel_apply]
    rw [two_mul, iterate_add_apply, e.rightInverse_symm.iterate k]
  · refine MeasurableSpace.comap_le_comap_of_eq_comp
      (fun w : Fin (2 * k + 1) → ι ↦ w ⟨0, by omega⟩) (measurable_pi_apply _) ?_
    funext x
    simp [windowLabel_apply]

variable [Countable ι] [MeasurableSingletonClass ι]

/-- The windows of `ξ` have entropy rate at most that of `ξ`: `e.symm^[N]` is a factor map from
`e` to itself, so the window has the rate of an itinerary of `ξ`. -/
theorem partitionEntropyRate_windowLabel_le [IsZeroOrProbabilityMeasure μ] (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) {ξ : X → ι} (hξ : Measurable ξ) (N : ℕ) :
    partitionEntropyRate μ e (windowLabel e.toEquiv ξ N) ≤ partitionEntropyRate μ e ξ := by
  have hcomm : Function.Commute e.symm e := fun x ↦ by simp
  have hπ : IsFactorMap (e.symm^[N]) e e μ μ :=
    .of_semiconj (he.symm.iterate N) (hcomm.iterate_left N)
  rw [windowLabel, MeasurableEquiv.coe_toEquiv_symm]
  calc partitionEntropyRate μ e (iteratedPartitionLabel e ξ (2 * N + 1) ∘ e.symm^[N])
      = partitionEntropyRate μ e (iteratedPartitionLabel e ξ (2 * N + 1)) :=
        hπ.partitionEntropyRate_comp he.quasiMeasurePreserving e.measurable
          (measurable_iteratedPartitionLabel e.measurable hξ _)
    _ ≤ partitionEntropyRate μ e ξ := partitionEntropyRate_iteratedPartitionLabel_le he hξ _

variable [IsProbabilityMeasure μ]

/-- The entropy rate of a measurable finite label is at most that of a two-sided generator. -/
theorem partitionEntropyRate_le_of_twoSidedGenerator (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {ξ : X → ι} (hξ : Measurable ξ)
    (hgen : ∀ s : Set X, MeasurableSet s → ∃ t : Set X,
      MeasurableSet[⨆ k : ℕ, MeasurableSpace.comap (fun x ↦ ξ (e^[k] x)) ‹_› ⊔
        MeasurableSpace.comap (fun x ↦ ξ (e.symm^[k] x)) ‹_›] t ∧ s =ᵐ[μ] t)
    [Finite κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] {η : X → κ}
    (hη : Measurable η) :
    partitionEntropyRate μ e η ≤ partitionEntropyRate μ e ξ :=
  partitionEntropyRate_le_of_monotone_comap he
    (measurable_windowLabel e.measurable e.symm.measurable hξ)
    (monotone_comap_windowLabel e.toEquiv ξ)
    (fun s hs ↦ (hgen s hs).imp fun _ ht ↦
      ⟨iSup_comap_le_iSup_comap_windowLabel e.toEquiv ξ _ ht.1, ht.2⟩)
    (partitionEntropyRate_windowLabel_le e he hξ) hη

/-- **The Kolmogorov–Sinai theorem for two-sided generators.** Let `e : X ≃ᵐ X` preserve a
probability measure `μ`, and let `ξ` be a measurable countable label of finite entropy whose
labels `ξ ∘ e^[k]` and `ξ ∘ e.symm^[k]`, `k : ℕ`, generate the σ-algebra of `X` modulo `μ`-null
sets. Then the Kolmogorov–Sinai entropy is the entropy rate of `ξ` (Sarig 2023, Theorem 4.4). -/
theorem measureEntropy_eq_partitionEntropyRate_of_twoSidedGenerator (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) {ξ : X → ι} (hξ : Measurable ξ)
    (hH : countablePartitionEntropy μ ξ ≠ ∞)
    (hgen : ∀ s : Set X, MeasurableSet s → ∃ t : Set X,
      MeasurableSet[⨆ k : ℕ, MeasurableSpace.comap (fun x ↦ ξ (e^[k] x)) ‹_› ⊔
        MeasurableSpace.comap (fun x ↦ ξ (e.symm^[k] x)) ‹_›] t ∧ s =ᵐ[μ] t) :
    measureEntropy μ e = partitionEntropyRate μ e ξ := by
  refine le_antisymm ?_ (partitionEntropyRate_le_measureEntropy_of_countable e hξ hH)
  rw [measureEntropy_eq_iSup_fin he]
  exact iSup₂_le fun n η ↦ iSup_le fun hη ↦
    partitionEntropyRate_le_of_twoSidedGenerator e he hξ hgen hη

end TauCeti
