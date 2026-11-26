/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.IsomorphicModNull
public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Basic

/-!
# Measure entropy of factors and of isomorphic systems

Let `π` be a factor map from `T` on `(X, μ)` to `S` on `(Y, ν)` (`TauCeti.IsFactorMap`). A label
`a` on `Y` pulls back to the label `a ∘ π` on `X`, whose itineraries under `T` are almost
everywhere the pullbacks of the itineraries of `a` under `S`. Since `π` preserves the measures,
the two labels have the same itinerary entropies and the same entropy rate, so the factor has
at most the entropy of the extension. Isomorphic systems mod 0 are factors of each other, so
they have the same entropy.

## Main results

* `TauCeti.IsFactorMap.partitionEntropyRate_comp`: `h_μ(T, a ∘ π) = h_ν(S, a)`.
* `TauCeti.IsFactorMap.measureEntropy_le`: a factor has at most the entropy of the extension,
  `h_ν(S) ≤ h_μ(T)`.
* `TauCeti.IsIsomorphicModNull.measureEntropy_eq`: the measure entropy is invariant under
  isomorphism mod 0; in particular (`TauCeti.measureEntropy_eq_of_measurableEquiv`) under
  conjugacy by a measure-preserving measurable equivalence.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Problem 4.3, p. 130.
-/

public section

open MeasureTheory Function
open scoped ENNReal

namespace TauCeti

variable {X Y ι : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  {μ : Measure X} {ν : Measure Y} {T : X → X} {S : Y → Y} {π : X → Y}

namespace IsFactorMap

/-- The itineraries under `T` of the pulled-back label `a ∘ π` are almost everywhere the
pullbacks of the itineraries of `a` under `S`. -/
theorem iteratedPartitionLabel_comp_ae_eq (h : IsFactorMap π T S μ ν)
    (hT : QuasiMeasurePreserving T μ μ) (a : Y → ι) (n : ℕ) :
    iteratedPartitionLabel T (a ∘ π) n =ᵐ[μ] iteratedPartitionLabel S a n ∘ π := by
  have hk : ∀ k : Fin n, ∀ᵐ x ∂μ, π (T^[k] x) = S^[k] (π x) := fun k ↦
    h.comp_iterate_ae_eq hT k
  filter_upwards [ae_all_iff.mpr hk] with x hx
  exact funext fun k ↦ by simp [hx k]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The pulled-back label `a ∘ π` has the itinerary entropies of `a`. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_comp (h : IsFactorMap π T S μ ν)
    (hT : QuasiMeasurePreserving T μ μ) (hS : Measurable S) {a : Y → ι} (ha : Measurable a)
    (n : ℕ) :
    countablePartitionEntropy μ (iteratedPartitionLabel T (a ∘ π) n) =
      countablePartitionEntropy ν (iteratedPartitionLabel S a n) := by
  rw [countablePartitionEntropy_congr_ae (h.iteratedPartitionLabel_comp_ae_eq hT a n),
    countablePartitionEntropy_comp_of_measurePreserving h.measurePreserving
      (measurable_iteratedPartitionLabel hS ha n)]

/-- The pulled-back label `a ∘ π` has the entropy rate of `a`: `h_μ(T, a ∘ π) = h_ν(S, a)`. -/
theorem partitionEntropyRate_comp (h : IsFactorMap π T S μ ν)
    (hT : QuasiMeasurePreserving T μ μ) (hS : Measurable S) {a : Y → ι} (ha : Measurable a) :
    partitionEntropyRate μ T (a ∘ π) = partitionEntropyRate ν S a := by
  simp only [partitionEntropyRate_def,
    h.countablePartitionEntropy_iteratedPartitionLabel_comp hT hS ha]

end IsFactorMap

/-- **Entropy of a factor.** If `π` is a factor map from `T` on `(X, μ)` to `S` on `(Y, ν)`, with
`T` quasi-measure-preserving and `S` measurable, then `h_ν(S) ≤ h_μ(T)`. -/
theorem IsFactorMap.measureEntropy_le (h : IsFactorMap π T S μ ν)
    (hT : QuasiMeasurePreserving T μ μ) (hS : Measurable S) :
    measureEntropy ν S ≤ measureEntropy μ T := by
  refine measureEntropy_le_iff.mpr fun a ha hfin ↦ ?_
  have hπ := h.measurePreserving
  rw [← h.partitionEntropyRate_comp hT hS ha]
  refine partitionEntropyRate_le_measureEntropy (ha.comp hπ.measurable) ?_
  rwa [countablePartitionEntropy_comp_of_measurePreserving hπ ha]

/-- **Isomorphism invariance.** Systems that are isomorphic mod 0 have the same measure entropy,
for measure-preserving `T` and measurable `S`. -/
theorem IsIsomorphicModNull.measureEntropy_eq (h : IsIsomorphicModNull T μ S ν)
    (hT : MeasurePreserving T μ μ) (hS : Measurable S) :
    measureEntropy μ T = measureEntropy ν S :=
  (isIsomorphicModNull_iff_nonempty.mp h).elim fun e ↦
    le_antisymm
      (e.isFactorMap_invFun.measureEntropy_le
        (e.isFactorMap.measurePreserving_target hT hS).quasiMeasurePreserving hT.measurable)
      (e.isFactorMap.measureEntropy_le hT.quasiMeasurePreserving hS)

/-- Systems conjugate by a measure-preserving measurable equivalence have the same measure
entropy, for measure-preserving `T`. -/
theorem measureEntropy_eq_of_measurableEquiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (hconj : Semiconj e T S) (hT : MeasurePreserving T μ μ) :
    measureEntropy μ T = measureEntropy ν S := by
  have hS : S = e ∘ T ∘ e.symm := funext fun y ↦ by simpa using (hconj (e.symm y)).symm
  exact (IsIsomorphicModNull.of_measurableEquiv e he hconj).measureEntropy_eq hT
    (hS ▸ e.measurable.comp (hT.measurable.comp e.symm.measurable))

end TauCeti
