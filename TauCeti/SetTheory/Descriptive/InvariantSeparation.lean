/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.MeasureTheory.Constructions.Polish.Analytic

/-!
# Invariant Lusin separation

Lusin's separation theorem (`MeasureTheory.AnalyticSet.measurablySeparable`) separates two
disjoint analytic sets by a Borel set. This file proves its invariant form: for an equivalence
relation `E` with analytic graph, two analytic sets no point of which is `E`-equivalent to a point
of the other are separated by an `E`-invariant Borel set. A set `C` is `E`-invariant when it equals
its saturation `Quotient.mk E ⁻¹' (Quotient.mk E '' C)`, and the `E`-invariant Borel sets are
exactly the preimages of the measurable sets of Mathlib's quotient σ-algebra on `Quotient E`. So
the invariant form is Lusin separation in `Quotient E`: the images of the two sets are measurably
separable there.

The separator is built by alternating Lusin separation with saturation. Separate the saturation
of `A` from the saturation of `B` by a Borel set, then the saturation of that Borel set (analytic,
as a Borel set has analytic saturation under an analytic relation) from the saturation of `B`, and
so on; the union of these countably many Borel sets is Borel, and it is invariant because each
stage contains the saturation of the previous one.

Countable families of measurable sets of `Quotient E` separating its points are how the classes of
`E` are separated by invariant Borel sets, so this is the input for showing that an equivalence
relation is smooth by separating its classes, for instance that a closed equivalence relation on a
Polish space is smooth.

## Main results

* `Setoid.measurablySeparable_image_quotientMk`: for `E` with analytic graph on a Hausdorff space
  whose σ-algebra contains the Borel sets, the images in `Quotient E` of two analytic sets with
  disjoint images are measurably separable.
* `Setoid.exists_invariant_measurableSet_separating`: the same separation stated in the space: an
  `E`-invariant measurable set (Borel, for the Borel σ-algebra) contains `A` and misses `B`.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 14.7 (the Lusin separation theorem).
* S. Gao, *Invariant Descriptive Set Theory*, CRC Press, 2009 (separation by invariant Borel
  sets for analytic equivalence relations, by alternating separation and saturation).
-/

public section

open MeasureTheory Set

namespace Setoid

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Invariant Lusin separation in the quotient, for the Borel σ-algebra itself. The construction
needs the stages to be Borel, so that their saturations are analytic. -/
private theorem measurablySeparable_image_quotientMk_of_borelSpace [MeasurableSpace X]
    [BorelSpace X] (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E p.1 p.2}) {A B : Set X} (hA : AnalyticSet A)
    (hB : AnalyticSet B) (hAB : Disjoint (Quotient.mk E '' A) (Quotient.mk E '' B)) :
    MeasurablySeparable (Quotient.mk E '' A) (Quotient.mk E '' B) := by
  -- One step: a set with analytic saturation, whose classes avoid those of `B`, has its
  -- saturation inside a Borel set whose classes still avoid those of `B`.
  have step (S : Set X) (hS : AnalyticSet (Quotient.mk E ⁻¹' (Quotient.mk E '' S)))
      (hSB : Disjoint (Quotient.mk E '' S) (Quotient.mk E '' B)) :
      ∃ T, MeasurableSet T ∧ Quotient.mk E ⁻¹' (Quotient.mk E '' S) ⊆ T ∧
        Disjoint (Quotient.mk E '' T) (Quotient.mk E '' B) := by
    obtain ⟨T, hST, hTB, hT⟩ :=
      hS.measurablySeparable (hE.preimage_image_quotientMk hB) (hSB.preimage _)
    exact ⟨T, hT, hST, disjoint_image_left.2 hTB.symm⟩
  -- Iterate the step on Borel sets, starting from `A`; Borel sets have analytic saturations.
  obtain ⟨T₀, hT₀, hAT₀, hT₀B⟩ := step A (hE.preimage_image_quotientMk hA) hAB
  choose next hnext hsub hdisj using fun T : {T : Set X //
      MeasurableSet T ∧ Disjoint (Quotient.mk E '' T) (Quotient.mk E '' B)} ↦
    step T.1 (hE.preimage_image_quotientMk_measurableSet T.2.1) T.2.2
  let f := fun T ↦ (⟨next T, hnext T, hdisj T⟩ : {T : Set X //
      MeasurableSet T ∧ Disjoint (Quotient.mk E '' T) (Quotient.mk E '' B)})
  let T n := (f^[n] ⟨T₀, hT₀, hT₀B⟩).1
  have hTsucc (n : ℕ) : Quotient.mk E ⁻¹' (Quotient.mk E '' T n) ⊆ T (n + 1) := by
    simp only [T, Function.iterate_succ_apply']
    exact hsub _
  -- The union of the stages is invariant, as each stage contains the saturation of the last.
  have hsat : Quotient.mk E ⁻¹' (Quotient.mk E '' ⋃ n, T n) = ⋃ n, T n := by
    refine (subset_preimage_image _ _).antisymm' ?_
    rw [image_iUnion, preimage_iUnion]
    exact iUnion_subset fun n ↦ (hTsucc n).trans (subset_iUnion T (n + 1))
  refine ⟨Quotient.mk E '' ⋃ n, T n,
    image_mono ((subset_preimage_image _ A).trans (hAT₀.trans (subset_iUnion T 0))), ?_, ?_⟩
  · rw [image_iUnion]
    exact disjoint_iUnion_right.2 fun n ↦ (f^[n] ⟨T₀, hT₀, hT₀B⟩).2.2.symm
  · rw [measurableSet_quotient, Quotient.mk''_eq_mk, hsat]
    exact MeasurableSet.iUnion fun n ↦ (f^[n] ⟨T₀, hT₀, hT₀B⟩).2.1

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- **Invariant Lusin separation**, in the quotient. Let `E` be an equivalence relation with
analytic graph on a Hausdorff space whose σ-algebra contains the Borel sets. If `A` and `B` are
analytic sets and no class of `E` meets both, then their images in `Quotient E` are separated by a
measurable set of Mathlib's quotient σ-algebra. -/
theorem measurablySeparable_image_quotientMk (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E p.1 p.2}) {A B : Set X} (hA : AnalyticSet A)
    (hB : AnalyticSet B) (hAB : Disjoint (Quotient.mk E '' A) (Quotient.mk E '' B)) :
    MeasurablySeparable (Quotient.mk E '' A) (Quotient.mk E '' B) := by
  -- Separate for the Borel σ-algebra, which is coarser than the ambient one.
  obtain ⟨C, hAC, hBC, hC⟩ := @measurablySeparable_image_quotientMk_of_borelSpace X _ _
    (borel X) (@BorelSpace.mk _ _ (borel X) rfl) E hE A B hA hB hAB
  exact ⟨C, hAC, hBC, MeasurableSpace.map_mono OpensMeasurableSpace.borel_le _ hC⟩

/-- **Invariant Lusin separation.** Let `E` be an equivalence relation with analytic graph on a
Hausdorff space whose σ-algebra contains the Borel sets. If `A` and `B` are analytic sets and no
class of `E` meets both, then some `E`-invariant measurable set contains `A` and is disjoint from
`B`. In particular, for the Borel σ-algebra, disjoint `E`-invariant analytic sets are separated by
an `E`-invariant Borel set. -/
theorem exists_invariant_measurableSet_separating (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E p.1 p.2}) {A B : Set X} (hA : AnalyticSet A)
    (hB : AnalyticSet B) (hAB : Disjoint (Quotient.mk E '' A) (Quotient.mk E '' B)) :
    ∃ C, MeasurableSet C ∧ Quotient.mk E ⁻¹' (Quotient.mk E '' C) = C ∧ A ⊆ C ∧
      Disjoint C B := by
  obtain ⟨C, hAC, hBC, hC⟩ := E.measurablySeparable_image_quotientMk hE hA hB hAB
  refine ⟨Quotient.mk E ⁻¹' C, ?_, by rw [image_preimage_eq C Quotient.mk_surjective],
    image_subset_iff.1 hAC, (disjoint_image_left.1 hBC).symm⟩
  rwa [measurableSet_quotient, Quotient.mk''_eq_mk] at hC

end Setoid
