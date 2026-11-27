/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.AEInvariants
public import TauCeti.Dynamics.Ergodic.Action.Factor
public import TauCeti.Dynamics.Ergodic.Action.WeakMixing.Basic
public import TauCeti.Dynamics.Ergodic.MeasurePreserving

/-!
# Invariant sets and weak mixing of factors

Let `π : X → Y` be a factor map of measure-preserving actions of a monoid `M`
(`TauCeti.IsFactorMapSMul M π μ ν`). This file shows that, when each `(m • ·)` is measurable on
`Y`, the invariant σ-algebra of the factor is the σ-algebra of the measurable sets whose preimages
are invariant, and that weak mixing of an action of `ℝ` passes to its factors.

For any factor map, the pullback of the invariant σ-algebra of the factor lies in the invariant
σ-algebra of the source: this is `TauCeti.comap_aeSMulInvariants_le` applied to the fields of
`TauCeti.IsFactorMapSMul`.

## Main results

* `TauCeti.IsFactorMapSMul.measurableSet_aeSMulInvariants_preimage_iff`: when the factor's action
  is measurable by each fixed element of `M`, a measurable subset of the factor is invariant
  exactly when its preimage is.
* `TauCeti.IsFactorMapVAdd.isWeaklyMixing`: weak mixing of an action of `ℝ` passes to factors.
* `MeasureTheory.Measure.IsWeaklyMixing.map`: the pushforward along an equivariant measurable map
  to a space with a measurable translation action is weakly mixing.
-/

public section

open MeasureTheory Filter Set

variable {M X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {π : X → Y}

namespace TauCeti

namespace IsFactorMapSMul

variable [SMul M X] [SMul M Y]

/-- **Invariant sets of a factor.** For a factor map `π` of actions whose target action is
measurable, a measurable set `s` of the factor is invariant exactly when its preimage is. -/
@[to_additive /-- **Invariant sets of a factor.** For a factor map `π` of additive actions whose
target action is measurable, a measurable set `s` of the factor is invariant exactly when its
preimage is. -/]
theorem measurableSet_aeSMulInvariants_preimage_iff [MeasurableConstSMul M Y]
    (h : IsFactorMapSMul M π μ ν) {s : Set Y} (hs : MeasurableSet s) :
    MeasurableSet[aeSMulInvariants M μ] (π ⁻¹' s) ↔ MeasurableSet[aeSMulInvariants M ν] s := by
  have hπ := h.measurePreserving
  simp only [measurableSet_aeSMulInvariants, hs.preimage hπ.measurable, hs, true_and]
  refine forall_congr' fun m ↦ ?_
  rw [← hπ.preimage_ae_eq_preimage_iff (measurable_const_smul m hs).nullMeasurableSet
    hs.nullMeasurableSet]
  exact ⟨((h.comp_smul_ae_eq m).preimage s).symm.trans,
    ((h.comp_smul_ae_eq m).preimage s).trans⟩

end IsFactorMapSMul

/-- **Weak mixing passes to factors.** If `π` is a factor map of actions of `ℝ` whose target
action is measurable and the source measure is weakly mixing, then so is the target measure. This
is the almost-everywhere form of `MeasureTheory.Measure.IsWeaklyMixing.map`. -/
theorem IsFactorMapVAdd.isWeaklyMixing [AddAction ℝ X] [AddAction ℝ Y]
    [MeasurableConstVAdd ℝ Y] (h : IsFactorMapVAdd ℝ π μ ν) (hμ : μ.IsWeaklyMixing) :
    ν.IsWeaklyMixing := by
  have hπ := h.measurePreserving
  rw [Measure.isWeaklyMixing_def] at hμ ⊢
  intro A B hA hB
  have key (t : ℝ) : ν.real ((fun y ↦ t +ᵥ y) ⁻¹' A ∩ B) =
      μ.real ((fun x ↦ t +ᵥ x) ⁻¹' (π ⁻¹' A) ∩ π ⁻¹' B) := by
    rw [← hπ.measureReal_preimage ((measurable_const_vadd t hA).inter hB).nullMeasurableSet,
      preimage_inter]
    exact measureReal_congr ((((h.comp_vadd_ae_eq t).preimage A).symm).inter (by rfl))
  have := hμ (π ⁻¹' A) (π ⁻¹' B) (hπ.measurable hA) (hπ.measurable hB)
  simpa only [key, hπ.measureReal_preimage hA.nullMeasurableSet,
    hπ.measureReal_preimage hB.nullMeasurableSet] using this

end TauCeti

/-- **Weak mixing passes to factors**: the pushforward of a weakly mixing measure along an
equivariant measurable map is weakly mixing, as `ErgodicSMul.map` is for ergodicity. -/
theorem MeasureTheory.Measure.IsWeaklyMixing.map [AddAction ℝ X] [AddAction ℝ Y]
    [MeasurableConstVAdd ℝ Y] {f : X → Y} (h : μ.IsWeaklyMixing) (hf : Measurable f)
    (hfg : ∀ (t : ℝ) x, f (t +ᵥ x) = t +ᵥ f x) : (μ.map f).IsWeaklyMixing :=
  (TauCeti.IsFactorMapVAdd.of_map_vadd (M := ℝ) ⟨hf, rfl⟩ hfg).isWeaklyMixing h
