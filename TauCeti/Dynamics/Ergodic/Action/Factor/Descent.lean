/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.AEInvariants
public import TauCeti.Dynamics.Ergodic.Action.Factor
public import TauCeti.Dynamics.Ergodic.Action.WeakMixing.Basic

/-!
# Invariant sets and weak mixing of factors

Let `π : X → Y` be a factor map of measure-preserving actions of a monoid `M`
(`TauCeti.IsFactorMapSMul M π μ ν`). This file shows that the invariant σ-algebra of the factor
is the σ-algebra of the sets whose preimages are invariant, and that weak mixing of an action of
`ℝ` passes to its factors.

## Main results

* `MeasureTheory.MeasurePreserving.preimage_ae_eq_preimage_iff`: a measure-preserving map
  identifies almost-everywhere equality of measurable sets with that of their preimages.
* `TauCeti.IsFactorMapSMul.measurableSet_aeSMulInvariants_preimage_iff`: a measurable subset of
  the factor is invariant exactly when its preimage is; in particular
  `TauCeti.IsFactorMapSMul.comap_aeSMulInvariants_le`, the pullback of the invariant σ-algebra of
  the factor lies in the invariant σ-algebra of the source.
* `TauCeti.IsFactorMapVAdd.isWeaklyMixing`: weak mixing of an action of `ℝ` passes to factors.
-/

public section

open MeasureTheory Filter Set

variable {M X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {π : X → Y}

/-- A measure-preserving map identifies almost-everywhere equality of measurable sets with that of
their preimages. -/
theorem MeasureTheory.MeasurePreserving.preimage_ae_eq_preimage_iff (hπ : MeasurePreserving π μ ν)
    {s t : Set Y} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    π ⁻¹' s =ᵐ[μ] π ⁻¹' t ↔ s =ᵐ[ν] t := by
  rw [ae_eq_set, ae_eq_set, ← preimage_sdiff, ← preimage_sdiff,
    hπ.measure_preimage (hs.diff ht).nullMeasurableSet,
    hπ.measure_preimage (ht.diff hs).nullMeasurableSet]

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
  rw [← hπ.preimage_ae_eq_preimage_iff (measurable_const_smul m hs) hs]
  exact ⟨((h.comp_smul_ae_eq m).preimage s).symm.trans,
    ((h.comp_smul_ae_eq m).preimage s).trans⟩

/-- **Factor compatibility of invariant σ-algebras.** The pullback along a factor map of the
invariant σ-algebra of the factor lies in the invariant σ-algebra of the source. -/
@[to_additive /-- **Factor compatibility of invariant σ-algebras.** The pullback along a factor
map of additive actions of the invariant σ-algebra of the factor lies in the invariant σ-algebra
of the source. -/]
theorem comap_aeSMulInvariants_le (h : IsFactorMapSMul M π μ ν) :
    (aeSMulInvariants M ν).comap π ≤ aeSMulInvariants M μ :=
  TauCeti.comap_aeSMulInvariants_le h.measurePreserving.measurable
    h.measurePreserving.quasiMeasurePreserving h.comp_smul_ae_eq

end IsFactorMapSMul

/-- **Weak mixing passes to factors.** If `π` is a factor map of actions of `ℝ` whose target
action is measurable and the source measure is weakly mixing, then so is the target measure. This
extends `MeasureTheory.Measure.IsWeaklyMixing.map` from equivariant maps to almost-everywhere
intertwiners. -/
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
