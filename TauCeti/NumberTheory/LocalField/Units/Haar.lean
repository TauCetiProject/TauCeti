/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
import TauCeti.NumberTheory.LocalField.Topology

/-!
# The normalized Haar measure `d^×x` on the units of a nonarchimedean local field

Let `K` be a nonarchimedean local field with ring of integers `𝒪[K]`. Its unit group `Kˣ` is a
locally compact group, and the units `𝒪[K]ˣ = {x | v(x) = 1}` of the ring of integers form the
compact open subgroup `TauCeti.unitFiltration K 0`. This file builds the Haar measure `d^×x` on
`Kˣ` giving `𝒪[K]ˣ` mass one, the local factor at a finite place of the idelic Haar measure.

The measurable structure on `Kˣ` is Mathlib's `Units.instMeasurableSpace`, pulled back along
`Units.val : Kˣ → K`; it is the Borel structure of `Kˣ` by `Units.borelSpace₀`.

## Main declarations

* `TauCeti.unitsIntegerPositiveCompacts`: the units `𝒪[K]ˣ = TauCeti.unitFiltration K 0`, as a
  compact subset of `Kˣ` with nonempty interior.
* `TauCeti.unitsHaar`: the Haar measure `d^×x` on `Kˣ` with `d^×x(𝒪[K]ˣ) = 1`
  (`TauCeti.unitsHaar_unitFiltration_zero`).
* `TauCeti.unitsHaar_eq_iff`: `TauCeti.unitsHaar K` is the only σ-finite left-invariant measure on
  `Kˣ` giving `𝒪[K]ˣ` mass one.
-/

public section

open MeasureTheory Measure TopologicalSpace

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The units `𝒪[K]ˣ = TauCeti.unitFiltration K 0` of the ring of integers, as a compact subset
of `Kˣ` with nonempty interior: the normalizing set of the Haar measure `TauCeti.unitsHaar`. -/
noncomputable def unitsIntegerPositiveCompacts : PositiveCompacts Kˣ where
  carrier := unitFiltration K 0
  isCompact' := isCompact_unitFiltration 0
  interior_nonempty' := ⟨1, by rw [(isOpen_unitFiltration 0).interior_eq]; exact one_mem _⟩

@[simp]
theorem coe_unitsIntegerPositiveCompacts :
    (unitsIntegerPositiveCompacts K : Set Kˣ) = unitFiltration K 0 :=
  (rfl)

variable [MeasurableSpace K] [BorelSpace K]

/-- **The normalized Haar measure `d^×x` on `Kˣ`**: the Haar measure of the locally compact group
`Kˣ` giving the units `𝒪[K]ˣ` of the ring of integers mass one. -/
noncomputable def unitsHaar : Measure Kˣ :=
  haarMeasure (unitsIntegerPositiveCompacts K)

instance isHaarMeasure_unitsHaar : (unitsHaar K).IsHaarMeasure :=
  isHaarMeasure_haarMeasure _

/-- The normalized Haar measure gives the units `𝒪[K]ˣ = TauCeti.unitFiltration K 0` of the ring
of integers mass one. -/
theorem unitsHaar_unitFiltration_zero : unitsHaar K (unitFiltration K 0) = 1 :=
  coe_unitsIntegerPositiveCompacts K ▸ haarMeasure_self

/-- The normalized Haar measure is characterized by its normalization: a σ-finite left-invariant
measure on `Kˣ` equals `TauCeti.unitsHaar K` exactly when it gives `𝒪[K]ˣ` mass one. -/
theorem unitsHaar_eq_iff (μ : Measure Kˣ) [SigmaFinite μ] [IsMulLeftInvariant μ] :
    unitsHaar K = μ ↔ μ (unitFiltration K 0) = 1 :=
  have := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  haarMeasure_eq_iff (unitsIntegerPositiveCompacts K) μ

end TauCeti
