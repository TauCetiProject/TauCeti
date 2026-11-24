/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.NumberTheory.LocalField.HaarCharacter
import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# The normalized Haar measure `d^×x` on the units of a nonarchimedean local field

Let `K` be a nonarchimedean local field with ring of integers `𝒪[K]`. Its unit group `Kˣ` is a
locally compact group, and the units `𝒪[K]ˣ = {x | v(x) = 1}` of the ring of integers form a
compact open subgroup. This file builds the Haar measure `d^×x` on `Kˣ` giving `𝒪[K]ˣ` mass one,
the local factor at a finite place of the idelic Haar measure.

The measurable structure on `Kˣ` is Mathlib's `Units.instMeasurableSpace`, pulled back along
`Units.val : Kˣ → K`. Since `Units.val` is a topological embedding for a topological field, this
is the Borel structure of `Kˣ` (`TauCeti.instBorelSpaceUnits`, which holds for every topological
group with zero with continuous inversion).

## Main declarations

* `TauCeti.instBorelSpaceUnits`: the units of a topological group with zero with continuous
  inversion and Borel structure carry the Borel structure.
* `TauCeti.unitsIntegerPositiveCompacts`: the units `{x | v(x) = 1}` of `𝒪[K]`, as a compact
  subset of `Kˣ` with nonempty interior; it is open (`TauCeti.isOpen_unitsIntegerPositiveCompacts`).
* `TauCeti.unitsHaar`: the Haar measure `d^×x` on `Kˣ` with `d^×x(𝒪[K]ˣ) = 1`
  (`TauCeti.unitsHaar_unitsIntegerPositiveCompacts`).
-/

public section

open MeasureTheory Measure ValuativeRel TopologicalSpace Topology

namespace TauCeti

section Borel

variable {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
  [ContinuousMul G₀] [MeasurableSpace G₀] [BorelSpace G₀]

/-- The measurable structure on the units of a topological group with zero with continuous
inversion, pulled back along `Units.val`, is the Borel structure: `Units.val` is a topological
embedding (`Units.isEmbedding_val₀`). -/
instance instBorelSpaceUnits : BorelSpace G₀ˣ := by
  borelize G₀
  refine ⟨?_⟩
  rw [Units.isEmbedding_val₀.eq_induced, borel_comap]
  rfl

end Borel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem setOf_valuation_eq_one_eq_restrict :
    {x : K | valuation K x = 1} = {x | (valuation K).restrict x = 1} := by
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← map_one (valuation K).restrict,
    Valuation.restrict_inj, map_one]

/-- The units `{x | v(x) = 1}` of the ring of integers form a closed subset of `K`. -/
theorem isClosed_setOf_valuation_eq_one : IsClosed {x : K | valuation K x = 1} := by
  rw [setOf_valuation_eq_one_eq_restrict]
  exact (valuation K).isClosed_sphere 1

/-- The units `{x | v(x) = 1}` of the ring of integers form an open subset of `K`. -/
theorem isOpen_setOf_valuation_eq_one : IsOpen {x : K | valuation K x = 1} := by
  rw [setOf_valuation_eq_one_eq_restrict]
  exact (valuation K).isOpen_sphere one_ne_zero

/-- The units `{x | v(x) = 1}` of the ring of integers, as a compact subset of `Kˣ` with nonempty
interior: the normalizing set of the Haar measure `TauCeti.unitsHaar`. -/
noncomputable def unitsIntegerPositiveCompacts : PositiveCompacts Kˣ where
  carrier := {u | valuation K (u : K) = 1}
  isCompact' := by
    refine ((Units.isEmbedding_val₀ (G₀ := K)).isInducing.isCompact_preimage_iff
      (K := {x : K | valuation K x = 1}) ?_).2 ?_
    · intro x hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      exact ⟨Units.mk0 x hx0, rfl⟩
    · refine (integerPositiveCompacts K).isCompact.of_isClosed_subset
        (isClosed_setOf_valuation_eq_one K) fun x hx ↦ ?_
      simp only [Set.mem_ofPred_eq] at hx
      simp [coe_integerPositiveCompacts, Valuation.mem_integer_iff, hx]
  interior_nonempty' :=
    ⟨1, ((isOpen_setOf_valuation_eq_one K).preimage Units.continuous_val).interior_eq ▸ by
      simp⟩

@[simp]
theorem mem_unitsIntegerPositiveCompacts {u : Kˣ} :
    u ∈ unitsIntegerPositiveCompacts K ↔ valuation K (u : K) = 1 :=
  Iff.rfl

/-- The units of the ring of integers form an open subset of `Kˣ`. -/
theorem isOpen_unitsIntegerPositiveCompacts :
    IsOpen (unitsIntegerPositiveCompacts K : Set Kˣ) :=
  (isOpen_setOf_valuation_eq_one K).preimage Units.continuous_val

variable [MeasurableSpace K] [BorelSpace K]

/-- **The normalized Haar measure `d^×x` on `Kˣ`**: the Haar measure of the locally compact group
`Kˣ` giving the units `𝒪[K]ˣ` of the ring of integers mass one. -/
noncomputable def unitsHaar : Measure Kˣ :=
  haarMeasure (unitsIntegerPositiveCompacts K)

instance isHaarMeasure_unitsHaar : (unitsHaar K).IsHaarMeasure :=
  isHaarMeasure_haarMeasure _

/-- The normalized Haar measure gives the units of the ring of integers mass one. -/
theorem unitsHaar_unitsIntegerPositiveCompacts :
    unitsHaar K (unitsIntegerPositiveCompacts K) = 1 :=
  haarMeasure_self

/-- The normalized Haar measure gives `{u | v(u) = 1}` mass one. -/
theorem unitsHaar_setOf_valuation_eq_one :
    unitsHaar K {u | valuation K (u : K) = 1} = 1 :=
  haarMeasure_self

end TauCeti
