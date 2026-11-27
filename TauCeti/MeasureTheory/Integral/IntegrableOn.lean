/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Integrability of functions factoring through a locally constant map to a finite type

Let `G` be a topological space with a measurable structure in which open sets are measurable. A
function that agrees on an open set `U` of finite measure with `Φ ∘ π`, for a locally constant map
`π : U → R` to a finite type, is a simple function on `U` for the pulled-back measure, hence
integrable on `U` (`MeasureTheory.integrableOn_of_eq_comp`).
-/

public section

namespace MeasureTheory

variable {G R E : Type*} [MeasurableSpace G] {μ : Measure G} [NormedAddCommGroup E]
  [TopologicalSpace G] [OpensMeasurableSpace G]

/-- In a space whose open sets are measurable, a function that agrees on an open set `U` of finite
measure with a function of a locally constant map `π : U → R` to a finite type is integrable on
`U`. -/
theorem integrableOn_of_eq_comp [Finite R] {U : Set G} (hU : IsOpen U) (hμU : μ U ≠ ⊤)
    {π : U → R} (hπ : IsLocallyConstant π) {f : G → E} {Φ : R → E}
    (hf : ∀ x : U, f x = Φ (π x)) : IntegrableOn f U μ := by
  have : IsFiniteMeasure (μ.comap Subtype.val) :=
    ⟨by
      rw [comap_subtypeVal_apply hU.measurableSet, Set.image_univ, Subtype.range_coe]
      exact hμU.lt_top⟩
  -- `π` is a simple function on `U`: its fibres are open and its range is finite
  let p : SimpleFunc U R := ⟨π, fun r ↦ (hπ.isOpen_fiber r).measurableSet, Set.toFinite _⟩
  rw [integrableOn_iff_comap_subtypeVal hU.measurableSet, show f ∘ Subtype.val = p.map Φ from
    funext hf]
  exact (p.map Φ).integrable_of_isFiniteMeasure

end MeasureTheory
