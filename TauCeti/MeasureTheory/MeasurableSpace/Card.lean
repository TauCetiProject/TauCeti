/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Cardinality of countably separated measurable spaces

A countably separated measurable space, and in particular a standard Borel space, has at most
continuum many points, since it injects measurably into Cantor space
(`MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated`); hence so does every
quotient of one.

## Main results

* `TauCeti.mk_le_continuum_of_countablySeparated`: a countably separated measurable space, in
  particular a standard Borel space, has at most `𝔠` points.
* `Setoid.mk_quotient_le_continuum`: every quotient of such a space has at most `𝔠` elements.
-/

public section

open Function Cardinal

universe u

variable {X : Type u}

namespace TauCeti

/-- **A countably separated measurable space has at most continuum many points**, since it
injects into Cantor space. This applies in particular to every standard Borel space. -/
theorem mk_le_continuum_of_countablySeparated (X : Type u) [MeasurableSpace X]
    [MeasurableSpace.CountablySeparated X] : #X ≤ 𝔠 := by
  obtain ⟨f, -, hf⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated X
  simpa using lift_mk_le_lift_mk_of_injective hf

end TauCeti

/-- **A quotient of a countably separated measurable space has at most continuum many
elements.** This applies in particular to the quotient of a standard Borel space by an
arbitrary equivalence relation. -/
theorem Setoid.mk_quotient_le_continuum [MeasurableSpace X]
    [MeasurableSpace.CountablySeparated X] (E : Setoid X) : #(Quotient E) ≤ 𝔠 :=
  (mk_le_of_surjective Quotient.mk_surjective).trans
    (TauCeti.mk_le_continuum_of_countablySeparated X)
