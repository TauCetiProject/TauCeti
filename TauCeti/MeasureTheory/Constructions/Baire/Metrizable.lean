/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Metrizable.Basic
public import TauCeti.MeasureTheory.Constructions.Baire.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.PerfectlyNormal

/-!
# Pulling back Borel sets along maps into pseudometrizable spaces

On a pseudometrizable space `Y`, every closed set is the zero set of a continuous real-valued
function (`PerfectlyNormalSpace`), so the Baire σ-algebra `TauCeti.baire Y` coincides with the
Borel σ-algebra `borel Y` (`TauCeti.baire_eq_borel`). Pulling back along any continuous map
`q : X → Y` from an arbitrary topological space `X` into `Y` therefore maps every Borel set of `Y`
into `TauCeti.baire X`.

## Main results

* `Continuous.comap_borel_le_baire`: for a continuous map `q : X → Y` into a pseudometrizable
  space `Y`, `MeasurableSpace.comap q (borel Y) ≤ TauCeti.baire X`.

## References

* D. H. Fremlin, *Measure Theory*, Vol. 4, Torres Fremlin (2003), §4A3K.
-/

public section

open TopologicalSpace

/-- Pulling back the Borel σ-algebra along a continuous map into a pseudometrizable space lands in
the Baire σ-algebra of the domain. -/
theorem Continuous.comap_borel_le_baire {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PseudoMetrizableSpace Y] {q : X → Y} (hq : Continuous q) :
    MeasurableSpace.comap q (borel Y) ≤ TauCeti.baire X := by
  rw [← TauCeti.baire_eq_borel (X := Y)]
  exact measurable_iff_comap_le.mp hq.measurable_baire

end
