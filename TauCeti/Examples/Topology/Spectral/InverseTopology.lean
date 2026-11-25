/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Order.Sierpinski
import TauCeti.Topology.Spectral.InverseTopology

/-!
# Worked examples: the inverse topology of the Sierpiński space

The Sierpiński space `Prop`, whose only nontrivial open subset is `{True}`, is the prime spectrum
of a discrete valuation ring, with `True` the generic and `False` the closed point. Passing to the
inverse topology switches the two points: `{False}` becomes open, `{True}` is no longer open, and
`True ⤳ False` becomes `False ⤳ True`. The result is again a spectral space.
-/

open Set Topology

namespace TauCeti

/-- In the inverse topology of the Sierpiński space the closed point `False` becomes open. -/
example : IsOpen[inverseTopology Prop] {False} :=
  isOpen_inverseTopology_of_isClosed isClosed_singleton_false (Set.toFinite _).isCompact

/-- In the inverse topology of the Sierpiński space the open point `True` is no longer open: open
subsets of the inverse topology are stable under specialization, and `True ⤳ False`. -/
example : ¬ IsOpen[inverseTopology Prop] {True} := fun h ↦
  absurd (stableUnderSpecialization_of_isOpen_inverseTopology h
    (specializes_iff_nhds.2 (nhds_false ▸ le_top)) rfl) (by simp)

/-- The inverse topology of the Sierpiński space reverses its specialization `True ⤳ False`. -/
example : @Specializes Prop (inverseTopology Prop) False True :=
  have : SpectralSpace Prop := spectralSpace_prop
  specializes_inverseTopology_iff.2 (specializes_iff_nhds.2 (nhds_false ▸ le_top))

/-- The inverse topology of the Sierpiński space is spectral. -/
example : @SpectralSpace Prop (inverseTopology Prop) :=
  have : SpectralSpace Prop := spectralSpace_prop
  spectralSpace_inverseTopology Prop

end TauCeti
