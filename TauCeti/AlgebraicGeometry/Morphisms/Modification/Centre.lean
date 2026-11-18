/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

/-!
# The centre of a modification

For a morphism of schemes `f : X ⟶ Y`, the iso locus `f.isoLocus` is the largest open of `Y` over
which `f` is an isomorphism, and its closed complement `f.centre` is the set of points over which
`f` fails to be an isomorphism (`TauCeti/AlgebraicGeometry/Morphisms/IsoLocus.lean`). For a
modification the iso locus contains the dense open of the definition, so it is dense and the
centre is nowhere dense.

## Main results

* `TauCeti.AlgebraicGeometry.IsModification.dense_isoLocus` and
  `TauCeti.AlgebraicGeometry.IsModification.isNowhereDense_centre`: for a modification, the iso
  locus is dense and the centre is nowhere dense.

## References

* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

namespace IsModification

/-- The iso locus of a modification is dense. -/
theorem dense_isoLocus (f : X ⟶ Y) [IsModification f] : Dense (f.isoLocus : Set Y) := by
  obtain ⟨U, hU, -, hf⟩ := exists_isIso_morphismRestrict (f := f)
  exact hU.mono (f.le_isoLocus_iff.mpr hf)

/-- The centre of a modification is nowhere dense: it is closed, and `f` is an isomorphism over
its dense complement. -/
theorem isNowhereDense_centre (f : X ⟶ Y) [IsModification f] : IsNowhereDense f.centre := by
  rw [f.isClosed_centre.isNowhereDense_iff, interior_eq_empty_iff_dense_compl,
    Scheme.Hom.compl_centre]
  exact dense_isoLocus f

end IsModification

end TauCeti.AlgebraicGeometry
