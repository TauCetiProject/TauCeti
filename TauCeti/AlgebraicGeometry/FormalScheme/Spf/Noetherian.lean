/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Carrier
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Noetherian underlying spaces of formal spectra

Let `A` be a noetherian topological ring. Then the underlying space `Spf.carrier A` of the formal
spectrum is a noetherian topological space (`TauCeti.FormalScheme.Spf.noetherianSpace_carrier`), as
a subspace of `PrimeSpectrum A`. This supplies the affine topological input for
`TauCeti.FormalScheme.noetherianSpace_ofSpf` and
`TauCeti.FormalScheme.IsNoetherian.noetherianSpace`; noetherianity of the local stalks of `Spf A`
is `TauCeti.FormalScheme.Spf.isNoetherianRing_stalk` in
`TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk`.

## Main results

* `TauCeti.FormalScheme.Spf.noetherianSpace_carrier`: `Spf.carrier A` is a `NoetherianSpace` when
  `A` is a noetherian topological ring.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.4.2.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open TopologicalSpace

namespace TauCeti.FormalScheme.Spf

/-- The underlying space of `Spf A` for a noetherian topological ring `A` is a noetherian
topological space. -/
instance noetherianSpace_carrier {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsNoetherianRing A] : NoetherianSpace (carrier A) :=
  NoetherianSpace.set (carrier A)

end TauCeti.FormalScheme.Spf
