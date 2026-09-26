/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocallyCompact

/-!
# Local compactness of adeles

The adele ring of a number field is locally compact: its archimedean part is a finite product of
local fields, while its finite part is a restricted product with compact open integer rings.

## Main results

* `NumberField.AdeleRing.instLocallyCompactSpace`: the full adele ring is locally compact.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
-/

public section
noncomputable section

open IsDedekindDomain

namespace NumberField

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [NumberField K] [Algebra R K] [IsFractionRing R K]
variable [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]

/-- The adele ring of a number field is locally compact. -/
instance AdeleRing.instLocallyCompactSpace : LocallyCompactSpace (AdeleRing R K) :=
  inferInstanceAs <| LocallyCompactSpace
    (InfiniteAdeleRing K × FiniteAdeleRing R K)

end NumberField
