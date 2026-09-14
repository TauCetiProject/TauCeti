/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Separation of the adele ring of a number field

Mathlib's `NumberField.InfiniteAdeleRing K` is the finite product of the completions of `K` at its
infinite places, and `NumberField.AdeleRing R K` is the product of the infinite adele ring with the
finite adele ring of `R`.  Both are defined as type synonyms, so the Hausdorff property of the
underlying products is not found by instance search.  This file records it, so that closedness of
discrete subgroups and separation of quotients apply to the adele ring.
-/

public section

namespace NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The infinite adele ring is Hausdorff, as a finite product of the completions at the infinite
places. -/
instance InfiniteAdeleRing.instT2Space : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs <| T2Space ((v : InfinitePlace K) → v.Completion)

/-- The adele ring is Hausdorff, as the product of the infinite and the finite adele rings. -/
instance AdeleRing.instT2Space : T2Space (AdeleRing R K) :=
  inferInstanceAs <| T2Space (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing R K)

end NumberField
