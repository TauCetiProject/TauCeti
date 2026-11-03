/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic

/-!
# Isomorphism invariance of Euler characteristics

Mathlib's `HomologicalComplex.eulerChar` and `HomologicalComplex.homologyEulerChar` are defined
as `finsum`s of finranks.  This file records that both are invariant under isomorphisms of
complexes of modules.

## Main results

* `HomologicalComplex.eulerChar_eq_of_iso` and `HomologicalComplex.homologyEulerChar_eq_of_iso`:
  both Euler characteristics are invariant under isomorphisms of complexes.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι} [c.EulerCharSigns]
  {K L : HomologicalComplex (ModuleCat.{v} R) c}

/-- Isomorphic complexes of modules have the same Euler characteristic. -/
theorem eulerChar_eq_of_iso (e : K ≅ L) : K.eulerChar = L.eulerChar :=
  finsum_congr fun i => by rw [(Hom.isoApp e i).toLinearEquiv.finrank_eq]

/-- Isomorphic complexes of modules have the same homology Euler characteristic. -/
theorem homologyEulerChar_eq_of_iso [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (e : K ≅ L) :
    K.homologyEulerChar = L.homologyEulerChar :=
  finsum_congr fun i => by rw [(homologyMapIso e i).toLinearEquiv.finrank_eq]

end HomologicalComplex
