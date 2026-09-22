/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Quotient
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Functoriality

/-!
# PBW filtrations for Lie quotients

The quotient map of a Lie algebra by a Lie ideal induces a surjective map between corresponding
PBW filtration steps. This file records the quotient specializations of the general surjectivity
results in `PBW.Functoriality`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.map_mkQ_pbwFiltration`: specialization to a quotient by a
  Lie ideal.
* `TauCeti.UniversalEnvelopingAlgebra.map_mkQ_pbwFiltrationPrevious`: the same for the step
  immediately preceding a filtration degree.
* `TauCeti.UniversalEnvelopingAlgebra.mapFiltration_mkQ_surjective`: the induced linear map between
  quotient filtration steps is surjective.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) [CommRing R]
variable {L : Type v}
variable [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

section Quotient

variable (I : LieIdeal R L)

/-- The enveloping-algebra map induced by a Lie quotient maps each PBW filtration step onto the
corresponding filtration step of the quotient enveloping algebra. -/
@[simp]
theorem map_mkQ_pbwFiltration (k : ℕ) :
    (pbwFiltration R L k).map (map R I.mkQ).toLinearMap =
      pbwFiltration R (L ⧸ I) k :=
  map_pbwFiltration_eq_of_surjective R I.mkQ I.mkQ_surjective k

/-- The enveloping-algebra map induced by a Lie quotient maps the step immediately preceding each
PBW filtration degree onto the corresponding preceding step of the quotient enveloping algebra. -/
@[simp]
theorem map_mkQ_pbwFiltrationPrevious (k : ℕ) :
    (pbwFiltrationPrevious R L k).map (map R I.mkQ).toLinearMap =
      pbwFiltrationPrevious R (L ⧸ I) k :=
  map_pbwFiltrationPrevious_eq_of_surjective R I.mkQ I.mkQ_surjective k

/-- The linear map on each PBW filtration step induced by a Lie quotient is surjective. -/
theorem mapFiltration_mkQ_surjective (k : ℕ) :
    Function.Surjective (mapFiltration R I.mkQ k) :=
  mapFiltration_surjective_of_surjective R I.mkQ I.mkQ_surjective k

end Quotient

end TauCeti.UniversalEnvelopingAlgebra
