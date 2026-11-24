/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.MorphismProperty.Descent

import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import TauCeti.AlgebraicGeometry.Descent.MorphismProperty

/-!
# fpqc descent of separated and proper morphisms

Separatedness and properness descend along surjective, flat, quasi-compact morphisms of schemes.
The instances here allow the generic `MorphismProperty` descent API to recover these properties
from a base change over any base scheme.

Separatedness uses Tau Ceti's
`IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasiCompact` from
`TauCeti.AlgebraicGeometry.Descent.MorphismProperty`, together with Mathlib's diagonal descent
instance from `Mathlib.CategoryTheory.MorphismProperty.Descent`.
Properness combines descent of separatedness, universal closedness and local finite type using
Mathlib's `MorphismProperty.DescendsAlong.inf`. The latter two descent instances come from
`Mathlib.AlgebraicGeometry.Morphisms.FlatDescent` and
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`, respectively. Universal closedness already
implies quasi-compactness.

## References

* The Stacks Project, Lemma 35.23.6 (tag [02KU](https://stacks.math.columbia.edu/tag/02KU)),
  on separatedness.
* The Stacks Project, Lemma 35.23.16 (tag [02L1](https://stacks.math.columbia.edu/tag/02L1)),
  on properness.
-/

public section

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

universe u

/-- Separatedness descends along surjective, flat, quasi-compact morphisms of schemes. -/
instance IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong @IsSeparated.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
  -- At default transparency, stability of the nested intersection needs an explicit witness.
  have : IsStableUnderBaseChange (@Surjective.{u} ⊓ @Flat) :=
    IsStableUnderBaseChange.inf
  have : IsStableUnderBaseChange (@Surjective.{u} ⊓ @Flat ⊓ @QuasiCompact) :=
    IsStableUnderBaseChange.inf
  -- Match Mathlib's diagonal descent instance before specializing the property.
  have diagonalDescends (P : MorphismProperty Scheme.{u})
      [DescendsAlong P (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] [P.RespectsIso] :
      DescendsAlong (diagonal P) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    infer_instance
  exact diagonalDescends @IsClosedImmersion

/-- Properness descends along surjective, flat, quasi-compact morphisms of schemes. -/
instance IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong @IsProper.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [isProper_eq]
  have : DescendsAlong (@IsSeparated.{u} ⊓ @UniversallyClosed)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    DescendsAlong.inf (P := @IsSeparated) (W := @UniversallyClosed)
  exact DescendsAlong.inf (P := @IsSeparated ⊓ @UniversallyClosed) (W := @LocallyOfFiniteType)

end AlgebraicGeometry
