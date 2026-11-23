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

Separatedness descends by applying closed-immersion descent to the diagonal, using
`MorphismProperty.DescendsAlong` for diagonal properties.
Properness then follows by combining descent of separatedness, universal closedness and local
finite type. Universal closedness already implies quasi-compactness.

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
  exact @instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange _ _ _ _ _
    inferInstance inferInstance
    (@IsStableUnderBaseChange.inf _ _ _ _ IsStableUnderBaseChange.inf inferInstance)

/-- Properness descends along surjective, flat, quasi-compact morphisms of schemes. -/
instance IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong @IsProper.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [isProper_eq]
  exact @DescendsAlong.inf _ _ _ _ _
    (@DescendsAlong.inf _ _ _ _ _
      IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact inferInstance) inferInstance

end AlgebraicGeometry
