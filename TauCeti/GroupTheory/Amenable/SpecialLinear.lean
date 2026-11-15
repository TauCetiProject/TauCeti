/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.GroupTheory.Amenable.Basic

import TauCeti.GroupTheory.Amenable.FreeGroup
import TauCeti.GroupTheory.FreeGroup.Linear

/-!
# Nonamenability of `SL(2, R)` over strictly ordered commutative rings

For any strictly ordered commutative ring `R`, `SL(2, R)` contains a free subgroup of rank two by
Sanov's theorem (`TauCeti.injective_freeGroup_lift_transvection_of_two_le_abs`) and is therefore
not amenable as a discrete group. Consequently, no amenable discrete group admits an injective
homomorphism from `SL(2, R)`.

## Main results

* `TauCeti.not_amenable_specialLinearGroup_fin_two`: `SL(2, R)` is not amenable as a discrete
  group for any strictly ordered commutative ring `R` (in particular `SL(2, ℤ)` and `SL(2, ℝ)`).
* `TauCeti.not_amenable_of_injective_specialLinearGroup_fin_two`: a discrete group admitting an
  injective homomorphism from `SL(2, R)` is not amenable.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Example G.2.4(iii).
-/

public section

open scoped MatrixGroups

namespace TauCeti

variable {R G : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Over a strictly ordered commutative ring `R`, `SL(2, R)` is not amenable as a discrete
group. -/
theorem not_amenable_specialLinearGroup_fin_two
    [TopologicalSpace SL(2, R)] [DiscreteTopology SL(2, R)] :
    ¬ Amenable SL(2, R) := by
  -- Sanov's transvections with parameter `2` generate an embedded copy of `FreeGroup (Fin 2)`.
  have h2 : (2 : R) ≤ |(2 : R)| := le_abs_self 2
  exact not_amenable_of_injective_freeGroup _
    (injective_freeGroup_lift_transvection_of_two_le_abs h2 h2)

/-- A discrete group admitting an injective homomorphism from `SL(2, R)`, over a strictly ordered
commutative ring `R`, is not amenable. -/
theorem not_amenable_of_injective_specialLinearGroup_fin_two
    [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (φ : SL(2, R) →* G) (hφ : Function.Injective φ) :
    ¬ Amenable G := fun _ ↦ by
  let : TopologicalSpace SL(2, R) := ⊥
  have : DiscreteTopology SL(2, R) := ⟨rfl⟩
  exact not_amenable_specialLinearGroup_fin_two (Amenable.of_injective φ hφ)

end TauCeti
