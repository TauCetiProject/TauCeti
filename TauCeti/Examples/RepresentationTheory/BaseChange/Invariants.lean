/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.BaseChange.Invariants

/-!
# Examples: invariants under a field extension

For any field extension `K → L` and any group, including the infinite group `Multiplicative ℤ`,
extending scalars commutes with taking invariants. Over `ℤ → ℤ/2`, which is
not free, the comparison map can fail to be surjective
(`TauCeti.signRepresentation_invariantsBaseChangeMap_not_surjective` in
`TauCeti.Examples.RepresentationTheory.Smooth.BaseChange`).
-/

-- `L ⊗_K V^ℤ ≃ (L ⊗_K V)^ℤ` for an action of the infinite cyclic group.
example {K L V : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
    (ρ : Representation K (Multiplicative ℤ) V) :
    Function.Bijective (ρ.invariantsBaseChangeMap (A := L)) :=
  ρ.invariantsBaseChangeMap_bijective_of_free
