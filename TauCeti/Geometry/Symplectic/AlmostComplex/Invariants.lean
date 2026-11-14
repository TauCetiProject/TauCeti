/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Fixed vectors of representations by complex-linear maps

If a group acts on a real vector space by maps complex linear for an almost complex structure
`J`, the subspace of fixed vectors is stable under `J`.

## Main results

* `TauCeti.AlmostComplexStructure.invariants_mem_invtSubmodule`: the invariants of a
  representation by maps complex linear for an almost complex structure `J` are `J`-stable.
-/

public section

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The vectors fixed by a representation of a group by maps complex linear for an almost complex
structure `J` form a `J`-stable subspace. -/
theorem invariants_mem_invtSubmodule (J : AlmostComplexStructure V) {G : Type*} [Group G]
    {ρ : Representation ℝ G V} (hρ : ∀ g, IsComplexLinearMap J J (ρ g)) :
    ρ.invariants ∈ Module.End.invtSubmodule J.toLinearMap :=
  (Module.End.mem_invtSubmodule _).2 fun v hv ↦
    (Representation.mem_invariants ρ _).2 fun g ↦ by
      rw [(isComplexLinearMap_iff_apply J J (ρ g)).1 (hρ g) v,
        (Representation.mem_invariants ρ v).1 hv g]

end TauCeti.AlmostComplexStructure
