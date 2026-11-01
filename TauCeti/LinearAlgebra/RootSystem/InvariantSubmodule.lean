/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Reflection-invariant submodules of a root pairing

A submodule of the root space invariant under the reflection at `v` that contains the root at
`u`, where the pairing of `u` with `v` is a unit, also contains the root at `v`. Reflecting `u` in
`v` stays inside the submodule, and subtracting leaves a multiple of the root at `v` whose
coefficient is exactly that pairing.

This is stated for a bare `RootPairing` over a commutative ring: no base, no crystallographic
structure and no finiteness. Over a field the unit hypothesis is just nonvanishing of the pairing,
which is how consumers propagating membership along a Dynkin edge use it.

## Main results

* `RootPairing.root_mem_of_isUnit_pairing`: membership of a root in a reflection-invariant
  submodule propagates along a pairing that is a unit.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- **Membership of a root in a reflection-invariant submodule propagates along a unit pairing.**
If `q` is invariant under the reflection at `v`, the pairing of `u` with `v` is a unit, and the
root at `u` lies in `q`, then so does the root at `v`. Over a field, the unit hypothesis is
`P.pairing u v ≠ 0`. -/
theorem root_mem_of_isUnit_pairing {q : Submodule R M} {u v : ι}
    (hinvv : q ∈ Module.End.invtSubmodule (P.reflection v))
    (hpair : IsUnit (P.pairing u v)) (hu : P.root u ∈ q) : P.root v ∈ q := by
  -- `root u - reflection v (root u) = pairing u v • root v` lies in `q`.
  have h : P.root u - P.reflection v (P.root u) ∈ q :=
    q.sub_mem hu ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp hinvv _ hu)
  rwa [reflection_apply_root, sub_sub_cancel, q.smul_mem_iff_of_isUnit hpair] at h

end RootPairing
