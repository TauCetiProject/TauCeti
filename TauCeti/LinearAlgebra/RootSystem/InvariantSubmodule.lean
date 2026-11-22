/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Reflection-invariant submodules of a root pairing

A submodule of the root space invariant under the reflection at `v` that contains the root at
`u`, where the pairing of `u` with `v` is a unit, also contains the root at `v`. Reflecting `u` in
`v` stays inside the submodule, and subtracting leaves a multiple of the root at `v` whose
coefficient is exactly that pairing.

This is stated for a bare `RootPairing` over a commutative ring: no base, no crystallographic
structure and no finiteness. Over a field the unit hypothesis is just nonvanishing of the pairing,
which is how consumers propagating membership along a Dynkin edge use it.

Over a field in which `2 ≠ 0`, a submodule invariant under the reflections in a family of roots
whose coroots span, and containing none of these roots, is trivial: it lies in the kernel of every
coroot of the family, and these coroots separate points.

## Main results

* `RootPairing.root_mem_of_isUnit_pairing`: membership of a root in a reflection-invariant
  submodule propagates along a pairing that is a unit.
* `RootPairing.eq_bot_of_forall_root_not_mem_of_span_coroot_eq_top`: a submodule invariant under
  the reflections in a family of roots whose coroots span, and containing none of these roots, is
  trivial.
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

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N}

/-- **A submodule invariant under the reflections in a family of roots whose coroots span, and
containing none of these roots, is trivial.** Invariance is asked only under the reflections in the
roots of the family, not under every reflection of `P`. -/
theorem eq_bot_of_forall_root_not_mem_of_span_coroot_eq_top
    [NeZero (2 : K)] {J : Type*} {e : J → ι} {q : Submodule K M}
    (hinv : ∀ j, q ∈ Module.End.invtSubmodule (P.reflection (e j)))
    (h : ∀ j, P.root (e j) ∉ q)
    (hcoroot : Submodule.span K (Set.range (P.coroot ∘ e)) = ⊤) : q = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  have hker (j : J) : x ∈ LinearMap.ker (P.coroot' (e j)) :=
    (Submodule.mem_invtSubmodule_reflection_iff (P.flip.root_coroot_two (e j))
      (Submodule.disjoint_span_singleton_of_notMem (h j))).mp (hinv j) hx
  apply P.toPerfPair.injective
  rw [map_zero]
  refine LinearMap.ext_on_range hcoroot fun j ↦ ?_
  simpa using LinearMap.mem_ker.mp (hker j)

end Field

end RootPairing
