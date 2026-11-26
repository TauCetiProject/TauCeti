/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.RootSystem.BaseChange

/-!
# The projection onto the span of the roots

In a balanced root pairing `P` over a commutative ring, the span of the roots is complementary to
the common kernel of the coroot functionals, the central part of the weight space on which every
coroot vanishes. This file records that splitting and the projection `RootPairing.rootSpanProj`
onto the span of the roots along the central part, which preserves every coroot value.

## Main definitions

* `RootPairing.rootSpanProj`: the projection onto the span of the roots along the common kernel of
  the coroot functionals.

## Main results

* `RootPairing.isCompl_rootSpan_iInf_ker_coroot'`: the span of the roots is complementary to the
  common kernel of the coroot functionals.
* `RootPairing.coroot'_rootSpanProj`: the projection onto the span of the roots preserves every
  coroot value.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N] {P : RootPairing ι R M N} [P.IsBalanced]

variable (P) in
/-- In a balanced root pairing, the span of the roots is complementary to the common kernel of the
coroot functionals, the central part of the weight space. -/
theorem isCompl_rootSpan_iInf_ker_coroot' :
    IsCompl (P.rootSpan R) (⨅ i, LinearMap.ker (P.coroot' i)) := by
  rw [← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot']
  exact IsBalanced.isPerfectCompl.isCompl_left

variable (P) in
/-- The **projection onto the span of the roots** along the common kernel of the coroot
functionals. -/
noncomputable def rootSpanProj : M →ₗ[R] P.rootSpan R :=
  (P.rootSpan R).projectionOnto _ P.isCompl_rootSpan_iInf_ker_coroot'

/-- The projection onto the span of the roots fixes the vectors of that span. -/
theorem rootSpanProj_apply_of_mem {x : M} (hx : x ∈ P.rootSpan R) :
    P.rootSpanProj x = ⟨x, hx⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hx

/-- The kernel of the projection onto the span of the roots is the common kernel of the coroot
functionals. -/
@[simp]
theorem ker_rootSpanProj :
    LinearMap.ker P.rootSpanProj = ⨅ i, LinearMap.ker (P.coroot' i) :=
  Submodule.ker_projectionOnto _

/-- A vector and its projection onto the span of the roots differ by a vector on which every
coroot functional vanishes. -/
theorem sub_rootSpanProj_mem (x : M) :
    x - P.rootSpanProj x ∈ ⨅ i, LinearMap.ker (P.coroot' i) :=
  Submodule.sub_projection_mem _ x

/-- **The projection onto the span of the roots preserves every coroot value.** -/
theorem coroot'_rootSpanProj (i : ι) (x : M) : P.coroot' i (P.rootSpanProj x) = P.coroot' i x := by
  have h := Submodule.mem_iInf _ |>.mp (P.sub_rootSpanProj_mem x) i
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  exact h.symm

end RootPairing
