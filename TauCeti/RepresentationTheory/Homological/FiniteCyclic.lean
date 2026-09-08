/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.FiniteCyclic
public import Mathlib.RepresentationTheory.Invariants

/-!
# Supplementary results on finite cyclic group representations

This file supplies general results about representations of cyclic groups that complement
Mathlib's finite-cyclic representation API.
-/

public noncomputable section

universe u

open LinearMap

namespace Rep.FiniteCyclicGroup

variable {R G : Type u} [CommRing R] [Group G] (M : Rep R G) (g : G)

/-- If `g` generates `G`, the invariants of a representation are the kernel of `ρ(g) - 1`. -/
theorem invariants_eq_ker_apply_sub (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    M.ρ.invariants = ker (M.ρ g - LinearMap.id) := by
  ext x
  simpa [sub_eq_zero] using
    Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x

end Rep.FiniteCyclicGroup
