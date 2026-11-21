/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Stabilizers of vectors in a representation

This file complements Mathlib's `Representation.stabilizer` API: injective intertwining maps and
the inclusion of a subrepresentation preserve stabilizers, a vector is invariant under the
restriction to a subgroup exactly when that subgroup lies in its stabilizer, and the stabilizer of
a basis vector of a permutation representation is the stabilizer of the point.

## Main results

* `Representation.IntertwiningMap.stabilizer_apply_of_injective`
* `Subrepresentation.stabilizer_toRepresentation`
* `Representation.mem_invariants_comp_subtype_iff`
* `Representation.stabilizer_ofMulAction_single`
-/

public section

namespace Representation

section Semiring

variable {A G V W : Type*} [Semiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- The stabilizers of an injective intertwining map agree with those of its source. -/
theorem IntertwiningMap.stabilizer_apply_of_injective (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) (v : V) : σ.stabilizer (f v) = ρ.stabilizer v := by
  ext g
  rw [mem_stabilizer, mem_stabilizer, ← f.isIntertwining, hf.eq_iff]

/-- The stabilizer of a vector of a subrepresentation is its stabilizer in the ambient
representation. -/
@[simp]
theorem _root_.Subrepresentation.stabilizer_toRepresentation (ρ' : Subrepresentation ρ)
    (v : ρ'.toSubmodule) : ρ'.toRepresentation.stabilizer v = ρ.stabilizer v := by
  ext g
  rw [mem_stabilizer, mem_stabilizer, Subrepresentation.toRepresentation_apply_coe]

/-- The stabilizer of a basis vector of a permutation representation is the stabilizer of the
point, for nonzero coefficient. -/
theorem stabilizer_ofMulAction_single {X : Type*} [MulAction G X] (x : X) {r : A} (hr : r ≠ 0) :
    (ofMulAction A G X).stabilizer (MonoidAlgebra.single x r) = MulAction.stabilizer G x := by
  ext g
  rw [mem_stabilizer, ofMulAction_single, MonoidAlgebra.single_left_inj hr,
    MulAction.mem_stabilizer_iff]

end Semiring

section CommRing

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  {ρ : Representation A G V}

/-- A vector is invariant under the restriction of `ρ` to a subgroup `H` exactly when `H` lies in
its stabilizer. -/
theorem mem_invariants_comp_subtype_iff {H : Subgroup G} {v : V} :
    v ∈ invariants (ρ.comp H.subtype) ↔ H ≤ ρ.stabilizer v := by
  simp [mem_invariants, IsConcreteLE.le_iff]

end CommRing

end Representation
