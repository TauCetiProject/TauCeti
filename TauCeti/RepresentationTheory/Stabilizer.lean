/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Stabilizers of vectors in a representation

This file complements Mathlib's `Representation.stabilizer` API: injective intertwining maps and
the inclusion of a subrepresentation preserve stabilizers, a vector is invariant under the
restriction to a subgroup exactly when that subgroup lies in its stabilizer, and the stabilizer of
a basis vector of a permutation representation is the stabilizer of the point.

For a vector `v : V`, the **orbit map** `G ⧸ stabilizer ρ v → V`, `[g] ↦ ρ g v`
(`Representation.orbitMap`), is well defined because `ρ g v` depends only on the coset
`g (stabilizer ρ v)`. It is equivariant for the action of `G` on the cosets by left multiplication
(`Representation.orbitMap_smul`), injective (`Representation.orbitMap_injective`), and its range is
the orbit `{ρ g v | g ∈ G}` of `v` (`Representation.range_orbitMap`). The coadjoint orbit
`G ⧸ G_ν` of a Lie group, with the orbit map of the coadjoint representation, is the main instance.

## Main results

* `Representation.IntertwiningMap.stabilizer_apply_of_injective`
* `Subrepresentation.stabilizer_toRepresentation`
* `Representation.mem_invariants_comp_subtype_iff`
* `Representation.stabilizer_ofMulAction_single`
* `Representation.orbitMap_smul`, `Representation.orbitMap_injective`,
  `Representation.range_orbitMap`
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

section OrbitMap

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (v : V)

/-- The **orbit map** `[g] ↦ ρ g v` from the cosets of the stabilizer of `v` to `V`. It is a
bijection onto the orbit of `v` (`Representation.orbitMap_injective`,
`Representation.range_orbitMap`). -/
def orbitMap : G ⧸ ρ.stabilizer v → V :=
  Quotient.lift (s := QuotientGroup.leftRel _) (fun g : G ↦ ρ g v) fun g h hgh ↦ by
    have hk : ρ (g⁻¹ * h) v = v := mem_stabilizer.1 (QuotientGroup.leftRel_apply.1 hgh)
    rw [← mul_inv_cancel_left g h, map_mul, mul_apply_eq_comp, hk]

/-- The orbit map sends the coset of `g` to `ρ g v`. -/
@[simp]
theorem orbitMap_mk (g : G) : ρ.orbitMap v (g : G ⧸ ρ.stabilizer v) = ρ g v :=
  (rfl)

/-- The orbit map is equivariant for the action of `G` on the cosets of the stabilizer by left
multiplication. -/
@[simp]
theorem orbitMap_smul (h : G) (x : G ⧸ ρ.stabilizer v) :
    ρ.orbitMap v (h • x) = ρ h (ρ.orbitMap v x) := by
  induction x using QuotientGroup.induction_on with
  | H g => rw [MulAction.Quotient.smul_coe, smul_eq_mul, orbitMap_mk, orbitMap_mk, map_mul,
    mul_apply_eq_comp]

/-- The orbit map is injective: `ρ g v = ρ h v` exactly when `g⁻¹ h` stabilizes `v`. -/
theorem orbitMap_injective : Function.Injective (ρ.orbitMap v) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H g =>
  induction y using QuotientGroup.induction_on with | H h =>
  refine QuotientGroup.eq.2 (mem_stabilizer.2 ?_)
  rw [orbitMap_mk, orbitMap_mk] at hxy
  rw [map_mul, mul_apply_eq_comp, ← hxy, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
    map_one, one_apply_eq_self]

/-- The range of the orbit map is the orbit `{ρ g v | g ∈ G}` of `v`. -/
theorem range_orbitMap : Set.range (ρ.orbitMap v) = Set.range fun g : G ↦ ρ g v :=
  (QuotientGroup.mk_surjective.range_comp (ρ.orbitMap v)).symm

end OrbitMap

end Representation
