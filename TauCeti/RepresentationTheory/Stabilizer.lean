/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RepresentationTheory.Stabilizer

/-!
# The orbit map of a representation

For a representation `ρ` of a group `G` on `V` and a vector `v : V`, the **orbit map**
`G ⧸ stabilizer ρ v → V`, `[g] ↦ ρ g v` (`Representation.orbitMap`), is well defined because
`ρ g v` depends only on the coset `g (stabilizer ρ v)`. It is equivariant for the action of `G` on
the cosets by left multiplication (`Representation.orbitMap_smul`), injective
(`Representation.orbitMap_injective`), and its range is the orbit `{ρ g v | g ∈ G}` of `v`
(`Representation.range_orbitMap`).

The coadjoint orbit `G ⧸ G_ν` of a Lie group, with the orbit map of the coadjoint representation,
is the main instance.
-/

public section

namespace Representation

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

end Representation
