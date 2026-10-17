/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IsPerfect

/-!
# Central surjections of perfect groups

A surjective homomorphism from a perfect group with central kernel induces an isomorphism
between the quotients by the centres. Grün's lemma identifies the preimage of the target's
centre with the source's centre; the first isomorphism theorem then gives the quotient map.
-/

public section

namespace MonoidHom

open Subgroup

variable {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]

/-- A central surjection from a perfect group pulls the centre back to the centre.

Perfectness is essential here: Grün's lemma identifies the second upper central subgroup
with the centre, so an element central modulo the kernel was already central. -/
theorem comap_center_of_ker_le_center (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ center G) : (center H).comap f = center G := by
  refine le_antisymm ?_ (map_le_iff_le_comap.mp (map_center_le_center hf))
  intro x hx
  rw [← Group.IsPerfect.upperCentralSeries_eq_center G (n := 2) (by decide)]
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one]
  apply hker
  rw [mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (mem_center_iff.mp hx (f y)).symm

/-- A central surjection from a perfect group induces an isomorphism modulo centres.
The forward map sends the class of `x` to the class of `f x`. -/
noncomputable def quotientCenterCongrOfSurjective (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker ≤ center G) :
    G ⧸ center G ≃* H ⧸ center H :=
  QuotientGroup.liftEquiv (center G) (φ := (QuotientGroup.mk' (center H)).comp f)
    ((QuotientGroup.mk'_surjective (center H)).comp hf)
    (by rw [← comap_ker, QuotientGroup.ker_mk', f.comap_center_of_ker_le_center hf hker])

@[simp]
theorem quotientCenterCongrOfSurjective_mk (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker ≤ center G) (x : G) :
    f.quotientCenterCongrOfSurjective hf hker (x : G ⧸ center G) =
      (f x : H ⧸ center H) := by
  simp only [quotientCenterCongrOfSurjective, QuotientGroup.liftEquiv_coe,
    comp_apply, QuotientGroup.mk'_apply]

end MonoidHom
