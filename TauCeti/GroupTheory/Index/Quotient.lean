/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index

/-!
# The cokernel index before and after quotienting

For an additive homomorphism `f : A →+ B` and a subgroup `S ≤ B`, the order-index formula
relates the cokernel to its image after quotienting the target by `S`:

`[B : f(A)] · #f⁻¹(S) = [B/S : image(f)] · #S · #ker(f)`.

In particular, when `f` reflects torsion and the source torsion is finite, this computes the
correction between the cokernel on the whole group and the cokernel modulo torsion. The latter
is the index of the image on the free quotients of finitely generated abelian groups.

The proof uses Mathlib's order-index formula and second isomorphism theorem, through
`AddSubgroup.relIndex_sup_right` and `AddSubgroup.card_ker_mul_card_range`.
-/

public section

namespace TauCeti

variable {A B : Type*} [AddGroup A] [AddCommGroup B]

/-- The order-index formula relating a homomorphism's cokernel to its image after quotienting
the target by a subgroup. No finiteness is required for this cross-multiplied identity:
infinite orders and indices are read as `0`. -/
theorem index_range_mul_card_comap {f : A →+ B} {S : AddSubgroup B} :
    f.range.index * Nat.card (S.comap f) =
      (f.range.map (QuotientAddGroup.mk' S)).index * Nat.card S * Nat.card f.ker := by
  let T := S.comap f
  let I := T.map f
  have hker : f.ker ≤ T := AddMonoidHom.ker_le_comap f S
  have hkerCard : Nat.card (f.ker.addSubgroupOf T) = Nat.card f.ker :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hker).toEquiv
  have hT : Nat.card T = Nat.card f.ker * Nat.card I := by
    -- Count the kernel and image of the restriction to the inverse image of `S`.
    rw [← AddSubgroup.card_ker_mul_card_range (f.domRestrict T),
      AddMonoidHom.ker_domRestrict, AddMonoidHom.domRestrict_range, hkerCard]
  have hIS : I = f.range ⊓ S := by
    simpa [I, T, inf_comm] using AddSubgroup.map_comap_eq f S
  have hSI : f.range.relIndex S * Nat.card I = Nat.card S := by
    rw [← AddSubgroup.inf_relIndex_right, ← hIS, AddSubgroup.relIndex]
    have hcard : Nat.card (I.addSubgroupOf S) = Nat.card I :=
      Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (hIS ▸ inf_le_right)).toEquiv
    rw [← hcard]
    exact AddSubgroup.index_mul_card _
  have hidx : f.range.index = f.range.relIndex S * (f.range ⊔ S).index := by
    rw [← AddSubgroup.relIndex_sup_left S f.range]
    exact (AddSubgroup.relIndex_mul_index le_sup_left).symm
  have hquot : (f.range.map (QuotientAddGroup.mk' S)).index = (f.range ⊔ S).index := by
    rw [AddSubgroup.index_map, QuotientAddGroup.ker_mk', QuotientAddGroup.range_mk',
      AddSubgroup.index_top, mul_one]
  rw [hquot, hidx, hT]
  calc
    f.range.relIndex S * (f.range ⊔ S).index * (Nat.card f.ker * Nat.card I) =
        (f.range ⊔ S).index * (f.range.relIndex S * Nat.card I) * Nat.card f.ker := by ac_rfl
    _ = (f.range ⊔ S).index * Nat.card S * Nat.card f.ker := by rw [hSI]

end TauCeti
