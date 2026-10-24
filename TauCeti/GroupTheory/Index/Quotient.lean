/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.QuotientGroup.Index
import TauCeti.GroupTheory.Index.Map

/-!
# The image index before and after quotienting

For a homomorphism `f : A →* B` and a normal subgroup `S ≤ B`, the order-index formula
relates the image index to its index after quotienting the target by `S`:

`[B : f(A)] · #f⁻¹(S) = [B/S : image(f)] · #S · #ker(f)`.

In particular, when `f` reflects torsion and the source torsion is finite, this computes the
correction between the cokernel on the whole group and the cokernel modulo torsion. The latter
is the index of the image on the free quotients of finitely generated abelian groups.

The proof uses Mathlib's order-index formula `Subgroup.card_ker_mul_card_range` and
Tau Ceti's image-index factorization `TauCeti.subgroup_index_map_mul_relIndex_ker`.
-/

public section

namespace TauCeti

variable {A B : Type*} [Group A] [Group B]

/-- The order-index formula relating a homomorphism's image index to its image after quotienting
the target by a normal subgroup. No finiteness is required for this cross-multiplied identity:
infinite orders and indices are read as `0`. -/
@[to_additive TauCeti.index_range_mul_card_comap
  /-- The order-index formula relating an additive homomorphism's image index to its image after
  quotienting the target by a normal subgroup. No finiteness is required:
  infinite orders and indices are read as `0`. -/]
theorem index_range_mul_card_comap_mul {f : A →* B} {S : Subgroup B} [S.Normal] :
    f.range.index * Nat.card (S.comap f) =
      (f.range.map (QuotientGroup.mk' S)).index * Nat.card S * Nat.card f.ker := by
  let T := S.comap f
  let I := T.map f
  have hker : f.ker ≤ T := MonoidHom.ker_le_comap f S
  have hkerCard : Nat.card (f.ker.subgroupOf T) = Nat.card f.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  have hT : Nat.card T = Nat.card f.ker * Nat.card I := by
    -- Count the kernel and image of the restriction to the inverse image of `S`.
    rw [← Subgroup.card_ker_mul_card_range (f.domRestrict T),
      MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, hkerCard]
  have hIS : I = f.range ⊓ S := by
    simpa [I, T, inf_comm] using Subgroup.map_comap_eq f S
  have hSI : f.range.relIndex S * Nat.card I = Nat.card S := by
    rw [← Subgroup.inf_relIndex_right, ← hIS, Subgroup.relIndex]
    have hcard : Nat.card (I.subgroupOf S) = Nat.card I :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hIS ▸ inf_le_right)).toEquiv
    rw [← hcard]
    exact Subgroup.index_mul_card _
  have hidx := subgroup_index_map_mul_relIndex_ker f.range
    (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S)
  rw [QuotientGroup.ker_mk'] at hidx
  rw [← hidx, hT]
  calc
    (f.range.map (QuotientGroup.mk' S)).index * f.range.relIndex S *
        (Nat.card f.ker * Nat.card I) =
        (f.range.map (QuotientGroup.mk' S)).index *
          (f.range.relIndex S * Nat.card I) * Nat.card f.ker := by ac_rfl
    _ = (f.range.map (QuotientGroup.mk' S)).index * Nat.card S * Nat.card f.ker := by rw [hSI]

end TauCeti
