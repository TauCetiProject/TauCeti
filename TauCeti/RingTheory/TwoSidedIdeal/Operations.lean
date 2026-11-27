/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Pushforward and pullback operations on two-sided ideals

This file supplements `Mathlib.RingTheory.TwoSidedIdeal.Operations` with basic lemmas on
`TwoSidedIdeal.map` and `TwoSidedIdeal.comap` along nonunital ring homomorphisms, as well as
transport lemmas for `TwoSidedIdeal.op` and `TwoSidedIdeal.unop`.

## Main results

* `TwoSidedIdeal.map_le_iff_le_comap`: Galois connection between `TwoSidedIdeal.map` and
  `TwoSidedIdeal.comap`.
* `TwoSidedIdeal.coe_map_of_surjective` and `TwoSidedIdeal.mem_map_iff_of_surjective`: under a
  surjective nonunital ring homomorphism `f`, the pushforward ideal `TwoSidedIdeal.map f I` has
  underlying set `f '' I`.
* `TwoSidedIdeal.op_le_op_iff`, `TwoSidedIdeal.op_inj`, `TwoSidedIdeal.op_bot`,
  `TwoSidedIdeal.op_top`, `TwoSidedIdeal.op_inf`, `TwoSidedIdeal.op_sup` (and their `unop`
  counterparts): order, equality, and lattice transport along `TwoSidedIdeal.op` and
  `TwoSidedIdeal.unop`.
-/

public section

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {A B F : Type*} [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B]
  [FunLike F A B] [NonUnitalRingHomClass F A B]

/-- Galois connection between `TwoSidedIdeal.map` and `TwoSidedIdeal.comap`. -/
theorem map_le_iff_le_comap {f : F} {I : TwoSidedIdeal A} {J : TwoSidedIdeal B} :
    TwoSidedIdeal.map f I ≤ J ↔ I ≤ TwoSidedIdeal.comap f J := by
  rw [TwoSidedIdeal.map, TwoSidedIdeal.span_le]
  refine ⟨fun h a ha => (TwoSidedIdeal.mem_comap f).mpr (h (Set.mem_image_of_mem f ha)), ?_⟩
  rintro h _ ⟨a, ha, rfl⟩
  exact (TwoSidedIdeal.mem_comap f).mp (h ha)

/-- Under a surjective nonunital ring homomorphism, the pushforward ideal `TwoSidedIdeal.map f I`
has underlying set `f '' I` without needing further ideal generation. -/
theorem coe_map_of_surjective {f : F} (hf : Function.Surjective f) (I : TwoSidedIdeal A) :
    (TwoSidedIdeal.map f I : Set B) = f '' (I : Set A) := by
  let K : TwoSidedIdeal B := TwoSidedIdeal.mk' (f '' (I : Set A))
    ⟨0, I.zero_mem, map_zero f⟩
    (by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, I.add_mem hx hy, map_add f x y⟩)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨-x, I.neg_mem hx, map_neg f x⟩)
    (by rintro b _ ⟨y, hy, rfl⟩; obtain ⟨a, rfl⟩ := hf b
        exact ⟨a * y, I.mul_mem_left a y hy, map_mul f a y⟩)
    (by rintro _ b ⟨x, hx, rfl⟩; obtain ⟨a, rfl⟩ := hf b
        exact ⟨x * a, I.mul_mem_right x a hx, map_mul f x a⟩)
  refine Set.Subset.antisymm ?_ TwoSidedIdeal.subset_span
  have hle : TwoSidedIdeal.map f I ≤ K :=
    TwoSidedIdeal.span_le.mpr fun b hb => (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ b).mpr hb
  exact fun b hb => (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ b).mp (hle hb)

/-- Membership in `TwoSidedIdeal.map f I` for a surjective nonunital ring homomorphism `f`. -/
theorem mem_map_iff_of_surjective {f : F} (hf : Function.Surjective f) {I : TwoSidedIdeal A}
    {b : B} : b ∈ TwoSidedIdeal.map f I ↔ ∃ a ∈ I, f a = b := by
  rw [← SetLike.mem_coe, coe_map_of_surjective hf, Set.mem_image]
  simp

end NonUnitalNonAssocRing

section MulOpposite

variable {A : Type*} [NonUnitalNonAssocRing A]

@[simp]
theorem unop_op (I : TwoSidedIdeal A) : I.op.unop = I :=
  opOrderIso.left_inv I

@[simp]
theorem op_unop (I : TwoSidedIdeal Aᵐᵒᵖ) : I.unop.op = I :=
  opOrderIso.right_inv I

@[simp]
theorem op_le_op_iff {I J : TwoSidedIdeal A} : I.op ≤ J.op ↔ I ≤ J :=
  opOrderIso.le_iff_le

@[simp]
theorem unop_le_unop_iff {I J : TwoSidedIdeal Aᵐᵒᵖ} : I.unop ≤ J.unop ↔ I ≤ J :=
  opOrderIso.symm.le_iff_le

theorem op_injective :
    Function.Injective (TwoSidedIdeal.op : TwoSidedIdeal A → TwoSidedIdeal Aᵐᵒᵖ) :=
  opOrderIso.injective

theorem unop_injective :
    Function.Injective (TwoSidedIdeal.unop : TwoSidedIdeal Aᵐᵒᵖ → TwoSidedIdeal A) :=
  opOrderIso.symm.injective

@[simp]
theorem op_inj {I J : TwoSidedIdeal A} : I.op = J.op ↔ I = J :=
  opOrderIso.injective.eq_iff

@[simp]
theorem unop_inj {I J : TwoSidedIdeal Aᵐᵒᵖ} : I.unop = J.unop ↔ I = J :=
  opOrderIso.symm.injective.eq_iff

@[simp]
theorem op_bot : (⊥ : TwoSidedIdeal A).op = ⊥ :=
  opOrderIso.map_bot

@[simp]
theorem unop_bot : (⊥ : TwoSidedIdeal Aᵐᵒᵖ).unop = ⊥ :=
  opOrderIso.symm.map_bot

@[simp]
theorem op_eq_bot {I : TwoSidedIdeal A} : I.op = ⊥ ↔ I = ⊥ :=
  op_injective.eq_iff' op_bot

@[simp]
theorem unop_eq_bot {I : TwoSidedIdeal Aᵐᵒᵖ} : I.unop = ⊥ ↔ I = ⊥ :=
  unop_injective.eq_iff' unop_bot

@[simp]
theorem op_top : (⊤ : TwoSidedIdeal A).op = ⊤ :=
  opOrderIso.map_top

@[simp]
theorem unop_top : (⊤ : TwoSidedIdeal Aᵐᵒᵖ).unop = ⊤ :=
  opOrderIso.symm.map_top

@[simp]
theorem op_eq_top {I : TwoSidedIdeal A} : I.op = ⊤ ↔ I = ⊤ :=
  op_injective.eq_iff' op_top

@[simp]
theorem unop_eq_top {I : TwoSidedIdeal Aᵐᵒᵖ} : I.unop = ⊤ ↔ I = ⊤ :=
  unop_injective.eq_iff' unop_top

theorem op_inf (I J : TwoSidedIdeal A) : (I ⊓ J).op = I.op ⊓ J.op :=
  opOrderIso.map_inf I J

theorem unop_inf (I J : TwoSidedIdeal Aᵐᵒᵖ) : (I ⊓ J).unop = I.unop ⊓ J.unop :=
  opOrderIso.symm.map_inf I J

theorem op_sup (I J : TwoSidedIdeal A) : (I ⊔ J).op = I.op ⊔ J.op :=
  opOrderIso.map_sup I J

theorem unop_sup (I J : TwoSidedIdeal Aᵐᵒᵖ) : (I ⊔ J).unop = I.unop ⊔ J.unop :=
  opOrderIso.symm.map_sup I J

end MulOpposite

end TwoSidedIdeal
