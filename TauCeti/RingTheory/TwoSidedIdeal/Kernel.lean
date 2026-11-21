/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Kernels of two-sided ideal homomorphisms and product projections

This file provides general-purpose utilities for `TwoSidedIdeal.ker` extending
`Mathlib.RingTheory.TwoSidedIdeal.Kernel`:

* `TwoSidedIdeal.ker_congr`: homomorphisms with equal underlying functions have equal kernels;
* product projection kernel identities (`ker_fst_inf_ker_snd`, `ker_snd_inf_ker_fst`,
  `ker_fst_eq_bot_iff`, `ker_snd_eq_bot_iff`, `ker_nonUnitalStarAlgHom_fst`,
  `ker_nonUnitalStarAlgHom_snd`).
-/

public section

namespace TwoSidedIdeal

section Ker

/-- Two nonunital ring homomorphisms with equal underlying functions have equal kernels. -/
theorem ker_congr {A B F G : Type*} [NonUnitalNonAssocRing A] [NonUnitalNonAssocSemiring B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] [FunLike G A B] [NonUnitalRingHomClass G A B]
    {f : F} {g : G} (h : ∀ x, f x = g x) :
    TwoSidedIdeal.ker f = TwoSidedIdeal.ker g := by
  ext x
  simp [mem_ker, h]

end Ker

section Prod

/-- In a product `A × B`, the kernels of `fst` and `snd` meet trivially. -/
theorem ker_fst_inf_ker_snd {A B : Type*} [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] :
    TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) ⊓
      TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) = ⊥ := by
  ext p
  simp [mem_inf, mem_ker, NonUnitalRingHom.coe_fst, NonUnitalRingHom.coe_snd, Prod.ext_iff]

/-- In a product `A × B`, the kernels of `snd` and `fst` meet trivially. -/
theorem ker_snd_inf_ker_fst {A B : Type*} [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] :
    TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) ⊓
      TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) = ⊥ := by
  rw [inf_comm, ker_fst_inf_ker_snd]

/-- The kernel of `NonUnitalRingHom.fst A B` is trivial if and only if `B` is a subsingleton. -/
@[simp]
theorem ker_fst_eq_bot_iff {A B : Type*} [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] :
    TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) = ⊥ ↔ Subsingleton B := by
  rw [ker_eq_bot, NonUnitalRingHom.coe_fst]
  exact ⟨fun h => ⟨fun b₁ b₂ => congrArg Prod.snd (h (a₁ := (0, b₁)) (a₂ := (0, b₂)) rfl)⟩,
    fun _ => Prod.fst_injective⟩

/-- The kernel of `NonUnitalRingHom.snd A B` is trivial if and only if `A` is a subsingleton. -/
@[simp]
theorem ker_snd_eq_bot_iff {A B : Type*} [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] :
    TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) = ⊥ ↔ Subsingleton A := by
  rw [ker_eq_bot, NonUnitalRingHom.coe_snd]
  exact ⟨fun h => ⟨fun a₁ a₂ => congrArg Prod.fst (h (a₁ := (a₁, 0)) (a₂ := (a₂, 0)) rfl)⟩,
    fun _ => Prod.snd_injective⟩

/-- The kernel of `NonUnitalStarAlgHom.fst R A B` equals the kernel of
`NonUnitalRingHom.fst A B`. -/
theorem ker_nonUnitalStarAlgHom_fst (R A B : Type*) [Monoid R]
    [NonUnitalNonAssocRing A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocRing B] [DistribMulAction R B] [Star B] :
    TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst R A B) =
      TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) :=
  ker_congr fun p => by simp [NonUnitalRingHom.coe_fst]

/-- The kernel of `NonUnitalStarAlgHom.snd R A B` equals the kernel of
`NonUnitalRingHom.snd A B`. -/
theorem ker_nonUnitalStarAlgHom_snd (R A B : Type*) [Monoid R]
    [NonUnitalNonAssocRing A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocRing B] [DistribMulAction R B] [Star B] :
    TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd R A B) =
      TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) :=
  ker_congr fun p => by simp [NonUnitalRingHom.coe_snd]

end Prod

end TwoSidedIdeal
