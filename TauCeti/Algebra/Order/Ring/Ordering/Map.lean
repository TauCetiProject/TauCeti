/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Ring.Ordering.Basic
public import TauCeti.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.RingTheory.SimpleRing.Basic

/-! # Restriction and transport of ring preorderings

Mathlib's `Subsemiring.comap` and `Subsemiring.map` restrict and transport the
underlying positive cones. This file proves that these operations preserve the
preordering and ordering properties, under surjectivity and kernel containment for
images. It also identifies the induced orders along field embeddings.

## References

* T. Y. Lam, *An introduction to real algebra*, Rocky Mountain J. Math. 14 (1984), §1.
-/

public section

namespace Subsemiring

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Restriction of a spanning cone commutes with its support ideal. -/
@[simp] theorem supportIdeal_comap (P : Subsemiring B) (hP : P.IsSpanning) (f : A →+* B) :
    (P.comap f).supportIdeal (hP.comap f.toAddMonoidHom) =
      Ideal.comap f (P.supportIdeal hP) := by
  ext x
  -- Support-ideal membership is membership of both signs. Unwrap the two comaps
  -- so that `map_neg` sees the ring-hom application rather than an ideal membership.
  change (f x ∈ P ∧ f (-x) ∈ P) ↔ (f x ∈ P ∧ -f x ∈ P)
  rw [map_neg]

/-- The inverse image of a preordering is a preordering. -/
theorem IsPreordering.comap {P : Subsemiring B} (hP : P.IsPreordering) (f : A →+* B) :
    (P.comap f).IsPreordering where
  mem_of_isSquare := by
    rintro x ⟨y, rfl⟩
    simpa using hP.mul_self_mem (f y)
  neg_one_notMem := by simpa using hP.neg_one_notMem

/-- The surjective image of a preordering containing the kernel is a preordering. -/
theorem IsPreordering.map {P : Subsemiring A} (hP : P.IsPreordering) {f : A →+* B}
    (hf : Function.Surjective f) (hker : (RingHom.ker f : Set A) ⊆ P) :
    (P.map f).IsPreordering where
  mem_of_isSquare := by
    rintro y ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := hf z
    exact ⟨x * x, hP.mul_self_mem x, map_mul f x x⟩
  neg_one_notMem := by
    rintro ⟨x, hx, hfx⟩
    have hk : -(x + 1) ∈ P := hker (RingHom.mem_ker.mpr (by simp [hfx]))
    exact hP.neg_one_notMem (by simpa using P.add_mem hx hk)

/-- The restriction of an ordering is an ordering. -/
theorem IsOrdering.comap {P : Subsemiring B} (hP : P.IsOrdering) (f : A →+* B) :
    (P.comap f).IsOrdering :=
  (hP.isPreordering.comap f).isOrdering_iff.mpr fun a b h ↦ by
    simpa using hP.isPreordering.isOrdering_iff.mp hP (f a) (f b) (by simpa using h)

/-- The surjective image of an ordering containing the kernel is an ordering. -/
theorem IsOrdering.map {P : Subsemiring A} (hP : P.IsOrdering) {f : A →+* B}
    (hf : Function.Surjective f) (hker : (RingHom.ker f : Set A) ⊆ P) :
    (P.map f).IsOrdering :=
  (hP.isPreordering.map hf hker).isOrdering_iff.mpr fun a b h ↦ by
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    rw [← map_mul, ← map_neg, mem_map_iff_mem_of_ker_subset hker] at h
    simpa only [mem_map_iff_mem_of_ker_subset hker] using
      hP.isPreordering.isOrdering_iff.mp hP x y h

section Field

variable {K L : Type*} [Field K] [Field L] {P : Subsemiring L}

/-- An embedding preserves the cone order exactly when its pullback is the nonnegative cone. -/
theorem IsOrdering.strictMono_iff_nonneg_iff_mem_comap [LinearOrder K] [IsOrderedAddMonoid K]
    (hP : P.IsOrdering) (f : K →+* L) :
    letI := LinearOrder.ofAddSubmonoid hP.isPreordering.isPointed hP.isSpanning
      (dec := Classical.decPred _)
    StrictMono f ↔ ∀ x, 0 ≤ x ↔ x ∈ P.comap f := by
  let := LinearOrder.ofAddSubmonoid hP.isPreordering.isPointed hP.isSpanning
    (dec := Classical.decPred _)
  have : IsOrderedRing L := IsOrderedRing.ofSubsemiring hP.isPreordering.isPointed
  have hnonneg (x : L) : 0 ≤ x ↔ x ∈ P := by
    -- This locally constructed order uses cone membership of the difference as `≤`.
    -- Expose that relation so `sub_zero` can identify its nonnegative cone.
    change x - 0 ∈ P ↔ x ∈ P
    rw [sub_zero]
  refine ⟨fun hf x ↦ ?_, fun h ↦ ?_⟩
  · rw [mem_comap, ← hnonneg, ← map_zero f]
    exact hf.le_iff_le.symm
  · refine ((monotone_iff_map_nonneg f).mpr fun x hx ↦ ?_).strictMono_of_injective f.injective
    exact (hnonneg _).mpr ((h x).mp hx)

/-- The cone order on the pullback makes a field embedding strictly monotone. -/
theorem IsOrdering.strictMono_comap (hP : P.IsOrdering) (f : K →+* L) :
    letI := LinearOrder.ofAddSubmonoid (hP.comap f).isPreordering.isPointed
      (hP.comap f).isSpanning (dec := Classical.decPred _)
    letI := LinearOrder.ofAddSubmonoid hP.isPreordering.isPointed hP.isSpanning
      (dec := Classical.decPred _)
    StrictMono f := by
  let := LinearOrder.ofAddSubmonoid (hP.comap f).isPreordering.isPointed
    (hP.comap f).isSpanning (dec := Classical.decPred _)
  have : IsOrderedRing K := IsOrderedRing.ofSubsemiring (hP.comap f).isPreordering.isPointed
  apply (hP.strictMono_iff_nonneg_iff_mem_comap f).mpr
  intro x
  -- The pulled-back order likewise defines nonnegativity by membership of `x - 0`.
  change x - 0 ∈ P.comap f ↔ x ∈ P.comap f
  rw [sub_zero]

end Field

end Subsemiring
