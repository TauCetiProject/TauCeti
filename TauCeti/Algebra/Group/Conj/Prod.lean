/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Prod
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Conjugacy classes of a product

Conjugacy in a product is componentwise. The resulting equivalence of conjugacy classes
also identifies each class carrier with the product of the two carriers. In particular,
both the number of classes and the sizes of individual classes multiply. These comparisons
provide the column indexing for character tables of product groups.
-/

public section

namespace Prod

variable {M N : Type*} [Monoid M] [Monoid N]

/-- Two elements of a product are conjugate exactly when both components are conjugate. -/
@[simp]
theorem isConj_iff (a b : M × N) :
    IsConj a b ↔ IsConj a.1 b.1 ∧ IsConj a.2 b.2 := by
  constructor
  · intro h
    exact ⟨(MonoidHom.fst M N).map_isConj h, (MonoidHom.snd M N).map_isConj h⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨MulEquiv.prodUnits.symm (u, v), Prod.ext hu hv⟩

end Prod

namespace ConjClasses

variable (M N : Type*) [Monoid M] [Monoid N]

/-- Conjugacy classes of a product are pairs of conjugacy classes. -/
noncomputable def prodEquiv : ConjClasses (M × N) ≃ ConjClasses M × ConjClasses N :=
  Equiv.ofBijective (fun C => (C.map (MonoidHom.fst M N), C.map (MonoidHom.snd M N))) <| by
    constructor
    · intro C D h
      obtain ⟨a, rfl⟩ := mk_surjective C
      obtain ⟨b, rfl⟩ := mk_surjective D
      apply mk_eq_mk_iff_isConj.mpr
      exact (Prod.isConj_iff a b).mpr
        ⟨mk_eq_mk_iff_isConj.mp (congrArg Prod.fst h),
          mk_eq_mk_iff_isConj.mp (congrArg Prod.snd h)⟩
    · rintro ⟨C, D⟩
      obtain ⟨a, rfl⟩ := mk_surjective C
      obtain ⟨b, rfl⟩ := mk_surjective D
      exact ⟨ConjClasses.mk (a, b), rfl⟩

@[simp]
theorem prodEquiv_mk (a : M × N) :
    prodEquiv M N (ConjClasses.mk a) = (ConjClasses.mk a.1, ConjClasses.mk a.2) := (rfl)

@[simp]
theorem prodEquiv_symm_mk (a : M) (b : N) :
    (prodEquiv M N).symm (ConjClasses.mk a, ConjClasses.mk b) = ConjClasses.mk (a, b) :=
  (prodEquiv M N).symm_apply_apply (ConjClasses.mk (a, b))

/-- The number of conjugacy classes is multiplicative, with no finiteness assumption. -/
theorem natCard_prod :
    Nat.card (ConjClasses (M × N)) = Nat.card (ConjClasses M) * Nat.card (ConjClasses N) := by
  rw [Nat.card_congr (prodEquiv M N), Nat.card_prod]

/-- The carrier of a product class is the product of the carriers. -/
@[simp]
theorem carrier_prodEquiv_symm (C : ConjClasses M) (D : ConjClasses N) :
    ((prodEquiv M N).symm (C, D)).carrier = C.carrier ×ˢ D.carrier := by
  obtain ⟨a, rfl⟩ := mk_surjective C
  obtain ⟨b, rfl⟩ := mk_surjective D
  ext x
  simp [mem_carrier_iff_mk_eq, mk_eq_mk_iff_isConj]

/-- Sizes of corresponding conjugacy classes multiply, including infinite carriers. -/
theorem natCard_carrier_prodEquiv_symm (C : ConjClasses M) (D : ConjClasses N) :
    Nat.card ((prodEquiv M N).symm (C, D)).carrier = Nat.card C.carrier * Nat.card D.carrier := by
  rw [carrier_prodEquiv_symm, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]

end ConjClasses
