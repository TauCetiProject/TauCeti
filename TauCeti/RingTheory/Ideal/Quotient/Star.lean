/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Star on ideal quotients

A two-sided ideal stable under star gives a star ring quotient. The quotient inherits
conjugate scalar multiplication when the original ring is a star algebra. This allows
star-stable trace radicals to be divided out before introducing any norm.
-/

public section

namespace Ideal

variable {A : Type*}

/-- An ideal is star-stable if it contains the adjoint of each of its elements. -/
class IsStar [Semiring A] [Star A] (I : Ideal A) : Prop where
  /-- Closure under the involution. -/
  star_mem : ∀ {a : A}, a ∈ I → star a ∈ I

section Membership

variable [Semiring A] [InvolutiveStar A] (I : Ideal A) [I.IsStar]

/-- Membership in a star-stable ideal is unchanged by the involution. -/
@[simp]
theorem star_mem_iff {a : A} : star a ∈ I ↔ a ∈ I :=
  ⟨fun h ↦ by simpa using IsStar.star_mem h, IsStar.star_mem⟩

end Membership

namespace Quotient

variable [Ring A] [StarRing A] (I : Ideal A) [I.IsTwoSided] [I.IsStar]

instance instStar : Star (A ⧸ I) where
  star := QuotientAddGroup.lift I.toAddSubgroup
    ((Ideal.Quotient.mk I).toAddMonoidHom.comp (starAddEquiv : A ≃+ A).toAddMonoidHom)
    (fun _ ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (IsStar.star_mem ha))

/-- Taking adjoints commutes with passing to the quotient. -/
@[simp]
theorem star_mk (a : A) : star (mk I a) = mk I (star a) := (rfl)

instance instStarRing : StarRing (A ⧸ I) where
  star_involutive x := by
    obtain ⟨a, rfl⟩ := mk_surjective x
    simp
  star_mul x y := by
    obtain ⟨a, rfl⟩ := mk_surjective x
    obtain ⟨b, rfl⟩ := mk_surjective y
    simp only [← map_mul, star_mk, star_mul]
  star_add x y := by
    obtain ⟨a, rfl⟩ := mk_surjective x
    obtain ⟨b, rfl⟩ := mk_surjective y
    simp only [← map_add, star_mk, star_add]

instance {R : Type*} [CommSemiring R] [StarRing R] [Algebra R A] [StarModule R A] :
    StarModule R (A ⧸ I) where
  star_smul r x := by
    obtain ⟨a, rfl⟩ := mk_surjective x
    calc
      star (r • mk I a) = star (mk I (r • a)) := by
        rw [← mkₐ_eq_mk R, map_smul]
      _ = mk I (star r • star a) := by rw [star_mk, star_smul]
      _ = star r • star (mk I a) := by
        rw [star_mk, ← mkₐ_eq_mk R, map_smul]

end Quotient
end Ideal
