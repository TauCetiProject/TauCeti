/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Star on ideal quotients

A two-sided ideal stable under star gives a star ring quotient. The quotient inherits
conjugate scalar multiplication when the original ring is a star algebra, and a star-algebra
equivalence mapping one star-stable ideal onto another descends to a star-algebra equivalence of
the quotients. This allows star-stable trace radicals to be divided out and compared before
introducing any norm.
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

section Equiv

variable {R B : Type*} [CommSemiring R] [Ring A] [StarRing A] [Algebra R A]
  [Ring B] [StarRing B] [Algebra R B]
  (I : Ideal A) [I.IsTwoSided] [I.IsStar] (J : Ideal B) [J.IsTwoSided] [J.IsStar]

/-- The star-algebra equivalence `(A ⧸ I) ≃⋆ₐ[R] B ⧸ J` induced by `f : A ≃⋆ₐ[R] B` when
`J = I.map f`. -/
def quotientEquivStarAlg (f : A ≃⋆ₐ[R] B) (hIJ : J = I.map (f : A →+* B)) :
    (A ⧸ I) ≃⋆ₐ[R] B ⧸ J :=
  StarAlgEquiv.ofAlgEquiv (quotientEquivAlg I J f.toAlgEquiv hIJ) fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    calc
      quotientEquivAlg I J f.toAlgEquiv hIJ (star (Ideal.Quotient.mk I a))
          = Ideal.Quotient.mk J (f (star a)) := rfl
      _ = Ideal.Quotient.mk J (star (f a)) := by rw [map_star]
      _ = star (quotientEquivAlg I J f.toAlgEquiv hIJ (Ideal.Quotient.mk I a)) := rfl

/-- `quotientEquivStarAlg` acts on a quotient class by applying `f` to any representative. -/
@[simp]
theorem quotientEquivStarAlg_mk (f : A ≃⋆ₐ[R] B) (hIJ : J = I.map (f : A →+* B)) (a : A) :
    quotientEquivStarAlg I J f hIJ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (f a) :=
  (rfl)

/-- Forgetting the star structure on `quotientEquivStarAlg` recovers `quotientEquivAlg`. -/
@[simp]
theorem toAlgEquiv_quotientEquivStarAlg (f : A ≃⋆ₐ[R] B) (hIJ : J = I.map (f : A →+* B)) :
    (quotientEquivStarAlg I J f hIJ).toAlgEquiv = quotientEquivAlg I J f.toAlgEquiv hIJ :=
  (rfl)

/-- Evaluation of `quotientEquivStarAlg` agrees with `quotientEquivAlg`. -/
theorem quotientEquivStarAlg_apply (f : A ≃⋆ₐ[R] B) (hIJ : J = I.map (f : A →+* B)) (x : A ⧸ I) :
    quotientEquivStarAlg I J f hIJ x = quotientEquivAlg I J f.toAlgEquiv hIJ x :=
  (rfl)

/-- The inverse of `quotientEquivStarAlg` is `quotientEquivStarAlg` for `f.symm`. -/
@[simp]
theorem quotientEquivStarAlg_symm (f : A ≃⋆ₐ[R] B) (hIJ : J = I.map (f : A →+* B)) :
    (quotientEquivStarAlg I J f hIJ).symm = quotientEquivStarAlg J I f.symm
      (by
        have hid : (f.symm : B →+* A).comp (f : A →+* B) = RingHom.id A := by ext; simp
        rw [hIJ, map_map, hid, map_id]) :=
  (rfl)

end Equiv

end Ideal
