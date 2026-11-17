/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# Range, kernel, and corner subalgebras for `⋆`-algebras

Mathlib defines `codRestrict` and `rangeRestrict` for `NonUnitalStarAlgHom`
(`Mathlib/Algebra/Star/NonUnitalSubalgebra.lean`) and `StarAlgHom`
(`Mathlib/Algebra/Star/Subalgebra.lean`), but omits surjectivity of `rangeRestrict` and
compatibility of `TwoSidedIdeal.ker` with codomain and range restriction. We supply both in
nonunital and unital generality, mirroring `AlgHom.rangeRestrict_surjective` and
`AlgHom.ker_rangeRestrict`.

For a nonunital `⋆`-subalgebra `s` and a self-adjoint element `p`, we also define the fixed corner
`s.corner hp = {a ∈ s | p * a = a ∧ a * p = a}` and the orthogonal corner
`s.orthoCorner hp = {a ∈ s | p * a = 0 ∧ a * p = 0}`, together with
`NonUnitalStarSubalgebra.mem_ofClass`.

## Main results

* `NonUnitalStarAlgHom.rangeRestrict_surjective` and `StarAlgHom.rangeRestrict_surjective`:
  restricting a `⋆`-algebra homomorphism to its `⋆`-subalgebra range yields a surjective map.
* `NonUnitalStarAlgHom.ker_codRestrict`, `NonUnitalStarAlgHom.ker_rangeRestrict`,
  `StarAlgHom.ker_codRestrict`, and `StarAlgHom.ker_rangeRestrict`: restricting the codomain or
  range preserves `TwoSidedIdeal.ker`.
* `NonUnitalStarSubalgebra.corner`, `NonUnitalStarSubalgebra.orthoCorner`: corner and orthogonal
  corner `⋆`-subalgebras at a self-adjoint element.

## Implementation notes

`NonUnitalStarAlgHom.rangeRestrict` is an `abbrev` for `NonUnitalStarAlgHom.codRestrict`, so
`@[simp]` is placed on `NonUnitalStarAlgHom.ker_codRestrict` (which already simplifies
`TwoSidedIdeal.ker f.rangeRestrict`), whereas `StarAlgHom.rangeRestrict` is an irreducible `def` and
receives its own `@[simp]` attribute.
-/

public section

namespace NonUnitalStarAlgHom

section RangeRestrict

variable {R A B : Type*} [CommSemiring R]
  [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

/-- Restricting a nonunital `⋆`-algebra homomorphism to its range gives a surjective map. -/
theorem rangeRestrict_surjective (f : A →⋆ₙₐ[R] B) : Function.Surjective f.rangeRestrict :=
  fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩

end RangeRestrict

section Ker

variable {R A B : Type*} [CommSemiring R]
  [NonUnitalNonAssocRing A] [Module R A] [Star A]
  [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

/-- Restricting the codomain of a nonunital `⋆`-algebra homomorphism to a nonunital `⋆`-subalgebra
preserves its two-sided ideal kernel. -/
@[simp]
theorem ker_codRestrict (f : A →⋆ₙₐ[R] B) (S : NonUnitalStarSubalgebra R B)
    (hf : ∀ x, f x ∈ S) :
    TwoSidedIdeal.ker (f.codRestrict S hf) = TwoSidedIdeal.ker f := by
  ext a
  rw [TwoSidedIdeal.mem_ker, TwoSidedIdeal.mem_ker, Subtype.ext_iff]
  rfl

/-- Restricting a nonunital `⋆`-algebra homomorphism to its range preserves its two-sided ideal
kernel. -/
theorem ker_rangeRestrict (f : A →⋆ₙₐ[R] B) :
    TwoSidedIdeal.ker f.rangeRestrict = TwoSidedIdeal.ker f :=
  f.ker_codRestrict f.range f.mem_range_self

end Ker

end NonUnitalStarAlgHom

namespace StarAlgHom

section RangeRestrict

variable {R A B : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [Algebra R A] [StarRing A]
  [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- Restricting a unital `⋆`-algebra homomorphism to its range gives a surjective map. -/
theorem rangeRestrict_surjective (f : A →⋆ₐ[R] B) : Function.Surjective f.rangeRestrict :=
  f.toAlgHom.rangeRestrict_surjective

end RangeRestrict

section Ker

variable {R A B : Type*} [CommSemiring R] [StarRing R]
  [Ring A] [Algebra R A] [StarRing A]
  [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- Restricting the codomain of a unital `⋆`-algebra homomorphism to a `⋆`-subalgebra preserves its
two-sided ideal kernel. -/
@[simp]
theorem ker_codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : ∀ x, f x ∈ S) :
    TwoSidedIdeal.ker (f.codRestrict S hf) = TwoSidedIdeal.ker f :=
  f.toNonUnitalStarAlgHom.ker_codRestrict S.toNonUnitalStarSubalgebra hf

/-- Restricting a unital `⋆`-algebra homomorphism to its range preserves its two-sided ideal kernel.
-/
@[simp]
theorem ker_rangeRestrict (f : A →⋆ₐ[R] B) :
    TwoSidedIdeal.ker f.rangeRestrict = TwoSidedIdeal.ker f :=
  f.ker_codRestrict f.range fun x => ⟨x, rfl⟩

end Ker

end StarAlgHom

namespace NonUnitalStarSubalgebra
section OfClass
variable {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [SetLike S A] [NonUnitalSubsemiringClass S A] [SMulMemClass S R A] [StarMemClass S A]
/-- Membership in `NonUnitalStarSubalgebra.ofClass s` is membership in `s`. -/
@[simp] theorem mem_ofClass {s : S} {x : A} : x ∈ ofClass (R := R) s ↔ x ∈ s := Iff.rfl
end OfClass

section Corner
variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
private def mulCorner (s : NonUnitalStarSubalgebra R A) {p : A} (hp : IsSelfAdjoint p) (c : ℕ) :
    NonUnitalStarSubalgebra R A where
  carrier := {a : A | a ∈ s ∧ p * a = c • a ∧ a * p = c • a}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by simp [mul_add, ha.2.1, hb.2.1],
    by simp [add_mul, ha.2.2, hb.2.2]⟩
  zero_mem' := ⟨zero_mem s, by simp, by simp⟩
  mul_mem' ha hb := ⟨mul_mem ha.1 hb.1, by rw [← mul_assoc, ha.2.1, ← Nat.cast_smul_eq_nsmul R c,
    smul_mul_assoc, Nat.cast_smul_eq_nsmul], by rw [mul_assoc, hb.2.2, ← Nat.cast_smul_eq_nsmul R c,
    mul_smul_comm, Nat.cast_smul_eq_nsmul]⟩
  smul_mem' r _ ha := ⟨SMulMemClass.smul_mem r ha.1, by rw [mul_smul_comm, ha.2.1, smul_comm],
    by rw [smul_mul_assoc, ha.2.2, smul_comm]⟩
  star_mem' ha := ⟨star_mem ha.1, by rw [← hp.star_eq, ← star_mul, ha.2.2, star_nsmul],
    by rw [← hp.star_eq, ← star_mul, ha.2.1, star_nsmul]⟩
/-- Fixed corner `{a ∈ s | p * a = a ∧ a * p = a}` (`p s p` when `p ∈ s` is a star projection). -/
def corner (s : NonUnitalStarSubalgebra R A) {p : A} (hp : IsSelfAdjoint p) :
    NonUnitalStarSubalgebra R A :=
  (s.mulCorner hp 1).copy {a : A | a ∈ s ∧ p * a = a ∧ a * p = a} (by ext; simp [mulCorner]; rfl)
/-- Underlying set of `NonUnitalStarSubalgebra.corner`. -/
theorem coe_corner (s : NonUnitalStarSubalgebra R A) {p : A} (hp : IsSelfAdjoint p) :
    (s.corner hp : Set A) = {a : A | a ∈ s ∧ p * a = a ∧ a * p = a} := (rfl)
/-- Membership in `NonUnitalStarSubalgebra.corner`. -/
@[simp] theorem mem_corner {s : NonUnitalStarSubalgebra R A} {p : A} {hp : IsSelfAdjoint p}
    {a : A} : a ∈ s.corner hp ↔ a ∈ s ∧ p * a = a ∧ a * p = a := Iff.rfl
/-- Orthogonal corner `{a ∈ s | p * a = 0 ∧ a * p = 0}` (equals `(1 - p) s (1 - p)` in a unital
ring when `p ∈ s` is a star projection and `s` is closed under subtraction). -/
def orthoCorner (s : NonUnitalStarSubalgebra R A) {p : A} (hp : IsSelfAdjoint p) :
    NonUnitalStarSubalgebra R A :=
  (s.mulCorner hp 0).copy {a : A | a ∈ s ∧ p * a = 0 ∧ a * p = 0} (by ext; simp [mulCorner]; rfl)
/-- Underlying set of `NonUnitalStarSubalgebra.orthoCorner`. -/
theorem coe_orthoCorner (s : NonUnitalStarSubalgebra R A) {p : A} (hp : IsSelfAdjoint p) :
    (s.orthoCorner hp : Set A) = {a : A | a ∈ s ∧ p * a = 0 ∧ a * p = 0} := (rfl)
/-- Membership in `NonUnitalStarSubalgebra.orthoCorner`. -/
@[simp] theorem mem_orthoCorner {s : NonUnitalStarSubalgebra R A} {p : A} {hp : IsSelfAdjoint p}
    {a : A} : a ∈ s.orthoCorner hp ↔ a ∈ s ∧ p * a = 0 ∧ a * p = 0 := Iff.rfl
end Corner
end NonUnitalStarSubalgebra
