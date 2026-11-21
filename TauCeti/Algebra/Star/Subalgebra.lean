/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
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
`NonUnitalStarSubalgebra.mem_ofClass` and compression-image characterizations when `p ∈ s` is a
star projection (`NonUnitalStarSubalgebra.coe_corner_eq_image`,
`NonUnitalStarSubalgebra.coe_orthoCorner_eq_image`).

## Main results

* `NonUnitalStarAlgHom.rangeRestrict_surjective` and `StarAlgHom.rangeRestrict_surjective`:
  restricting a `⋆`-algebra homomorphism to its `⋆`-subalgebra range yields a surjective map.
* `NonUnitalStarAlgHom.ker_codRestrict`, `NonUnitalStarAlgHom.ker_rangeRestrict`,
  `StarAlgHom.ker_codRestrict`, and `StarAlgHom.ker_rangeRestrict`: restricting the codomain or
  range preserves `TwoSidedIdeal.ker`.
* `NonUnitalStarSubalgebra.corner`, `NonUnitalStarSubalgebra.orthoCorner`,
  `NonUnitalStarSubalgebra.coe_corner_eq_image`,
  `NonUnitalStarSubalgebra.coe_orthoCorner_eq_image`: corner and orthogonal corner `⋆`-subalgebras
  and their compression-image characterizations at a star projection in `s`.

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
/-- Compression by `p` fixes every member of `s.corner hp`. -/
theorem mul_mul_eq_of_mem_corner {s : NonUnitalStarSubalgebra R A} {p : A}
    {hp : IsSelfAdjoint p} {x : A} (hx : x ∈ s.corner hp) : p * x * p = x := by
  rw [(mem_corner.mp hx).2.1, (mem_corner.mp hx).2.2]
/-- Compressing an element of `s` by a star projection `p ∈ s` lands in `s.corner`. -/
theorem mul_mul_mem_corner {s : NonUnitalStarSubalgebra R A} {p : A} (hp : IsStarProjection p)
    (hp_mem : p ∈ s) {x : A} (hx : x ∈ s) : p * x * p ∈ s.corner hp.isSelfAdjoint :=
  mem_corner.mpr ⟨mul_mem (mul_mem hp_mem hx) hp_mem,
    by rw [← mul_assoc p (p * x) p, ← mul_assoc p p x, hp.isIdempotentElem.eq],
    by rw [mul_assoc, hp.isIdempotentElem.eq]⟩
/-- Membership in `s.corner hp.isSelfAdjoint` when `p ∈ s` is a star projection: `p y p` form. -/
theorem mem_corner_iff_exists {s : NonUnitalStarSubalgebra R A} {p : A} (hp : IsStarProjection p)
    (hp_mem : p ∈ s) {x : A} :
    x ∈ s.corner hp.isSelfAdjoint ↔ ∃ y ∈ s, p * y * p = x :=
  ⟨fun hx ↦ ⟨x, (mem_corner.mp hx).1, mul_mul_eq_of_mem_corner hx⟩,
   fun ⟨_, hy, hxy⟩ ↦ hxy ▸ mul_mul_mem_corner hp hp_mem hy⟩
/-- When `p ∈ s` is a star projection, `s.corner` is the image of `s` under `x ↦ p * x * p`. -/
theorem coe_corner_eq_image (s : NonUnitalStarSubalgebra R A) {p : A} (hp : IsStarProjection p)
    (hp_mem : p ∈ s) :
    (s.corner hp.isSelfAdjoint : Set A) = (fun x ↦ p * x * p) '' (s : Set A) :=
  Set.ext fun _ ↦ mem_corner_iff_exists hp hp_mem
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

section OrthoCorner
/-- Orthogonal compression `x ↦ x - p * x - x * p + p * x * p` fixes every member of
`s.orthoCorner hp`. -/
theorem sub_sub_add_eq_of_mem_orthoCorner {R A : Type*} [CommSemiring R] [NonUnitalRing A]
    [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    {s : NonUnitalStarSubalgebra R A} {p : A} {hp : IsSelfAdjoint p} {x : A}
    (hx : x ∈ s.orthoCorner hp) :
    x - p * x - x * p + p * x * p = x := by
  obtain ⟨_, hpx, hxp⟩ := mem_orthoCorner.mp hx
  rw [hpx, hxp, zero_mul, sub_zero, sub_zero, add_zero]

variable {R A : Type*} [CommRing R] [NonUnitalRing A] [StarRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
/-- Orthogonal compression `x ↦ x - p * x - x * p + p * x * p` of an element of `s` by a star
projection `p ∈ s` lands in `s.orthoCorner`. -/
theorem sub_sub_add_mem_orthoCorner {s : NonUnitalStarSubalgebra R A} {p : A}
    (hp : IsStarProjection p) (hp_mem : p ∈ s) {x : A} (hx : x ∈ s) :
    x - p * x - x * p + p * x * p ∈ s.orthoCorner hp.isSelfAdjoint :=
  mem_orthoCorner.mpr
    ⟨add_mem (sub_mem (sub_mem hx (mul_mem hp_mem hx)) (mul_mem hx hp_mem))
        (mul_mem (mul_mem hp_mem hx) hp_mem),
      by rw [mul_add, mul_sub, mul_sub, ← mul_assoc p p x, ← mul_assoc p (p * x) p,
        ← mul_assoc p p x, hp.isIdempotentElem.eq, mul_assoc, sub_self, zero_sub, neg_add_cancel],
      by rw [add_mul, sub_mul, sub_mul, mul_assoc x p p, mul_assoc (p * x) p p,
        hp.isIdempotentElem.eq, sub_right_comm, sub_self, zero_sub, neg_add_cancel]⟩
/-- Membership in `s.orthoCorner hp.isSelfAdjoint` when `p ∈ s` is a star projection:
`y - p * y - y * p + p * y * p` form. -/
theorem mem_orthoCorner_iff_exists {s : NonUnitalStarSubalgebra R A} {p : A}
    (hp : IsStarProjection p) (hp_mem : p ∈ s) {x : A} :
    x ∈ s.orthoCorner hp.isSelfAdjoint ↔ ∃ y ∈ s, y - p * y - y * p + p * y * p = x :=
  ⟨fun hx ↦ ⟨x, (mem_orthoCorner.mp hx).1, sub_sub_add_eq_of_mem_orthoCorner hx⟩,
   fun ⟨_, hy, hxy⟩ ↦ hxy ▸ sub_sub_add_mem_orthoCorner hp hp_mem hy⟩
/-- When `p ∈ s` is a star projection, `s.orthoCorner` is the image of `s` under
`x ↦ x - p * x - x * p + p * x * p`. -/
theorem coe_orthoCorner_eq_image (s : NonUnitalStarSubalgebra R A) {p : A}
    (hp : IsStarProjection p) (hp_mem : p ∈ s) :
    (s.orthoCorner hp.isSelfAdjoint : Set A) =
      (fun x ↦ x - p * x - x * p + p * x * p) '' (s : Set A) :=
  Set.ext fun _ ↦ mem_orthoCorner_iff_exists hp hp_mem
end OrthoCorner
end NonUnitalStarSubalgebra
