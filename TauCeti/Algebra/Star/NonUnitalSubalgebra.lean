/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Algebra.Star.StarProjection
public import TauCeti.Order.Hereditary

/-!
# Direct `SMul` instance, order-hereditary nonunital `⋆`-subalgebras, `star a * A * a`, and corners

Mathlib defines `NonUnitalStarSubalgebra.instModule` at default priority while leaving the direct
`SMul R S` instance to `SetLike.smul` at priority `50`. Consequently, synthesizing `SMul R S`
directly (as `StarAlgEquiv` does) traverses the module and action hierarchy instead of resolving on
`NonUnitalStarSubalgebra` immediately, which can time out on operator algebras over submodules. We
register `NonUnitalStarSubalgebra.instSMul := SetLike.smul S` at default priority, definitionally
equal to `S.instModule.toSMul`.

This file also provides lattice closure properties of order heredity (`TauCeti.IsHereditary`) for
`NonUnitalStarSubalgebra`: `⊤` and `⊥` are hereditary, and the infimum `B₁ ⊓ B₂` of two hereditary
nonunital `⋆`-subalgebras is hereditary, together with `NonUnitalStarSubalgebra.mem_ofClass`.

For any element `a`, the elements `star a * x * a` form a nonunital `⋆`-subalgebra
`NonUnitalStarSubalgebra.starMulMul a`, since
`(star a * x * a) * (star a * y * a) = star a * (x * a * star a * y) * a`. Its closure in a
C⋆-algebra is hereditary, and for a projection `p` it is the corner `pAp`.

Finally, for a nonunital `⋆`-subalgebra `s` and a self-adjoint element `p`, we define the fixed
corner `s.corner hp = {a ∈ s | p * a = a ∧ a * p = a}` and the orthogonal corner
`s.orthoCorner hp = {a ∈ s | p * a = 0 ∧ a * p = 0}`, together with compression-image
characterizations when `p ∈ s` is a star projection (`NonUnitalStarSubalgebra.coe_corner_eq_image`,
`NonUnitalStarSubalgebra.coe_orthoCorner_eq_image`).
-/

public section

namespace NonUnitalStarSubalgebra

/-- Direct `R`-scalar action on the carrier of a `NonUnitalStarSubalgebra R A`, definitionally equal
to `S.instModule.toSMul`. -/
instance instSMul {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : SMul R S :=
  SetLike.smul S

open TauCeti

variable {R A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

/-- The top nonunital `⋆`-subalgebra is hereditary. -/
@[simp]
theorem isHereditary_top [LE A] : IsHereditary (⊤ : NonUnitalStarSubalgebra R A) :=
  isHereditary_def.mpr fun _ _ _ _ _ => trivial

/-- The bottom nonunital `⋆`-subalgebra is hereditary in any partially ordered ambient type. -/
@[simp]
theorem isHereditary_bot [PartialOrder A] : IsHereditary (⊥ : NonUnitalStarSubalgebra R A) := by
  rw [isHereditary_def]
  intro a b ha hab hb
  rw [NonUnitalStarAlgebra.mem_bot] at hb ⊢
  exact le_antisymm (hab.trans_eq hb) ha

/-- The intersection of two hereditary nonunital `⋆`-subalgebras is hereditary. -/
theorem isHereditary_inf [LE A] {B₁ B₂ : NonUnitalStarSubalgebra R A}
    (h₁ : IsHereditary B₁) (h₂ : IsHereditary B₂) : IsHereditary (B₁ ⊓ B₂) :=
  isHereditary_def.mpr fun _ _ ha hab hb => ⟨h₁.mem_of_le ha hab hb.1, h₂.mem_of_le ha hab hb.2⟩

section StarMulMul

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The nonunital `⋆`-subalgebra `star a * A * a` of elements `star a * x * a`. -/
def starMulMul (a : A) : NonUnitalStarSubalgebra R A where
  carrier := Set.range fun x ↦ star a * x * a
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by simp only [mul_add, add_mul]⟩
  zero_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * a * star a * y, by simp only [mul_assoc]⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl⟩
    exact ⟨c • x, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  star_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨star x, by simp [mul_assoc]⟩

variable {a x : A}

/-- Membership in `star a * A * a`. -/
@[simp]
theorem mem_starMulMul : x ∈ starMulMul (R := R) a ↔ ∃ y, star a * y * a = x :=
  Iff.rfl

/-- The underlying set of `star a * A * a`. -/
@[simp]
theorem coe_starMulMul (a : A) :
    (starMulMul (R := R) a : Set A) = Set.range fun x ↦ star a * x * a :=
  (rfl)

/-- `star a * A * a` contains every `star a * x * a`. -/
theorem star_mul_mul_mem_starMulMul (a x : A) : star a * x * a ∈ starMulMul (R := R) a :=
  ⟨x, rfl⟩

end StarMulMul

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
private theorem mem_mulCorner {s : NonUnitalStarSubalgebra R A} {p : A} {hp : IsSelfAdjoint p}
    {c : ℕ} {a : A} :
    a ∈ s.mulCorner hp c ↔ a ∈ s ∧ p * a = c • a ∧ a * p = c • a := Iff.rfl
/-- Fixed corner `{a ∈ s | p * a = a ∧ a * p = a}` (`p s p` when `p ∈ s` is a star projection). -/
def corner (s : NonUnitalStarSubalgebra R A) {p : A} (hp : IsSelfAdjoint p) :
    NonUnitalStarSubalgebra R A :=
  (s.mulCorner hp 1).copy {a : A | a ∈ s ∧ p * a = a ∧ a * p = a}
    (Set.ext fun _ ↦ by simp [mem_mulCorner])
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
  (s.mulCorner hp 0).copy {a : A | a ∈ s ∧ p * a = 0 ∧ a * p = 0}
    (Set.ext fun _ ↦ by simp [mem_mulCorner])
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
    x - p * x - x * p + p * x * p ∈ s.orthoCorner hp.isSelfAdjoint := by
  have hleft (y : A) : p * (y - p * y - y * p + p * y * p) = 0 := by
    rw [mul_add, mul_sub, mul_sub, ← mul_assoc p p y, ← mul_assoc p (p * y) p,
      ← mul_assoc p p y, hp.isIdempotentElem.eq, mul_assoc, sub_self, zero_sub, neg_add_cancel]
  have hright : (x - p * x - x * p + p * x * p) * p = 0 := by
    have h := congrArg star (hleft (star x))
    simp only [star_mul, star_add, star_sub, star_star, hp.isSelfAdjoint.star_eq, star_zero] at h
    rwa [sub_right_comm, ← mul_assoc p x p] at h
  exact mem_orthoCorner.mpr
    ⟨add_mem (sub_mem (sub_mem hx (mul_mem hp_mem hx)) (mul_mem hx hp_mem))
        (mul_mem (mul_mem hp_mem hx) hp_mem),
      hleft x, hright⟩
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
