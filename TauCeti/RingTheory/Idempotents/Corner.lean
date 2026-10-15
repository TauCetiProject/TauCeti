/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents

/-!
# Corners cut out by two idempotents

Let `A` be a nonunital algebra over a semiring `k`: a nonunital semiring with a `k`-module
structure whose scalar multiplication commutes with multiplication on either side. This file
defines the corner `eAf` as the range of Mathlib's `LinearMap.mulLeftRight k (e, f)`, the linear
map `x ↦ e * x * f`. When `e` and `f` are idempotent, membership is equivalent to the fixed-point
equation `e * x * f = x`.

The second part concerns Mathlib's corner ring `IsIdempotentElem.Corner` of an idempotent `e`, the
ring `eAe` with unit `e`. Mathlib gives it a semiring structure even when `A` has no unit, and a
ring structure when `A` is a nonunital ring. The corner inherits the compatible scalar action
and module structure of `A`. Over a commutative semiring `R`, this makes it an `R`-algebra,
with `algebraMap R eAe r = r • e`. When `A` is unital, this is the structure under which `eAe`
can be compared with `A` as `R`-algebras, for instance through Mathlib's `MoritaEquivalence`.

## Main definitions

* `TauCeti.cornerSubmodule`: the corner `eAf`, as a `k`-submodule of `A`.
* `IsIdempotentElem.Corner.instAlgebra`: the corner `eAe` of an idempotent of a nonunital
  `R`-algebra is a unital `R`-algebra.
* `IsIdempotentElem.cornerLinearEquivCornerSubmodule`: the corner ring `eAe`, as an `R`-module,
  agrees with the corner submodule `TauCeti.cornerSubmodule R e e`.
* `IsIdempotentElem.cornerMap`: a homomorphism of nonunital semirings restricts to a unital
  homomorphism of corners; a surjective homomorphism remains surjective on corners.
* `IsIdempotentElem.cornerEquiv`: a ring equivalence restricts to an equivalence of corners.
* `IsIdempotentElem.cornerPiEquiv`: the corner of an idempotent in a product of rings is the
  product of the corners of its components.

## Main results

* `TauCeti.mem_cornerSubmodule_iff`: the fixed-point characterization of an idempotent corner.
* `IsIdempotentElem.mul_corner_val` and `IsIdempotentElem.corner_val_mul`: an element of the
  corner ring `eAe` is fixed by `e` on both sides.
* `Pi.isIdempotentElem_iff`: an element of a product is idempotent exactly when each component
  is.

## References

See I. Assem, D. Simson, A. Skowroński,
*Elements of the Representation Theory of Associative Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

universe u v

variable (k : Type v) [Semiring k] {A : Type u} [NonUnitalSemiring A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A]

/-- **The corner `eAf`**, as a `k`-submodule of `A`: the range of the map `x ↦ e * x * f`. -/
def cornerSubmodule (e f : A) : Submodule k A :=
  LinearMap.range (LinearMap.mulLeftRight k (e, f))

/-- The corner submodule is the range of the corner map. -/
theorem cornerSubmodule_def (e f : A) :
    cornerSubmodule k e f = LinearMap.range (LinearMap.mulLeftRight k (e, f)) := (rfl)

/-- Cutting an element down by `e` on the left and `f` on the right lands in the corner `eAf`. -/
theorem mul_mul_mem_cornerSubmodule (e f x : A) : e * x * f ∈ cornerSubmodule k e f :=
  ⟨x, by simp only [LinearMap.mulLeftRight_apply]⟩

/-- For idempotents `e` and `f`, an element belongs to the corner `eAf` exactly when multiplying it
by `e` on the left and by `f` on the right fixes it. -/
@[simp]
theorem mem_cornerSubmodule_iff {e f x : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : x ∈ cornerSubmodule k e f ↔ e * x * f = x := by
  constructor
  · rintro ⟨y, rfl⟩
    simp only [LinearMap.mulLeftRight_apply]
    calc
      e * (e * y * f) * f = (e * e) * y * (f * f) := by simp only [mul_assoc]
      _ = e * y * f := by rw [he.eq, hf.eq]
  · intro h
    exact ⟨x, by simpa only [LinearMap.mulLeftRight_apply] using h⟩

variable {k}

/-- An element of the corner `eAf` is fixed by `e` on the left. -/
theorem mul_eq_self_of_mem_cornerSubmodule {e f x : A} (he : IsIdempotentElem e)
    (hx : x ∈ cornerSubmodule k e f) : e * x = x := by
  rcases hx with ⟨y, rfl⟩
  simp only [LinearMap.mulLeftRight_apply, ← mul_assoc, he.eq]

/-- An element of the corner `eAf` is fixed by `f` on the right. -/
theorem mul_eq_self_of_mem_cornerSubmodule_right {e f x : A} (hf : IsIdempotentElem f)
    (hx : x ∈ cornerSubmodule k e f) : x * f = x := by
  rcases hx with ⟨y, rfl⟩
  simp only [LinearMap.mulLeftRight_apply]
  rw [mul_assoc, hf.eq]

end TauCeti

/-! ### The corner ring as an algebra -/

namespace IsIdempotentElem

section Semigroup

variable {A : Type u} [Semigroup A] {e : A} (he : IsIdempotentElem e)

/-- An element of the corner `eAe` is fixed by `e` on the left. -/
@[simp]
theorem mul_corner_val (b : he.Corner) : e * b.1 = b.1 :=
  ((Subsemigroup.mem_corner_iff he).1 b.2).1

/-- An element of the corner `eAe` is fixed by `e` on the right. -/
@[simp]
theorem corner_val_mul (b : he.Corner) : b.1 * e = b.1 :=
  ((Subsemigroup.mem_corner_iff he).1 b.2).2

namespace Corner

variable {he} {R : Type v} [SMul R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- A scalar action compatible with multiplication restricts to the corner. -/
instance instSMul : SMul R he.Corner where
  smul r b := ⟨r • b.1, (Subsemigroup.mem_corner_iff he).2
    ⟨by rw [mul_smul_comm, he.mul_corner_val], by rw [smul_mul_assoc, he.corner_val_mul]⟩⟩

@[simp]
theorem val_smul (r : R) (b : he.Corner) : (r • b).1 = r • b.1 := (rfl)

end Corner

end Semigroup

namespace Corner

section NonUnitalSemiring

variable {A : Type u} [NonUnitalSemiring A] {e : A} {he : IsIdempotentElem e}

/-- The unit of the corner ring `eAe` is `e`. -/
@[simp]
theorem val_one : (1 : he.Corner).1 = e := (rfl)

@[simp]
theorem val_mul (b c : he.Corner) : (b * c).1 = b.1 * c.1 := (rfl)

@[simp]
theorem val_zero : (0 : he.Corner).1 = 0 := (rfl)

@[simp]
theorem val_add (b c : he.Corner) : (b + c).1 = b.1 + c.1 := (rfl)

variable {R : Type v} [Semiring R] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- The corner inherits the module structure of the ambient nonunital algebra. -/
instance instModule : Module R he.Corner :=
  Function.Injective.module R ⟨⟨fun b : he.Corner ↦ b.1, rfl⟩, fun _ _ ↦ rfl⟩
    Subtype.val_injective fun _ _ ↦ rfl

end NonUnitalSemiring

section NonUnitalRing

variable {A : Type u} [NonUnitalRing A] {e : A} {he : IsIdempotentElem e}

@[simp]
theorem val_neg (b : he.Corner) : (-b).1 = -b.1 := (rfl)

@[simp]
theorem val_sub (b c : he.Corner) : (b - c).1 = b.1 - c.1 := (rfl)

end NonUnitalRing

section Algebra

variable {A : Type u} [NonUnitalSemiring A] {e : A} {he : IsIdempotentElem e}
  {R : Type v} [CommSemiring R] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- **The corner `eAe` of an idempotent of a nonunital `R`-algebra is an `R`-algebra**, with
`algebraMap R eAe r = r • e`. -/
instance instAlgebra : Algebra R he.Corner :=
  Algebra.ofModule'
    (fun r b ↦ Subtype.ext <|
      (smul_mul_assoc r e b.1).trans (congrArg (r • ·) (he.mul_corner_val b)))
    (fun r b ↦ Subtype.ext <|
      (mul_smul_comm r b.1 e).trans (congrArg (r • ·) (he.corner_val_mul b)))

@[simp]
theorem val_algebraMap (r : R) : (algebraMap R he.Corner r).1 = r • e := (rfl)

end Algebra

end Corner

section Map

variable {A B : Type*} [NonUnitalSemiring A] [NonUnitalSemiring B]
  {e : A} (he : IsIdempotentElem e)

/-- A nonunital homomorphism restricts to a unital homomorphism between idempotent corners.
The unit in the source is `e`, and the unit in the target is its image. -/
def cornerMap (f : A →ₙ+* B) : he.Corner →+* (he.map f).Corner where
  toFun x := ⟨f x.1, (Subsemigroup.mem_corner_iff (he.map f)).mpr
    ⟨by rw [← map_mul, he.mul_corner_val], by rw [← map_mul, he.corner_val_mul]⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul f x.1 y.1)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (map_add f x.1 y.1)

@[simp]
theorem val_cornerMap (f : A →ₙ+* B) (x : he.Corner) : (he.cornerMap f x).1 = f x.1 :=
  (rfl)

/-- A surjective homomorphism is surjective on every idempotent corner. -/
theorem cornerMap_surjective (f : A →ₙ+* B) (hf : Function.Surjective f) :
    Function.Surjective (he.cornerMap f) := by
  intro y
  obtain ⟨x, hx⟩ := hf y.1
  refine ⟨⟨e * x * e, x, rfl⟩, ?_⟩
  apply Subtype.ext
  exact (map_mul f (e * x) e).trans (by
    rw [map_mul, hx, (he.map f).mul_corner_val, (he.map f).corner_val_mul])

/-- A ring equivalence restricts to an equivalence between the corner `eAe` and the corner of the
image of `e`. -/
def cornerEquiv (f : A ≃+* B) : he.Corner ≃+* (he.map f).Corner where
  toFun := he.cornerMap f.toNonUnitalRingHom
  invFun y := ⟨f.symm y.1, (Subsemigroup.mem_corner_iff he).mpr
    ⟨f.injective (by rw [map_mul, f.apply_symm_apply, (he.map f).mul_corner_val]),
      f.injective (by rw [map_mul, f.apply_symm_apply, (he.map f).corner_val_mul])⟩⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x.1)
  right_inv y := Subtype.ext (f.apply_symm_apply y.1)
  map_mul' := map_mul (he.cornerMap f.toNonUnitalRingHom)
  map_add' := map_add (he.cornerMap f.toNonUnitalRingHom)

@[simp]
theorem val_cornerEquiv_apply (f : A ≃+* B) (x : he.Corner) : (he.cornerEquiv f x).1 = f x.1 :=
  (rfl)

@[simp]
theorem val_cornerEquiv_symm_apply (f : A ≃+* B) (y : (he.map f).Corner) :
    ((he.cornerEquiv f).symm y).1 = f.symm y.1 :=
  (rfl)

end Map

section Pi

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalSemiring (A i)] {e : ∀ i, A i}

/-- An element of a product is idempotent exactly when each of its components is. -/
theorem _root_.Pi.isIdempotentElem_iff : IsIdempotentElem e ↔ ∀ i, IsIdempotentElem (e i) :=
  funext_iff

variable (he : IsIdempotentElem e)

/-- **The corner of an idempotent in a product is the product of the corners** of its
components. -/
def cornerPiEquiv : he.Corner ≃+* ∀ i, (Pi.isIdempotentElem_iff.mp he i).Corner where
  toFun x i := ⟨x.1 i, (Subsemigroup.mem_corner_iff (Pi.isIdempotentElem_iff.mp he i)).mpr
    ⟨congrFun (he.mul_corner_val x) i, congrFun (he.corner_val_mul x) i⟩⟩
  invFun y := ⟨fun i ↦ (y i).1, (Subsemigroup.mem_corner_iff he).mpr
    ⟨funext fun i ↦ (Pi.isIdempotentElem_iff.mp he i).mul_corner_val (y i),
      funext fun i ↦ (Pi.isIdempotentElem_iff.mp he i).corner_val_mul (y i)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem val_cornerPiEquiv_apply (x : he.Corner) (i : ι) : (he.cornerPiEquiv x i).1 = x.1 i :=
  (rfl)

@[simp]
theorem val_cornerPiEquiv_symm_apply (y : ∀ i, (Pi.isIdempotentElem_iff.mp he i).Corner) :
    (he.cornerPiEquiv.symm y).1 = fun i ↦ (y i).1 :=
  (rfl)

end Pi

variable {A : Type u} [NonUnitalSemiring A] {e : A} (he : IsIdempotentElem e)
  {R : Type v} [Semiring R] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- The carrier of the corner ring `eAe` is the corner submodule `TauCeti.cornerSubmodule R e e`:
both are the range of `x ↦ e * x * e`. -/
theorem coe_corner_eq_cornerSubmodule (e : A) :
    (Subsemigroup.corner e : Set A) = TauCeti.cornerSubmodule R e e := by
  ext x
  simp only [SetLike.mem_coe, TauCeti.cornerSubmodule, LinearMap.mem_range,
    LinearMap.mulLeftRight_apply]
  rfl

/-- The corner ring `eAe`, as an `R`-module, is the corner submodule
`TauCeti.cornerSubmodule R e e`. -/
def cornerLinearEquivCornerSubmodule : he.Corner ≃ₗ[R] TauCeti.cornerSubmodule R e e where
  toFun b := ⟨b.1, (Set.ext_iff.1 (coe_corner_eq_cornerSubmodule (R := R) e) b.1).1 b.2⟩
  invFun x := ⟨x.1, (Set.ext_iff.1 (coe_corner_eq_cornerSubmodule (R := R) e) x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_cornerLinearEquivCornerSubmodule_apply (b : he.Corner) :
    (he.cornerLinearEquivCornerSubmodule (R := R) b : A) = b.1 := (rfl)

@[simp]
theorem val_cornerLinearEquivCornerSubmodule_symm_apply (x : TauCeti.cornerSubmodule R e e) :
    ((he.cornerLinearEquivCornerSubmodule (R := R)).symm x).1 = x := (rfl)

end IsIdempotentElem
