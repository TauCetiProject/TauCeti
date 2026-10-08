/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.Idempotents

/-!
# Corners cut out by two idempotents

Let `A` be an algebra over a commutative semiring `k`. This file defines the corner `eAf` as the
range of the `k`-linear map `x ↦ e * x * f`. When `e` and `f` are idempotent, membership is
equivalent to the fixed-point equation `e * x * f = x`.

The second part concerns Mathlib's corner ring `IsIdempotentElem.Corner` of an idempotent `e`, the
ring `eAe` with unit `e`. Mathlib gives it a ring structure; when `A` is an algebra over a
commutative semiring `R`, this file makes it an `R`-algebra, with `algebraMap R eAe r = r • e`.
This is the structure under which `eAe` can be compared with `A` as `R`-algebras, for instance
through Mathlib's `MoritaEquivalence`.

## Main definitions

* `TauCeti.cornerMap`: the `k`-linear map `x ↦ e * x * f`.
* `TauCeti.cornerSubmodule`: the corner `eAf`, as a `k`-submodule of `A`.
* `IsIdempotentElem.Corner.instAlgebra`: the corner ring `eAe` of an idempotent of an `R`-algebra
  is an `R`-algebra.
* `IsIdempotentElem.cornerLinearEquivCornerSubmodule`: the corner ring `eAe`, as an `R`-module,
  agrees with the corner submodule `TauCeti.cornerSubmodule R e e`.

## Main results

* `TauCeti.mem_cornerSubmodule_iff`: the fixed-point characterization of an idempotent corner.
* `IsIdempotentElem.mul_corner_val` and `IsIdempotentElem.corner_val_mul`: an element of the
  corner ring `eAe` is fixed by `e` on both sides.

## References

This is the corner infrastructure used by Layer 3 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. See I. Assem, D. Simson, A. Skowroński,
*Elements of the Representation Theory of Associative Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

universe u v

variable (k : Type v) [CommSemiring k] {A : Type u} [Semiring A] [Algebra k A]

/-- Cutting an element of `A` down to the corner at `(e, f)`: multiplying it by `e` on the left
and by `f` on the right. -/
def cornerMap (e f : A) : A →ₗ[k] A :=
  (LinearMap.mulLeft k e).comp (LinearMap.mulRight k f)

@[simp]
theorem cornerMap_apply (e f x : A) : cornerMap k e f x = e * x * f :=
  (mul_assoc _ _ _).symm

/-- **The corner `eAf`**, as a `k`-submodule of `A`: the range of the map `x ↦ e * x * f`. -/
def cornerSubmodule (e f : A) : Submodule k A :=
  LinearMap.range (cornerMap k e f)

/-- The corner submodule is the range of the corner map. -/
theorem cornerSubmodule_def (e f : A) :
    cornerSubmodule k e f = LinearMap.range (cornerMap k e f) := (rfl)

/-- For idempotents `e` and `f`, an element belongs to the corner `eAf` exactly when multiplying it
by `e` on the left and by `f` on the right fixes it. -/
@[simp]
theorem mem_cornerSubmodule_iff {e f x : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : x ∈ cornerSubmodule k e f ↔ e * x * f = x := by
  constructor
  · rintro ⟨y, rfl⟩
    simp only [cornerMap_apply]
    calc
      e * (e * y * f) * f = (e * e) * y * (f * f) := by simp only [mul_assoc]
      _ = e * y * f := by rw [he.eq, hf.eq]
  · intro h
    exact ⟨x, by simpa only [cornerMap_apply] using h⟩

variable {k}

/-- An element of the corner `eAf` is fixed by `e` on the left. -/
theorem mul_eq_self_of_mem_cornerSubmodule {e f x : A} (he : IsIdempotentElem e)
    (hx : x ∈ cornerSubmodule k e f) : e * x = x := by
  rcases hx with ⟨y, rfl⟩
  simp only [cornerMap_apply]
  calc
    e * (e * y * f) = (e * (e * y)) * f := (mul_assoc _ _ _).symm
    _ = (e * e) * y * f := by rw [← mul_assoc e e y]
    _ = e * y * f := by rw [he.eq]

/-- An element of the corner `eAf` is fixed by `f` on the right. -/
theorem mul_eq_self_of_mem_cornerSubmodule_right {e f x : A} (hf : IsIdempotentElem f)
    (hx : x ∈ cornerSubmodule k e f) : x * f = x := by
  rcases hx with ⟨y, rfl⟩
  simp only [cornerMap_apply]
  rw [mul_assoc, hf.eq]

end TauCeti

/-! ### The corner ring as an algebra -/

namespace IsIdempotentElem

variable {A : Type u} [Semiring A] {e : A} (he : IsIdempotentElem e)

/-- An element of the corner ring `eAe` is fixed by `e` on the left. -/
@[simp]
theorem mul_corner_val (b : he.Corner) : e * b.1 = b.1 :=
  ((Subsemigroup.mem_corner_iff he).1 b.2).1

/-- An element of the corner ring `eAe` is fixed by `e` on the right. -/
@[simp]
theorem corner_val_mul (b : he.Corner) : b.1 * e = b.1 :=
  ((Subsemigroup.mem_corner_iff he).1 b.2).2

namespace Corner

variable {he}

/-- The unit of the corner ring `eAe` is `e`. -/
@[simp]
theorem val_one : (1 : he.Corner).1 = e := (rfl)

@[simp]
theorem val_mul (b c : he.Corner) : (b * c).1 = b.1 * c.1 := (rfl)

@[simp]
theorem val_zero : (0 : he.Corner).1 = 0 := (rfl)

@[simp]
theorem val_add (b c : he.Corner) : (b + c).1 = b.1 + c.1 := (rfl)

section Ring

variable {A : Type u} [Ring A] {e : A} {he : IsIdempotentElem e}

@[simp]
theorem val_neg (b : he.Corner) : (-b).1 = -b.1 := (rfl)

@[simp]
theorem val_sub (b c : he.Corner) : (b - c).1 = b.1 - c.1 := (rfl)

end Ring

variable {R : Type v} [CommSemiring R] [Algebra R A]

instance instSMul : SMul R he.Corner where
  smul r b := ⟨r • b.1, (Subsemigroup.mem_corner_iff he).2
    ⟨by rw [mul_smul_comm, he.mul_corner_val], by rw [smul_mul_assoc, he.corner_val_mul]⟩⟩

@[simp]
theorem val_smul (r : R) (b : he.Corner) : (r • b).1 = r • b.1 := (rfl)

instance instModule : Module R he.Corner :=
  Function.Injective.module R ⟨⟨fun b : he.Corner ↦ b.1, rfl⟩, fun _ _ ↦ rfl⟩
    Subtype.val_injective fun _ _ ↦ rfl

/-- **The corner ring `eAe` of an idempotent of an `R`-algebra is an `R`-algebra**, with
`algebraMap R eAe r = r • e`. -/
instance instAlgebra : Algebra R he.Corner :=
  Algebra.ofModule'
    (fun r b ↦ Subtype.ext <|
      (smul_mul_assoc r e b.1).trans (congrArg (r • ·) (he.mul_corner_val b)))
    (fun r b ↦ Subtype.ext <|
      (mul_smul_comm r b.1 e).trans (congrArg (r • ·) (he.corner_val_mul b)))

@[simp]
theorem val_algebraMap (r : R) : (algebraMap R he.Corner r).1 = r • e := (rfl)

end Corner

variable {R : Type v} [CommSemiring R] [Algebra R A]

/-- The carrier of the corner ring `eAe` is the corner submodule `TauCeti.cornerSubmodule R e e`:
both are the range of `x ↦ e * x * e`. -/
theorem coe_corner_eq_cornerSubmodule (e : A) :
    (Subsemigroup.corner e : Set A) = TauCeti.cornerSubmodule R e e := by
  ext x
  simp only [SetLike.mem_coe, TauCeti.cornerSubmodule, LinearMap.mem_range,
    TauCeti.cornerMap_apply]
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
