/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Quotient
public import TauCeti.RingTheory.Jacobson.MulOpposite
import Mathlib.Tactic.NoncommRing

/-!
# The Jacobson radical of a corner ring

Let `e` be an idempotent of a ring `A` and `eAe` its corner ring (`IsIdempotentElem.Corner`), with
unit `e`. This file proves that the Jacobson radical of the corner is the corner of the Jacobson
radical:

`J(eAe) = eJ(A)e = J(A) ∩ eAe`.

The proof goes through units. An element `x` of the corner is a unit of `eAe` exactly when
`1 - e + x` is a unit of `A` (`IsIdempotentElem.isUnit_corner_iff`): the map `x ↦ 1 - e + x` is
multiplicative, because the cross terms `(1 - e) * x` and `x * (1 - e)` vanish, and an inverse
`w` of `1 - e + x` in `A` cuts down to the inverse `ewe` of `x` in the corner. With the
elementwise descriptions of the radical (`TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left`
and its right-handed form) and the swap `1 + ab ↦ 1 + ba` (`TauCeti.isUnit_one_add_mul_comm`),
this compares the radicals.

Combined with the quotient calculation of `TauCeti.RingTheory.Idempotents.Quotient`, the radical
quotient of the corner is the corner of the radical quotient,
`eAe ⧸ J(eAe) ≃ ē (A ⧸ J(A)) ē` (`IsIdempotentElem.cornerQuotientJacobsonEquiv`). This is how
the semisimple part of a corner ring is read off from that of the ambient ring, for instance to
recognise a corner ring as basic.

## Main definitions

* `IsIdempotentElem.cornerQuotientJacobsonEquiv`: the radical quotient of the corner `eAe` is the
  corner of the radical quotient of `A`.

## Main results

* `IsIdempotentElem.isUnit_corner_iff`: `x` is a unit of `eAe` if and only if `1 - e + x` is a
  unit of `A`.
* `IsIdempotentElem.mem_jacobson_corner_iff`: an element of `eAe` lies in its Jacobson radical
  if and only if it lies in the Jacobson radical of `A`.
* `IsIdempotentElem.jacobson_corner`: `J(eAe) = eJ(A)e`, as ideals of the corner.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., GTM 131, Springer (2001),
  §21.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, CUP (2006), Section I.6.
-/

public section

namespace IsIdempotentElem

variable {A : Type*} [Ring A] {e : A} (he : IsIdempotentElem e)

/-- **Units of a corner ring.** An element `x` of the corner `eAe` is a unit there exactly when
`1 - e + x` is a unit of `A`. -/
theorem isUnit_corner_iff {x : he.Corner} : IsUnit x ↔ IsUnit (1 - e + x.1) := by
  constructor
  · -- `x ↦ 1 - e + x` is a monoid homomorphism `eAe → A`: the cross terms vanish.
    let φ : he.Corner →* A :=
      { toFun y := 1 - e + y.1
        map_one' := by simp
        map_mul' y z := by
          have h : (1 - e + y.1) * (1 - e + z.1) =
              1 - e - e + e * e + (z.1 - e * z.1) + (y.1 - y.1 * e) + y.1 * z.1 := by
            noncomm_ring
          rw [h, he.eq, he.mul_corner_val, he.corner_val_mul, Corner.val_mul]
          abel }
    exact fun h => h.map φ
  · rintro h
    obtain ⟨w, hw₁, hw₂⟩ := isUnit_iff_exists.mp h
    have hl : e * (1 - e + x.1) = x.1 := by
      rw [mul_add, mul_sub, mul_one, he.eq, sub_self, zero_add, he.mul_corner_val]
    have hr : (1 - e + x.1) * e = x.1 := by
      rw [add_mul, sub_mul, one_mul, he.eq, sub_self, zero_add, he.corner_val_mul]
    have h₁ : x.1 * w = e := by rw [← hl, mul_assoc, hw₁, mul_one]
    have h₂ : w * x.1 = e := by rw [← hr, ← mul_assoc, hw₂, one_mul]
    -- The inverse of `x` in the corner is `e * w * e`.
    have h₃ : x.1 * (e * w * e) = e := by
      rw [← mul_assoc, ← mul_assoc, he.corner_val_mul, h₁, he.eq]
    have h₄ : e * w * e * x.1 = e := by
      rw [mul_assoc, he.mul_corner_val, mul_assoc, h₂, he.eq]
    exact isUnit_iff_exists.mpr ⟨⟨e * w * e, w, rfl⟩, Subtype.ext h₃, Subtype.ext h₄⟩

/-- `1 - e + (1 + y)` is `1 + y` for an element `y` of the corner. -/
private theorem one_sub_add_val_one_add (y : he.Corner) :
    1 - e + (1 + y : he.Corner).1 = 1 + y.1 := by
  rw [Corner.val_add, Corner.val_one]
  abel

/-- **The Jacobson radical of a corner ring is cut out by the ambient radical.** An element of
the corner `eAe` lies in `Ring.jacobson eAe` exactly when it lies in `Ring.jacobson A`. -/
@[simp]
theorem mem_jacobson_corner_iff {x : he.Corner} :
    x ∈ Ring.jacobson he.Corner ↔ x.1 ∈ Ring.jacobson A := by
  constructor
  · intro hx
    refine TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left.mpr fun a => ?_
    -- `1 + x * (e * a * e)` is a unit of the corner; read it in `A` and swap the factors.
    have hu : IsUnit (1 + x.1 * (e * a * e)) := by
      have := he.isUnit_corner_iff.mp
        (TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_right.mp hx ⟨e * a * e, a, rfl⟩)
      rwa [he.one_sub_add_val_one_add] at this
    have hxa : x.1 * (e * a * e) = x.1 * (a * e) := by
      rw [mul_assoc e a e, ← mul_assoc, he.corner_val_mul]
    rwa [hxa, TauCeti.isUnit_one_add_mul_comm, mul_assoc, he.mul_corner_val] at hu
  · intro hx
    refine TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left.mpr fun y => ?_
    have hu : IsUnit (1 + y.1 * x.1) :=
      TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left.mp hx y.1
    rw [he.isUnit_corner_iff, he.one_sub_add_val_one_add]
    exact hu

/-- **`J(eAe) = eJ(A)e`.** The Jacobson radical of the corner ring `eAe` is the restriction to the
corner of the Jacobson radical of `A`. -/
theorem jacobson_corner : Ring.jacobson he.Corner = he.cornerIdeal (Ring.jacobson A) := by
  ext x
  rw [mem_jacobson_corner_iff, mem_cornerIdeal]

/-- **The radical quotient of a corner ring is the corner of the radical quotient**:
`eAe ⧸ J(eAe) ≃ ē (A ⧸ J(A)) ē`, where `ē` is the image of `e`. -/
noncomputable def cornerQuotientJacobsonEquiv :
    (he.Corner ⧸ Ring.jacobson he.Corner) ≃+*
      (he.map (Ideal.Quotient.mk (Ring.jacobson A))).Corner :=
  (Ideal.quotEquivOfEq he.jacobson_corner).trans (he.cornerQuotientEquiv (Ring.jacobson A))

@[simp]
theorem cornerQuotientJacobsonEquiv_mk (x : he.Corner) :
    he.cornerQuotientJacobsonEquiv (Ideal.Quotient.mk _ x) =
      he.cornerQuotientHom (Ring.jacobson A) x := by
  simp [cornerQuotientJacobsonEquiv]

end IsIdempotentElem
