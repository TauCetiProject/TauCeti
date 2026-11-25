/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import TauCeti.RingTheory.Semisimple.Trace.Reduced

/-!
# Positive involutions

Let `B` be a finite-dimensional semisimple `ℚ`-algebra. An *involution* of `B` is an additive map
`x ↦ x*` with `(x y)* = y* x*` and `x** = x`; it is automatically `ℚ`-linear. It is *positive* if
`Trd_{B/ℚ}(x x*) > 0` for every nonzero `x ∈ B`, where `Trd_{B/ℚ}` is the reduced trace
`TauCeti.Algebra.semisimpleReducedTrace ℚ B`: the sum over the simple factors `B_i` of `B`, with
centres `F_i`, of `Tr_{F_i/ℚ}` composed with the reduced trace of `B_i` over `F_i`. The Rosati
involution of a polarized abelian variety is positive, and a semisimple `ℚ`-algebra with a positive
involution is the starting point of PEL data.

The definition makes sense for any `ℚ`-algebra; it is the classical notion when `B` is
finite-dimensional and semisimple.

## Main definitions

* `TauCeti.PositiveInvolution B`: an involution of the `ℚ`-algebra `B` with
  `Trd_{B/ℚ}(x x*) > 0` for `x ≠ 0`.
* `TauCeti.PositiveInvolution.toStarRing`: the `StarRing` structure of a positive involution.
* `TauCeti.PositiveInvolution.ofStarRing`: a `StarRing` structure satisfying the positivity
  inequality is a positive involution.
* `TauCeti.PositiveInvolution.toLinearEquiv`: a positive involution as a `ℚ`-linear equivalence.

## Main results

* `TauCeti.PositiveInvolution.trd_mul_star_pos`: the defining inequality `Trd(x x*) > 0`.
* `TauCeti.PositiveInvolution.trd_star_mul_pos`: also `Trd(x* x) > 0` for `x ≠ 0`.
* `TauCeti.PositiveInvolution.star_smul`: a positive involution is `ℚ`-linear.
* `TauCeti.PositiveInvolution.ofStarRing_toStarRing`, `TauCeti.PositiveInvolution.star_ofStarRing`,
  `TauCeti.PositiveInvolution.toStarRing_ofStarRing`: positive involutions are the `StarRing`
  structures satisfying the inequality.

## References

* J. S. Milne, *Introduction to Shimura varieties*, Proposition 8.10 and Definition 8.11.
* K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, §1.2.1.
* R. Kottwitz, *Points on some Shimura varieties over finite fields*, §5.
-/

public section

namespace TauCeti

variable (B : Type*) [Ring B] [Algebra ℚ B]

/-- A **positive involution** of a `ℚ`-algebra `B`: an additive map `x ↦ x*` with
`(x y)* = y* x*` and `x** = x`, such that the reduced trace `Trd_{B/ℚ}(x x*)` is positive for every
nonzero `x`. For `B` finite-dimensional and semisimple this is the positivity of the involution in
the sense of PEL data. -/
structure PositiveInvolution where
  /-- The involution `x ↦ x*`. -/
  star : B → B
  /-- The involution is involutive: `x** = x`. -/
  star_involutive : Function.Involutive star
  /-- The involution reverses products: `(x y)* = y* x*`. -/
  star_mul (x y : B) : star (x * y) = star y * star x
  /-- The involution is additive. -/
  star_add (x y : B) : star (x + y) = star x + star y
  /-- **Positivity**: `Trd_{B/ℚ}(x x*) > 0` for every nonzero `x`. -/
  trd_mul_star_pos (x : B) (hx : x ≠ 0) :
    0 < Algebra.semisimpleReducedTrace ℚ B (x * star x)

namespace PositiveInvolution

variable {B}

attribute [simp] star_mul star_add

/-- Two positive involutions with the same underlying map are equal. -/
@[ext]
theorem ext {P Q : PositiveInvolution B} (h : ∀ x, P.star x = Q.star x) : P = Q := by
  obtain ⟨p, _, _, _, _⟩ := P
  obtain ⟨q, _, _, _, _⟩ := Q
  obtain rfl : p = q := funext h
  rfl

variable (P : PositiveInvolution B)

@[simp]
theorem star_star (x : B) : P.star (P.star x) = x :=
  P.star_involutive x

theorem star_injective : Function.Injective P.star :=
  P.star_involutive.injective

@[simp]
theorem star_inj {x y : B} : P.star x = P.star y ↔ x = y :=
  P.star_injective.eq_iff

/-- The `StarRing` structure of a positive involution. -/
@[expose, implicit_reducible]
def toStarRing : StarRing B where
  star := P.star
  star_involutive := P.star_involutive
  star_mul := P.star_mul
  star_add := P.star_add

@[simp]
theorem star_toStarRing (x : B) : (P.toStarRing).star x = P.star x :=
  (rfl)

/-- The involution as an additive equivalence. -/
def toAddEquiv : B ≃+ B :=
  letI := P.toStarRing
  starAddEquiv

@[simp]
theorem toAddEquiv_apply (x : B) : P.toAddEquiv x = P.star x :=
  (rfl)

/-- An involution is its own inverse. -/
@[simp]
theorem toAddEquiv_symm : P.toAddEquiv.symm = P.toAddEquiv :=
  AddEquiv.ext fun x ↦ P.toAddEquiv.symm_apply_eq.2 (by simp)

@[simp]
theorem star_zero : P.star 0 = 0 :=
  map_zero P.toAddEquiv

@[simp]
theorem star_neg (x : B) : P.star (-x) = -P.star x :=
  map_neg P.toAddEquiv x

@[simp]
theorem star_sub (x y : B) : P.star (x - y) = P.star x - P.star y :=
  map_sub P.toAddEquiv x y

@[simp]
theorem star_eq_zero {x : B} : P.star x = 0 ↔ x = 0 :=
  map_eq_zero_iff P.toAddEquiv P.toAddEquiv.injective

@[simp]
theorem star_one : P.star 1 = 1 :=
  letI := P.toStarRing
  _root_.star_one B

/-- A positive involution is `ℚ`-linear: `(q x)* = q x*`. -/
@[simp]
theorem star_smul (q : ℚ) (x : B) : P.star (q • x) = q • P.star x :=
  letI := P.toStarRing
  star_rat_smul q x

/-- A positive involution fixes the scalars: `(algebraMap ℚ B q)* = algebraMap ℚ B q`. -/
@[simp]
theorem star_algebraMap (q : ℚ) : P.star (algebraMap ℚ B q) = algebraMap ℚ B q := by
  rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one]

/-- A positive involution as a `ℚ`-linear equivalence. -/
def toLinearEquiv : B ≃ₗ[ℚ] B :=
  { P.toAddEquiv with map_smul' := P.star_smul }

@[simp]
theorem toLinearEquiv_apply (x : B) : P.toLinearEquiv x = P.star x :=
  (rfl)

/-- An involution is its own inverse. -/
@[simp]
theorem toLinearEquiv_symm : P.toLinearEquiv.symm = P.toLinearEquiv :=
  LinearEquiv.ext fun x ↦ P.toLinearEquiv.symm_apply_eq.2 (by simp)

/-- **Positivity of `x* x`.** For a positive involution, also `Trd_{B/ℚ}(x* x) > 0` for every
nonzero `x`. -/
theorem trd_star_mul_pos {x : B} (hx : x ≠ 0) :
    0 < Algebra.semisimpleReducedTrace ℚ B (P.star x * x) := by
  simpa using P.trd_mul_star_pos (P.star x) ((P.star_eq_zero).not.mpr hx)

/-- `Trd_{B/ℚ}(x x*) ≥ 0` for every `x`. -/
theorem trd_mul_star_nonneg (x : B) : 0 ≤ Algebra.semisimpleReducedTrace ℚ B (x * P.star x) := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (P.trd_mul_star_pos x hx).le

/-- `Trd_{B/ℚ}(x x*) = 0` only for `x = 0`. -/
@[simp]
theorem trd_mul_star_eq_zero {x : B} :
    Algebra.semisimpleReducedTrace ℚ B (x * P.star x) = 0 ↔ x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ (P.trd_mul_star_pos x hx).ne' h, fun h ↦ by simp [h]⟩

/-- **A `StarRing` structure satisfying the positivity inequality is a positive involution.** -/
def ofStarRing [StarRing B]
    (h : ∀ x : B, x ≠ 0 → 0 < Algebra.semisimpleReducedTrace ℚ B (x * Star.star x)) :
    PositiveInvolution B where
  star := Star.star
  star_involutive := InvolutiveStar.star_involutive
  star_mul := StarMul.star_mul
  star_add := StarAddMonoid.star_add
  trd_mul_star_pos := h

@[simp]
theorem star_ofStarRing [StarRing B]
    (h : ∀ x : B, x ≠ 0 → 0 < Algebra.semisimpleReducedTrace ℚ B (x * Star.star x)) (x : B) :
    (ofStarRing h).star x = Star.star x :=
  (rfl)

/-- A positive involution is recovered from its `StarRing` structure. -/
@[simp]
theorem ofStarRing_toStarRing :
    letI := P.toStarRing
    ofStarRing P.trd_mul_star_pos = P :=
  (rfl)

/-- A `StarRing` structure is recovered from the positive involution it defines. -/
@[simp]
theorem toStarRing_ofStarRing [inst : StarRing B]
    (h : ∀ x : B, x ≠ 0 → 0 < Algebra.semisimpleReducedTrace ℚ B (x * Star.star x)) :
    (ofStarRing h).toStarRing = inst :=
  (rfl)

end PositiveInvolution

end TauCeti
