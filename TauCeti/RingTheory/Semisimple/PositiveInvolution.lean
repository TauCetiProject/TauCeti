/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
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

* `TauCeti.PositiveInvolution B`: a `StarRing` structure on the `ℚ`-algebra `B` with
  `Trd_{B/ℚ}(x x*) > 0` for `x ≠ 0`.
* `TauCeti.PositiveInvolution.ofStarRing`: a `StarRing` structure satisfying the positivity
  inequality is a positive involution; this is the constructor, and
  `TauCeti.PositiveInvolution.toStarRing` recovers the `StarRing` structure.

## Main results

* `TauCeti.PositiveInvolution.semisimpleReducedTrace_mul_star_pos`: the defining inequality
  `Trd(x x*) > 0`.
* `TauCeti.PositiveInvolution.semisimpleReducedTrace_star_mul_pos`: also `Trd(x* x) > 0` for
  `x ≠ 0`.
* `TauCeti.PositiveInvolution.semisimpleReducedTrace_mul_star_eq_zero`,
  `TauCeti.PositiveInvolution.semisimpleReducedTrace_star_mul_eq_zero`: `Trd(x x*)` and `Trd(x* x)`
  vanish only at `x = 0`.

## Implementation notes

A positive involution bundles its `StarRing` structure, so Mathlib's `star` API applies to it
under `letI := P.toStarRing`. For instance `star_rat_smul` says that the involution is
`ℚ`-linear, and `starAddEquiv` and `starLinearEquiv ℚ` are the involution as an equivalence.

## References

* J. S. Milne, *Introduction to Shimura varieties*, Proposition 8.10 and Definition 8.11.
* K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, §1.2.1.
* R. Kottwitz, *Points on some Shimura varieties over finite fields*, §5.
-/

public section

namespace TauCeti

variable (B : Type*) [Ring B] [Algebra ℚ B]

/-- A **positive involution** of a `ℚ`-algebra `B`: a `StarRing` structure `x ↦ x*` on `B` (so
`(x y)* = y* x*` and `x** = x`) such that the reduced trace `Trd_{B/ℚ}(x x*)` is positive for every
nonzero `x`. For `B` finite-dimensional and semisimple this is the positivity of the involution in
the sense of PEL data. -/
structure PositiveInvolution where
  /-- **A `StarRing` structure satisfying the positivity inequality is a positive involution.** -/
  ofStarRing ::
  /-- The involution `x ↦ x*`, as a `StarRing` structure on `B`. -/
  [toStarRing : StarRing B]
  /-- **Positivity**: `Trd_{B/ℚ}(x x*) > 0` for every nonzero `x`. -/
  semisimpleReducedTrace_mul_star_pos (x : B) (hx : x ≠ 0) :
    0 < Algebra.semisimpleReducedTrace ℚ B (x * star x)

namespace PositiveInvolution

variable {B}

/-- Two positive involutions with the same underlying map are equal. -/
@[ext]
theorem ext {P Q : PositiveInvolution B}
    (h : ∀ x, P.toStarRing.star x = Q.toStarRing.star x) : P = Q := by
  obtain @⟨@⟨@⟨@⟨⟨p⟩, _⟩, _⟩, _⟩, _⟩ := P
  obtain @⟨@⟨@⟨@⟨⟨q⟩, _⟩, _⟩, _⟩, _⟩ := Q
  obtain rfl : p = q := funext h
  rfl

variable (P : PositiveInvolution B)

/-- **Positivity of `x* x`.** For a positive involution, also `Trd_{B/ℚ}(x* x) > 0` for every
nonzero `x`. -/
theorem semisimpleReducedTrace_star_mul_pos {x : B} (hx : x ≠ 0) :
    letI := P.toStarRing
    0 < Algebra.semisimpleReducedTrace ℚ B (star x * x) := by
  let := P.toStarRing
  simpa using P.semisimpleReducedTrace_mul_star_pos (star x) (star_ne_zero.2 hx)

/-- `Trd_{B/ℚ}(x x*) ≥ 0` for every `x`. -/
theorem semisimpleReducedTrace_mul_star_nonneg (x : B) :
    letI := P.toStarRing
    0 ≤ Algebra.semisimpleReducedTrace ℚ B (x * star x) := by
  let := P.toStarRing
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (P.semisimpleReducedTrace_mul_star_pos x hx).le

/-- `Trd_{B/ℚ}(x x*) = 0` only for `x = 0`. -/
@[simp]
theorem semisimpleReducedTrace_mul_star_eq_zero {x : B} :
    letI := P.toStarRing
    Algebra.semisimpleReducedTrace ℚ B (x * star x) = 0 ↔ x = 0 := by
  let := P.toStarRing
  exact ⟨fun h ↦ by_contra fun hx ↦ (P.semisimpleReducedTrace_mul_star_pos x hx).ne' h,
    fun h ↦ by simp [h]⟩

/-- `Trd_{B/ℚ}(x* x) ≥ 0` for every `x`. -/
theorem semisimpleReducedTrace_star_mul_nonneg (x : B) :
    letI := P.toStarRing
    0 ≤ Algebra.semisimpleReducedTrace ℚ B (star x * x) := by
  let := P.toStarRing
  simpa using P.semisimpleReducedTrace_mul_star_nonneg (star x)

/-- `Trd_{B/ℚ}(x* x) = 0` only for `x = 0`. -/
@[simp]
theorem semisimpleReducedTrace_star_mul_eq_zero {x : B} :
    letI := P.toStarRing
    Algebra.semisimpleReducedTrace ℚ B (star x * x) = 0 ↔ x = 0 := by
  let := P.toStarRing
  simpa using P.semisimpleReducedTrace_mul_star_eq_zero (x := star x)

end PositiveInvolution

end TauCeti
