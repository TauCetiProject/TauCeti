/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Tactic.NoncommRing

/-!
# Kato's intertwiner for pairs of idempotents and star projections

For two idempotents `p` and `q` in a unital ring `R`, Kato's element
`projectionIntertwiner p q = q * p + (1 - q) * (1 - p)` intertwines `p` and `q`:
`q * projectionIntertwiner p q = q * p = projectionIntertwiner p q * p`.
Multiplying `projectionIntertwiner p q` on either side by the reversed intertwiner
`projectionIntertwiner q p` yields `1 - (p - q) ^ 2`, an element commuting with `p`, `q`, and
`projectionIntertwiner p q`.

When `R` is a star ring and `p`, `q` are star projections, `star (projectionIntertwiner p q)` is
`projectionIntertwiner q p`, so `projectionIntertwiner p q` is normal with
`star z * z = z * star z = 1 - (p - q) ^ 2` and `z + star z = 2 • (1 - (p - q) ^ 2)`. In a unital
C⋆-algebra with `‖p - q‖ < 1`, dividing `z` by the positive square root of `1 - (p - q) ^ 2`
produces a unitary `u` with `u * p * star u = q` and `‖u - 1‖ ≤ √2 * ‖p - q‖`.

## Main definitions

* `TauCeti.projectionIntertwiner p q`: the element `q * p + (1 - q) * (1 - p)`.

## Main statements

* `IsIdempotentElem.mul_projectionIntertwiner_eq_projectionIntertwiner_mul`: the intertwining
  identity `q * projectionIntertwiner p q = projectionIntertwiner p q * p`.
* `IsIdempotentElem.projectionIntertwiner_swap_mul_self` and
  `IsIdempotentElem.projectionIntertwiner_mul_swap`: both products with `projectionIntertwiner q p`
  equal `1 - (p - q) ^ 2`.
* `IsStarProjection.star_projectionIntertwiner_mul_self` and
  `IsStarProjection.projectionIntertwiner_mul_star_self`: for star projections, `star z * z` and
  `z * star z` equal `1 - (p - q) ^ 2`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1966), Chapter I, §4.6.
* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences **122**, Springer (2006), Proposition II.4.3.2.
-/

public section

namespace TauCeti

section Ring

variable {R S : Type*} [Ring R] [Ring S]

/-- **Kato's intertwiner** `q * p + (1 - q) * (1 - p)` for two idempotents `p` and `q` in a ring.
When `p` and `q` are idempotent, `q * projectionIntertwiner p q = projectionIntertwiner p q * p`,
and multiplying by `projectionIntertwiner q p` on either side gives `1 - (p - q) ^ 2`. -/
def projectionIntertwiner (p q : R) : R :=
  q * p + (1 - q) * (1 - p)

/-- Unfold `TauCeti.projectionIntertwiner`. -/
theorem projectionIntertwiner_def (p q : R) :
    projectionIntertwiner p q = q * p + (1 - q) * (1 - p) :=
  (rfl)

/-- Expanded form `1 - p - q + 2 • (q * p)` of `TauCeti.projectionIntertwiner`. -/
theorem projectionIntertwiner_eq_one_sub_add (p q : R) :
    projectionIntertwiner p q = 1 - p - q + 2 • (q * p) := by
  rw [projectionIntertwiner_def]
  noncomm_ring

/-- Kato's intertwiner of `0` with `0` is `1`. -/
@[simp]
theorem projectionIntertwiner_zero_zero : projectionIntertwiner (0 : R) 0 = 1 := by
  simp [projectionIntertwiner_def]

/-- Kato's intertwiner of `1` with `1` is `1`. -/
@[simp]
theorem projectionIntertwiner_one_one : projectionIntertwiner (1 : R) 1 = 1 := by
  simp [projectionIntertwiner_def]

/-- Passing to complementary idempotents `1 - p` and `1 - q` leaves
`TauCeti.projectionIntertwiner` unchanged. -/
@[simp]
theorem projectionIntertwiner_one_sub (p q : R) :
    projectionIntertwiner (1 - p) (1 - q) = projectionIntertwiner p q := by
  rw [projectionIntertwiner_def, projectionIntertwiner_def]
  noncomm_ring

/-- Any unital ring homomorphism preserves `TauCeti.projectionIntertwiner`. -/
theorem map_projectionIntertwiner {F : Type*} [FunLike F R S] [RingHomClass F R S]
    (φ : F) (p q : R) :
    φ (projectionIntertwiner p q) = projectionIntertwiner (φ p) (φ q) := by
  simp [projectionIntertwiner_def]

end Ring

section StarRing

variable {R : Type*} [Ring R] [StarRing R]

/-- Taking the star of `TauCeti.projectionIntertwiner p q` for self-adjoint `p` and `q` swaps the
two arguments. -/
theorem star_projectionIntertwiner {p q : R} (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) :
    star (projectionIntertwiner p q) = projectionIntertwiner q p := by
  simp [projectionIntertwiner_def, hp.star_eq, hq.star_eq]

end StarRing

end TauCeti

namespace IsIdempotentElem

open TauCeti

variable {R : Type*} [Ring R] {p q : R}

/-- The intertwiner of an idempotent with itself is `1`. -/
theorem projectionIntertwiner_self (hp : IsIdempotentElem p) :
    projectionIntertwiner p p = 1 := by
  calc projectionIntertwiner p p
      = 1 + 2 • (p * p - p) := by rw [projectionIntertwiner_def]; noncomm_ring
    _ = 1 := by simp [hp.eq]

/-- Right-multiplying `projectionIntertwiner p q` by an idempotent `p` retains `q * p`. -/
theorem projectionIntertwiner_mul (hp : IsIdempotentElem p) (q : R) :
    projectionIntertwiner p q * p = q * p := by
  rw [projectionIntertwiner_def, add_mul, mul_assoc, hp.eq, mul_assoc, hp.one_sub_mul_self,
    mul_zero, add_zero]

/-- Left-multiplying `projectionIntertwiner p q` by an idempotent `q` retains `q * p`. -/
theorem mul_projectionIntertwiner (hq : IsIdempotentElem q) (p : R) :
    q * projectionIntertwiner p q = q * p := by
  rw [projectionIntertwiner_def, mul_add, ← mul_assoc, hq.eq, ← mul_assoc, hq.mul_one_sub_self,
    zero_mul, add_zero]

/-- **Kato's intertwining relation** `q * projectionIntertwiner p q = projectionIntertwiner p q * p`
for two idempotents `p` and `q`. -/
theorem mul_projectionIntertwiner_eq_projectionIntertwiner_mul
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    q * projectionIntertwiner p q = projectionIntertwiner p q * p := by
  rw [hq.mul_projectionIntertwiner, hp.projectionIntertwiner_mul]

/-- Multiplying `projectionIntertwiner q p` by `projectionIntertwiner p q` gives
`1 - (p - q) ^ 2`. -/
theorem projectionIntertwiner_swap_mul_self (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    projectionIntertwiner q p * projectionIntertwiner p q = 1 - (p - q) ^ 2 := by
  have hpp : p * p - p = 0 := sub_eq_zero.mpr hp.eq
  have hqq : q * q - q = 0 := sub_eq_zero.mpr hq.eq
  calc projectionIntertwiner q p * projectionIntertwiner p q
      = p * (q * q) * p + p * (q * (1 - q)) * (1 - p)
          + (1 - p) * ((1 - q) * q) * p
          + (1 - p) * ((1 - q) * (1 - q)) * (1 - p) := by
        rw [projectionIntertwiner_def, projectionIntertwiner_def]; noncomm_ring
    _ = p * q * p + (1 - p) * (1 - q) * (1 - p) := by
        rw [hq.eq, hq.mul_one_sub_self, hq.one_sub_mul_self, hq.one_sub.eq]; simp
    _ = 1 - (p - q) ^ 2 + 2 • (p * p - p) + (q * q - q) := by noncomm_ring
    _ = 1 - (p - q) ^ 2 := by simp [hpp, hqq]

/-- Multiplying `projectionIntertwiner p q` by `projectionIntertwiner q p` gives
`1 - (p - q) ^ 2`. -/
theorem projectionIntertwiner_mul_swap (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    projectionIntertwiner p q * projectionIntertwiner q p = 1 - (p - q) ^ 2 := by
  have hsub : (q - p) ^ 2 = (p - q) ^ 2 := by noncomm_ring
  rw [hq.projectionIntertwiner_swap_mul_self hp, hsub]

/-- Symmetrizing `projectionIntertwiner p q` gives `2 • (1 - (p - q) ^ 2)`. -/
theorem projectionIntertwiner_add_swap (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    projectionIntertwiner p q + projectionIntertwiner q p = 2 • (1 - (p - q) ^ 2) := by
  have hpp : p * p - p = 0 := sub_eq_zero.mpr hp.eq
  have hqq : q * q - q = 0 := sub_eq_zero.mpr hq.eq
  calc projectionIntertwiner p q + projectionIntertwiner q p
      = 2 • (1 - (p - q) ^ 2) + 2 • (p * p - p) + 2 • (q * q - q) := by
        rw [projectionIntertwiner_def, projectionIntertwiner_def]; noncomm_ring
    _ = 2 • (1 - (p - q) ^ 2) := by simp [hpp, hqq]

/-- For two idempotents `p` and `q`, `p` commutes with `(p - q) ^ 2`. -/
theorem commute_sub_sq (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    Commute p ((p - q) ^ 2) := by
  have hpp : p * p - p = 0 := sub_eq_zero.mpr hp.eq
  have hqq : q * q - q = 0 := sub_eq_zero.mpr hq.eq
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  calc p * (p - q) ^ 2 - (p - q) ^ 2 * p
      = q * (p * p - p) - (p * p - p) * q + p * (q * q - q) - (q * q - q) * p := by
        noncomm_ring
    _ = 0 := by simp [hpp, hqq]

/-- For two idempotents `p` and `q`, `p` commutes with `1 - (p - q) ^ 2`. -/
theorem commute_one_sub_sub_sq (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    Commute p (1 - (p - q) ^ 2) :=
  (Commute.one_right p).sub_right (hp.commute_sub_sq hq)

/-- For two idempotents `p` and `q`, `projectionIntertwiner p q` commutes with
`1 - (p - q) ^ 2`. -/
theorem commute_projectionIntertwiner_one_sub_sub_sq
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    Commute (projectionIntertwiner p q) (1 - (p - q) ^ 2) := by
  have hsub : (q - p) ^ 2 = (p - q) ^ 2 := by noncomm_ring
  have hqc : Commute q (1 - (p - q) ^ 2) := hq.commute_one_sub_sub_sq hp |> (hsub ▸ ·)
  have hpc : Commute p (1 - (p - q) ^ 2) := hp.commute_one_sub_sub_sq hq
  rw [projectionIntertwiner_def]
  exact (hqc.mul_left hpc).add_left
    (((Commute.one_left _).sub_left hqc).mul_left ((Commute.one_left _).sub_left hpc))

end IsIdempotentElem

namespace IsStarProjection

open TauCeti

variable {R : Type*} [Ring R] [StarRing R] {p q : R}

/-- For star projections `p` and `q`, `star (projectionIntertwiner p q) * projectionIntertwiner p q`
equals `1 - (p - q) ^ 2`. -/
theorem star_projectionIntertwiner_mul_self (hp : IsStarProjection p) (hq : IsStarProjection q) :
    star (projectionIntertwiner p q) * projectionIntertwiner p q = 1 - (p - q) ^ 2 := by
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint,
    hp.isIdempotentElem.projectionIntertwiner_swap_mul_self hq.isIdempotentElem]

/-- For star projections `p` and `q`, `projectionIntertwiner p q * star (projectionIntertwiner p q)`
equals `1 - (p - q) ^ 2`. -/
theorem projectionIntertwiner_mul_star_self (hp : IsStarProjection p) (hq : IsStarProjection q) :
    projectionIntertwiner p q * star (projectionIntertwiner p q) = 1 - (p - q) ^ 2 := by
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint,
    hp.isIdempotentElem.projectionIntertwiner_mul_swap hq.isIdempotentElem]

/-- For star projections `p` and `q`, `projectionIntertwiner p q + star (projectionIntertwiner p q)`
equals `2 • (1 - (p - q) ^ 2)`. -/
theorem projectionIntertwiner_add_star (hp : IsStarProjection p) (hq : IsStarProjection q) :
    projectionIntertwiner p q + star (projectionIntertwiner p q) = 2 • (1 - (p - q) ^ 2) := by
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint,
    hp.isIdempotentElem.projectionIntertwiner_add_swap hq.isIdempotentElem]

end IsStarProjection
